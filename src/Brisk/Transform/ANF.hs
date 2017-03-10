--------------------------------------------------------------------------------
-- | Convert GHC Core into Administrative Normal Form (ANF) --------------------
--------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}


module Brisk.Transform.ANF (anormalize) where

import           Prelude                          
import           GhcPlugins
import           CoreSyn
import           CoreUtils                        (exprType)
import qualified DsMonad
import           DsMonad                          (initDs)
import           GHC                              hiding (exprType)
import           HscTypes
import           OccName                          (mkVarOccFS)
import           Id                               (mkUserLocal)
import           Literal
import           MkCore                           (mkCoreLets)
import           Outputable                       (trace)
import           Var                              (varType, setVarType)
import           Type                             (mkForAllTys, substTy, mkForAllTys, mkTvSubstPrs, isTyVar)
import           TyCoRep
import           TyCon                            (tyConDataCons_maybe)
import           DataCon                          (dataConInstArgTys)
import           FamInstEnv                       (emptyFamInstEnv)
import           VarEnv                           (VarEnv, emptyVarEnv, extendVarEnv, lookupWithDefaultVarEnv)
import           UniqSupply                       (MonadUnique)
import           Data.Text                        (pack)
import           Data.Text.Encoding               (encodeUtf8)

import           Control.Monad.State.Lazy
-- import           System.Console.CmdArgs.Verbosity (whenLoud)
-- import           Language.Fixpoint.Misc             (fst3)
-- import           Language.Fixpoint.Types            (anfPrefix)

-- import           Language.Haskell.Liquid.UX.Config  (Config, untidyCore, nocaseexpand, noPatternInline)
-- import           Language.Haskell.Liquid.Misc       (concatMapM)
-- import           Language.Haskell.Liquid.Transforms.Rec
-- import           Language.Haskell.Liquid.Transforms.Rewrite
-- import           Language.Haskell.Liquid.Types.Errors
import           Brisk.Transform.Misc   (MGIModGuts(..))
import qualified Brisk.Transform.SpanStack as Sp
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy, (\\))

--------------------------------------------------------------------------------
-- | A-Normalize a module ------------------------------------------------------
--------------------------------------------------------------------------------
anormalize :: HscEnv -> ModGuts -> [CoreBind] -> IO [CoreBind]
--------------------------------------------------------------------------------
anormalize hscEnv mg cbs
  = do (fromMaybe err . snd) <$> initDs hscEnv m grEnv tEnv emptyFamInstEnv act
    where
      m        = mg_module mg
      grEnv    = mg_rdr_env mg
      tEnv     = modGutsTypeEnv mg
      act      = concatMapM (normalizeTopBind γ0) cbs
      -- orig_cbs = transformRecExpr $ mgi_binds modGuts
      err      = error "Oops, cannot A-Normalize GHC Core!"
      γ0       = emptyAnfEnv

concatMapM :: (Monad f, Traversable t) => (a1 -> f [a]) -> t a1 -> f [a]
concatMapM f = fmap concat . mapM f      

modGutsTypeEnv :: ModGuts -> TypeEnv
modGutsTypeEnv mg  = typeEnvFromEntities ids tcs fis
  where
    ids            = bindersOfBinds (mg_binds mg)
    tcs            = mg_tcs mg
    fis            = mg_fam_insts mg

--------------------------------------------------------------------------------
-- | A-Normalize a @CoreBind@ --------------------------------------------------
--------------------------------------------------------------------------------

-- Can't make the below default for normalizeBind as it
-- fails tests/pos/lets.hs due to GHCs odd let-bindings

normalizeTopBind :: AnfEnv -> Bind CoreBndr -> DsMonad.DsM [CoreBind]
normalizeTopBind γ (NonRec x e)
  = do e' <- runDsM $ evalStateT (stitch γ e) (DsST [])
       return [normalizeTyVars $ NonRec x e']

normalizeTopBind γ (Rec xes)
  = do xes' <- runDsM $ execStateT (normalizeBind γ (Rec xes)) (DsST [])
       return $ map normalizeTyVars (st_binds xes')

normalizeTyVars :: Bind Id -> Bind Id
normalizeTyVars (NonRec x e) = NonRec (setVarType x t') $ normalizeForAllTys e
  where t'       = subst msg as as' bt
        msg      = "WARNING unable to renameVars on " ++ Sp.showPpr unsafeGlobalDynFlags x
        as'      = fst $ splitForAllTys $ exprType e
        (as, bt) = splitForAllTys (varType x)
normalizeTyVars (Rec xes)    = Rec xes'
  where nrec = normalizeTyVars <$> ((\(x, e) -> NonRec x e) <$> xes)
        xes' = (\(NonRec x e) -> (x, e)) <$> nrec

subst :: String -> [TyVar] -> [TyVar] -> Type -> Type
subst msg as as' bt
  | length as == length as'
  = mkPiTypes as' $ Type.substTy su bt
  | otherwise
  = trace msg $ mkPiTypes as bt
  where su = mkTvSubstPrs $ zip as (mkTyVarTys as')

-- | eta-expand CoreBinds with quantified types
normalizeForAllTys :: CoreExpr -> CoreExpr
normalizeForAllTys e = case e of
  Lam b _ | isTyVar b
    -> e
  _ -> mkLams tvs (mkTyApps e (map mkTyVarTy tvs))
  where
  (tvs, _) = splitForAllTys (exprType e)


newtype DsM a = DsM {runDsM :: DsMonad.DsM a}
   deriving (Functor, Monad, MonadUnique, Applicative)

data DsST = DsST { st_binds :: [CoreBind] }

type DsMW = StateT DsST DsM

------------------------------------------------------------------
normalizeBind :: AnfEnv -> CoreBind -> DsMW ()
------------------------------------------------------------------
normalizeBind γ (NonRec x e)
  = do e' <- normalize γ e
       add [NonRec x e']

normalizeBind γ (Rec xes)
  = do es' <- mapM (stitch γ) es
       add [Rec (zip xs es')]
    where
       (xs, es) = unzip xes

--------------------------------------------------------------------
normalizeName :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------

-- normalizeNameDebug γ e
--   = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

normalizeName γ e@(Lit l)
  | shouldNormalize l
  = normalizeLiteral γ e
  | otherwise
  = return e

normalizeName γ (Var x)
  = return $ Var (lookupAnfEnv γ x x)

normalizeName _ e@(Type _)
  = return e

normalizeName γ e@(Coercion _)
  = do x     <- lift $ freshNormalVar γ $ exprType e
       add  [NonRec x e]
       return $ Var x

normalizeName γ (Tick tt e)
  = do e'    <- normalizeName (γ `at` tt) e
       return $ Tick tt e'

normalizeName γ e
  = do e'   <- normalize γ e
       x    <- lift $ freshNormalVar γ $ exprType e
       add [NonRec x e']
       return $ Var x

shouldNormalize :: Literal -> Bool
shouldNormalize l = case l of
  LitInteger _ _ -> True
  MachStr _ -> True
  _ -> False

add :: [CoreBind] -> DsMW ()
add w = modify $ \s -> s { st_binds = st_binds s ++ w}

--------------------------------------------------------------------------------
normalizeLiteral :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
normalizeLiteral γ e =
  do x <- lift $ freshNormalVar γ $ exprType e
     add [NonRec x e]
     return $ Var x

--------------------------------------------------------------------------------
normalize :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
normalize γ (Lam x e)
  = do e' <- stitch γ e
       return $ Lam x e'

normalize γ (Let b e)
  = do normalizeBind γ b
       normalize γ e
       -- Need to float bindings all the way up to the top
       -- Due to GHCs odd let-bindings (see tests/pos/lets.hs)

normalize γ (Case e x t as)
  = do n     <- normalizeName γ e
       x'    <- lift $ freshNormalVar γ τx -- rename "wild" to avoid shadowing
       let γ' = extendAnfEnv γ x x'
       as'   <- forM as $ \(c, xs, e') -> liftM (c, xs,) (stitch γ' e')
       as''  <- lift $ expandDefaultCase γ τx as'
       return $ Case n x' t as''
    where τx = varType x

normalize γ (Var x)
  = return $ Var (lookupAnfEnv γ x x)

normalize _ e@(Lit _)
  = return e

normalize _ e@(Type _)
  = return e

normalize γ (Cast e τ)
  = do e' <- normalizeName γ e
       return $ Cast e' τ

normalize γ (App e1 e2)
  = do e1' <- normalize γ e1
       n2  <- normalizeName γ e2
       return $ App e1' n2

normalize γ (Tick tt e)
  = do e' <- normalize (γ `at` tt) e
       return $ Tick tt e'

normalize _ (Coercion c)
  = return $ Coercion c

--------------------------------------------------------------------------------
stitch :: AnfEnv -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------------------
stitch γ e
  = do bs'   <- get
       modify $ \s -> s { st_binds = [] }
       e'    <- normalize γ e
       bs    <- st_binds <$> get
       put bs'
       return $ mkCoreLets bs e'

--------------------------------------------------------------------------------
expandDefaultCase :: AnfEnv
                  -> Type
                  -> [(AltCon, [Id], CoreExpr)]
                  -> DsM [(AltCon, [Id], CoreExpr)]
--------------------------------------------------------------------------------
expandDefaultCase γ tyapp@(TyConApp tc _) z@((DEFAULT, _ ,_):dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | (DataAlt d, _ , _) <- dcs]
                     if (length ds') == 1
                      then expandDefaultCase' γ tyapp z
                      else return z
       Nothing -> return z --

expandDefaultCase _ _ z
   = return z

expandDefaultCase' :: AnfEnv -> Type -> [(AltCon, [Id], c)] -> DsM [(AltCon, [Id], c)]
expandDefaultCase' γ (TyConApp tc argτs) z@((DEFAULT, _ ,e) : dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | (DataAlt d, _ , _) <- dcs]
                     dcs'   <- forM ds' $ cloneCase γ argτs e
                     return $ sortCases $ dcs' ++ dcs
       Nothing -> return z --

expandDefaultCase' _ _ z
   = return z

cloneCase :: AnfEnv -> [Type] -> t -> DataCon -> DsM (AltCon, [Id], t)
cloneCase γ argτs e d
  = do xs  <- mapM (freshNormalVar γ) $ dataConInstArgTys d argτs
       return (DataAlt d, xs, e)

sortCases :: [(AltCon, b, c)] -> [(AltCon, b, c)]
sortCases = sortBy (\x y -> cmpAltCon (fst3 x) (fst3 y))
  where fst3 (x,_,_) = x

--------------------------------------------------------------------------------
-- | ANF Environments ----------------------------------------------------------
--------------------------------------------------------------------------------

-- freshNormalVar :: Type -> DsM Id
-- freshNormalVar = mkSysLocalM (symbolFastString anfPrefix)

freshNormalVar :: AnfEnv -> Type -> DsM Id
freshNormalVar γ t = do u <- getUniqueM
                        return $ mkUserLocal anfOcc u t sp
  where
    anfOcc         = mkVarOccFS . mkFastStringByteString . encodeUtf8 . pack $ "$$brisk_anf" -- symbolFastString anfPrefix
    sp             = Sp.srcSpan (aeSrcSpan γ)

data AnfEnv = AnfEnv
  { aeVarEnv  :: VarEnv Id
  , aeSrcSpan :: Sp.SpanStack
  }

emptyAnfEnv :: AnfEnv
emptyAnfEnv = AnfEnv emptyVarEnv Sp.empty

lookupAnfEnv :: AnfEnv -> Id -> Id -> Id
lookupAnfEnv γ x y = lookupWithDefaultVarEnv (aeVarEnv γ) x y

extendAnfEnv :: AnfEnv -> Id -> Id -> AnfEnv
extendAnfEnv γ x y = γ { aeVarEnv = extendVarEnv (aeVarEnv γ) x y }

at :: AnfEnv -> Tickish Id -> AnfEnv
at γ tt = γ { aeSrcSpan = Sp.push (Sp.Tick tt) (aeSrcSpan γ)}
