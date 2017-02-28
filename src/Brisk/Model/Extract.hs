{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Brisk.Model.Extract where

import GHC (GhcMonad)
import GhcPlugins          hiding ((<+>), pp, text, Subst, Id, mkTyVar, tyVarName)
import qualified GhcPlugins as Ghc
import Type                as Ty
import TyCoRep             as Tr
import Name
import Control.Monad.Trans.State
import Control.Monad.State  hiding (get, gets, modify)
import Data.Function
import Data.List
import Data.Maybe
import PrelNames
import Text.Show.Pretty (ppShow)

import qualified Data.Set as Set
import qualified Brisk.Model.Env as Env
-- import           Brisk.Transform.ANF
import           Brisk.Model.GhcInterface
import           Brisk.Model.Types
import           Brisk.Model.Builtins
import           Brisk.Model.Prolog
-- import           Brisk.Model.Promela
import           Brisk.Model.IceT (runIceT, HasType(..))
import           Brisk.Pretty
import           Text.PrettyPrint.HughesPJ as PP

type MGen a  = StateT MGState IO a
data MGState = MGS { hscEnv   :: !HscEnv
                   , modGuts  :: !ModGuts
                   , procTy   :: !Name
                   , cnt      :: !Int
                   , srcSpans :: ![SrcSpan]
                   }

-- initialEState :: HscEnv -> ModGuts -> Var -> MGState
initialEState henv mg t
  = MGS { hscEnv   = henv
        , modGuts  = mg
        , procTy   = t 
        , cnt      = 0
        , srcSpans = [noSrcSpan]
        }

type EffMap = Env.Env Id AbsEff 

instance Annot TyAnnot where
  dummyAnnot = (Nothing, noSrcSpan)

instance HasType TyAnnot where
  getType         = fst
  setType t (_,l) = (t,l)

pushSpan :: RealSrcSpan -> MGen ()              
pushSpan ss = modify $ \s -> s { srcSpans = RealSrcSpan ss : srcSpans s }

currentSpan :: MGen SrcSpan
currentSpan = head <$> gets srcSpans

popSpan ::  MGen SrcSpan
popSpan = do span:spans <- gets srcSpans
             modify $ \s -> s { srcSpans = spans }
             return span

noAnnot :: Functor f => f a -> f TyAnnot
noAnnot = fmap (const dummyAnnot)

specAnnot :: Maybe Ty.Type -> TyAnnot  
specAnnot t = (idOfType <$> t, noSrcSpan)

annotType :: CoreExpr -> AbsEff -> AbsEff
annotType e t = t { annot = a }
  where
    a | isTypeArg e = annot t
      | otherwise   = (Just (exprEType e),  snd (annot t))

idOfType  = ofType tyConId (tyVarName . nameId)
exprEType = idOfType . exprType    

liftAnnot t = (t, noSrcSpan)  

specTableEnv :: SpecTableIn -> EffMap
specTableEnv (SpecTable tab)
  = Env.addsEnv Env.empty [ (x, liftAnnot <$> t) | x :<=: t <- tab ]

runMGen :: [String] -> HscEnv -> ModGuts -> SpecTableIn -> CoreProgram -> IO SpecTableOut
runMGen bs hsenv mg specs prog
  = do -- initBinds <- resolve hsenv (specTuple <$> specs)
       -- let g0    = Env.addsEnv Env.empty [ (nameId x, specAnnot <$> b) | (x,b) <- initBinds ]
       let g0    = Env.unionEnvs (specTableEnv builtin) (specTableEnv specs)
       procTy    <- ghcTyName hsenv "Control.Distributed.Process.Internal.Types" "Process"
       g         <- evalStateT (go g0 prog) (initialEState hsenv mg procTy)
       ns        <- forM bs findModuleNameId
       let all   = Env.toList g
           brisk = filter ((`elem` ns) . fst) all
       -- dumpBinds all
       dumpBinds brisk
       forM_ brisk (putStrLn . render . PP.vcat . fmap pp . runIceT . snd)
       forM_ brisk (putStrLn . toBriskString . snd)
       return $ SpecTable [ x :<=: e | (x,e) <- all ]
  where
    go :: EffMap -> CoreProgram -> MGen EffMap
    go                     = foldM mGenBind
    findModuleNameId b     = nameId <$> lookupName hsenv (mg_module mg) b

isPure :: Ty.Type -> MGen Bool
isPure t
  = do ty <- gets procTy
       return $ go ty t
  where
    go t (Tr.TyVarTy t')     = True
    go t (Tr.LitTy _)        = True
    go t (Tr.AppTy t1 t2)    = True
    go t (Tr.TyConApp tc [_,t']) {- FunTy _ t') -}
     | isFunTyCon tc
     = go t t'
    go t (Tr.TyConApp tc ts) = cmp t tc
    go t (Tr.ForAllTy _ t')  = go t t'
    cmp t t' = nameId (getName t) /= nameId (getName t')

dumpBinds :: [(Id, AbsEff)] -> IO ()
dumpBinds binds
  = forM_ binds $ \(k,v) ->
      putStrLn (render (pp k <+> text ":=" <+> PP.vcat [ pp v
                                                       -- , text (ppShow v)
                                                       ]))

bindId :: NamedThing a => a -> Id
bindId = nameId . getName

annotOfBind x
  = (Just . idOfType $ idType x, getSrcSpan x)

mGenBind :: EffMap -> CoreBind -> MGen EffMap 
mGenBind g (NonRec x b)
  | isDictId x
  = return g
  | otherwise
  = do a <- mGenExpr g b
       return (Env.insert g (bindId x) a)
mGenBind g (Rec [(f,e)])
  = do let g' = Env.insert g n guess
       a <- mGenExpr g' e
       return (Env.insert g n (ERec n a (annotOfBind f)))
         where
           (bs,_)  = collectBinders e
           bes     = [ EVar (bindId x) (annotOfBind x) | x <- bs, not (isDictId x) ]
           guess   = foldr go (foldl go' (var n (annotOfBind f)) bes) bes
           n       = bindId f
           go (EVar x l) a  = ELam x a l
           go' a x = EApp a x (annotOfBind f)
mGenBind g (Rec bs)
  = do liftIO $ putStrLn "Skipping binding group!"
       return g

mGenExpr :: EffMap -> CoreExpr -> MGen AbsEff 
mGenExpr g e = annotType e <$> mGenExpr' g e

mGenExpr' g (Tick (SourceNote ss _) e)
  = do pushSpan ss
       a <- mGenExpr g e
       popSpan
       return a
mGenExpr' g (Tick _ e)
  = mGenExpr g e
mGenExpr' g (Type t)
  = do s <- currentSpan
       return (EType (idOfType t) (Nothing, s))
mGenExpr' g exp@(Cast e _)
  = mGenExpr g e

mGenExpr' g (Lit l)
  = do s <- currentSpan
       return (litEffect s l)

mGenExpr' g (Var x)
  | Just dc <- isDataConId_maybe x
  = return $ conEffExpr (annotOfBind x) (dataConOrigResTy dc) dc

mGenExpr' g (Var x)
  | Just a <- Env.lookup g (bindId x)
  = return (annotType (Var x) a)
  | otherwise
  = do pure <- isPure (idType x)
       s    <- currentSpan
       if False then
          return $ defaultEffExpr (Nothing, s) (idType x)
       else
          return $ var (bindId x) (annotOfBind x)

mGenExpr' g (Let b e)
  = do g' <- mGenBind g b
       mGenExpr g' e
mGenExpr' g abs@(Lam b e)
  = do a <- mGenExpr (Env.insert g n (var n $ annotOfBind b)) e
       s <- currentSpan
       if isDictId b then
         return a
       else
         return (lam n a (Just (exprEType abs), s))
         where
           n | isTyVar b = tyVarName (bindId b)
             | otherwise = bindId b

mGenExpr' g exp@(App e e')
  | not (isTypeArg e') && isDictTy (exprType e')
  = mGenExpr g e
mGenExpr' g e@(App (Var i) l)
  | Just dc <- isDataConWorkId_maybe i,
    dc == intDataCon
  = mGenExpr' g l
mGenExpr' g e@(App e1@(Var f) _)
  | getName f == failMName
  = error "AHA!!!!"
mGenExpr' g e@(App e1@(Var f) e2@(Type t))
  | isMonadOp f, Just tc <- tyConAppTyCon_maybe t
  = do a <- mGenMonadOp f tc
       annotType e <$> maybe defApp return a
         where
           defApp = do eff1 <- mGenExpr g e1
                       eff2 <- mGenExpr g e2
                       mGenApp g eff1 eff2
mGenExpr' g e@(App e1 e2)
  = do ef1 <- mGenExpr g e1
       ef2 <- mGenExpr g e2
       simplify . annotType e <$> mGenApp g ef1 ef2

mGenExpr' g e@(Case e' _ t alts)
  = do a     <- mGenExpr g e'
       defA  <- mapM (mGenExpr g) def
       as    <- mGenCaseAlts g alts'
       s     <- currentSpan
       let tCase = exprEType e'
           tExp  = exprEType e
       return . simplify $ ECase tCase a as defA (Just tExp, s)
         where
           (alts', def) = findDefault alts

mGenExpr' g e
  = exprError "Unhandled Expression" e
              
mGenMonadOp :: NamedThing a => a -> TyCon -> MGen (Maybe AbsEff)
mGenMonadOp f tc
  = do tc' <- gets procTy
       if tc' == getName tc then
         return (noAnnot <$> monadOp f)
       else
         return Nothing

mGenApp :: EffMap -> AbsEff -> AbsEff -> MGen AbsEff
mGenApp g e@ECon {} (EType _ _)
  = return e
mGenApp g e@ECon {} a
  = return $ simplify (e `apConEff` a)
mGenApp g a@(ELam x m _) a2
  = return . simplify $ subst x a2 m
  -- = do ELam x a1 _ <- alphaRename (fv a2) a
  --      return . simplify . subst x a2 $ a1
mGenApp _ a1@(ERec f _ l) a2
  = return $ EApp a1 a2 l
mGenApp _ a1@(EApp _ _ l) a2
  = return $ EApp a1 a2 l
mGenApp g e@(EVar x l) a2
  = return $ EApp e a2 l
mGenApp _ e@(EVal _ _) _
  = return e
mGenApp _ e1 e2
  = error ("App: " ++ render (pp e1 <+> pp e2))

substIf :: Id -> Set.Set Id -> AbsEff -> AbsEff -> AbsEff
substIf x xs a
  | x `Set.member` xs = subst x a
  | otherwise         = id

var :: Id -> a -> EffExpr Id a
var = EVar   
lam = ELam  

mGenCaseAlts :: EffMap -> [CoreAlt] -> MGen [(Id, [Id], AbsEff)]
mGenCaseAlts g = mapM go
  where
    go (DataAlt c, bs, e)
      = do let g' = Env.addsEnv g [ (bindId b, var (bindId b) (annotOfBind b))
                                  | b <- bs
                                  ]
           a <- mGenExpr g' e
           return (dataConId c, bindId <$> bs, a)
    go (LitAlt l, [], e)
      = do ae <- mGenExpr g e
           return (vv, [], ae)
    go (DEFAULT, [], e)
      = error "unhandled DEFAULT case"

litEffect :: SrcSpan -> Literal -> AbsEff
litEffect l (LitInteger i _) = litInt i (Nothing, l)
litEffect l (MachInt i)      = litInt i (Nothing, l)
litEffect l (MachInt64 i)    = litInt i (Nothing, l)
litEffect l _                = litInt 0 (Nothing, l)

instance Pretty Name where
  ppPrec _ i = text $ showSDoc unsafeGlobalDynFlags (ppr i)
instance Pretty CoreExpr where
  ppPrec _ i = text $ showSDoc unsafeGlobalDynFlags (ppr i)

exprError :: String -> CoreExpr -> a  
exprError s e
  = errorFmt s $ showPpr unsafeGlobalDynFlags e

nameError :: NamedThing n => String -> n -> a
nameError s x
  = errorFmt s $ showSDocDebug unsafeGlobalDynFlags (ppr (getName x))

errorFmt s e
  = error ("[BRISK] " ++ s ++ ": " ++ e)
