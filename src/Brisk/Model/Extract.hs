{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Brisk.Model.Extract where
import GhcPlugins          hiding ((<+>), pp, text, Subst)
import Name
import Control.Monad.Trans.State
import Control.Monad.State  hiding (gets)
import Data.Function
import PrelNames

import           Brisk.Model.GhcInterface
import qualified Brisk.Model.Env as Env
import           Brisk.Model.GhcInterface
import           Brisk.Model.Types
import           Brisk.Model.Builtins
import           Brisk.Pretty
import           Text.PrettyPrint.HughesPJ

type MGen a  = StateT MGState IO a
data MGState = MGS { hscEnv  :: HscEnv
                   , modGuts :: ModGuts
                   , procTy  :: Name
                   }

-- initialEState :: HscEnv -> ModGuts -> Var -> MGState
initialEState henv mg t
  = MGS { hscEnv  = henv
        , modGuts = mg
        , procTy  = t 
        }
type Annot  = ()
type AbsEff = EffExpr Name Annot
type EffMap = Env.Env Name (EffExpr Name Annot)

runMGen :: [String] -> HscEnv -> ModGuts -> CoreProgram -> IO ()
runMGen bs hsenv mg prog
  = do g0     <- Env.addsEnv Env.empty <$> resolve hsenv builtin
       procTy <- ghcTyName hsenv "Control.Distributed.Process.Internal.Types" "Process"
       g      <- evalStateT (go g0) (initialEState hsenv mg procTy)
       ns     <- forM bs $ \b ->
                   lookupName hsenv (mg_module mg) b
       let binds = if null ns
                     then Env.toList g
                     else filter ((`elem` ns) . fst) (Env.toList g)
       dumpBinds binds
  where
    go g = foldM mGenBind g prog

dumpBinds binds
  = forM_ binds $ \(k,v) ->
      putStrLn (render (pp k <+> text ":=" <+> pp v))
              

mGenBind :: EffMap -> CoreBind -> MGen EffMap 
mGenBind g (NonRec x b)
  | isDictId x
  = return g
  | otherwise
  = do a <- mGenExpr g b
       return (Env.insert g (getName x) a)
mGenBind g (Rec [(f,e)])
  = do let g' = Env.insert g n (var n)
           n  = getName f
       a <- mGenExpr g' e
       return (Env.insert g n (ERec n a ()))

mGenExpr :: EffMap -> CoreExpr -> MGen AbsEff 
mGenExpr g (Type t)
  = return (EType t)

mGenExpr g (Cast e _)
  = mGenExpr g e

mGenExpr g (Lit l)
  = return $ litEffect l

mGenExpr g (Var x)
  | Just a <- Env.lookup g (getName x) = return a
  | otherwise = nameError "Not in scope" x

mGenExpr g (Let b e)
  = do g' <- mGenBind g b
       mGenExpr g' e

mGenExpr g (Lam b e)
  = do a <- mGenExpr (Env.insert g n (var n)) e
       if isDictId b then
         return a
       else
         return (n $->$ a)
         where
           n = getName b

mGenExpr g (App e e')
  | not (isTypeArg e') && isDictTy (exprType e')
  = mGenExpr g e
mGenExpr g (App e1@(Var f) e2@(Type t))
  | isMonadOp f, Just tc <- tyConAppTyCon_maybe t
  = do a <- mGenMonadOp f tc
       maybe defApp return a
         where
           defApp = mGenApp g <$> mGenExpr g e1 <*> mGenExpr g e2
mGenExpr g (App e1 e2)
  = mGenApp g <$> mGenExpr g e1 <*> mGenExpr g e2

mGenExpr g e@(Case e' _ t alts)
  = do a     <- mGenExpr g e'
       defA  <- mapM (mGenExpr g) def
       as    <- mGenCaseAlts g alts'
       return $ ECase a as defA
         where
           (alts', def) = findDefault alts

mGenExpr g e
  = exprError "Unhandled Expression" e
              
mGenMonadOp :: Id -> TyCon -> MGen (Maybe AbsEff)
mGenMonadOp f tc
  = do tc' <- gets procTy
       if tc' == getName tc then
         return (monadOp f)
       else
         return Nothing


mGenApp g (ELam x a1 _) a2
  = subst x a2 a1
mGenApp g e@(EVar x l) a2
  = EApp e a2 l
mGenApp _ e@(EVal _ _) _
  = e
mGenApp _ e1 e2
  = error ("App: " ++ render (pp e1 <+> pp e2))

mGenCaseAlts :: EffMap -> [CoreAlt] -> MGen [(Name, [Name], AbsEff)]
mGenCaseAlts g = mapM go
  where
    go (DataAlt c, bs, e)
      = do let g' = Env.addsEnv g [ (b, var b) | b <- getName <$> bs ]
           a <- mGenExpr g' e
           return (getName c, getName <$> bs, a)
    go (LitAlt l, [], e)
      = do ae <- mGenExpr g e
           return (builtinName 0, [], ae)
    go (DEFAULT, [], e)
      = error "unhandled DEFAULT case"

litEffect _ = EVal (builtinName 0, PTrue) ()    

instance Pretty Name where
  pp i = text $ showSDoc unsafeGlobalDynFlags (ppr i)
instance Pretty Type where
  pp i = text $ showSDoc unsafeGlobalDynFlags (ppr i)

exprError :: String -> CoreExpr -> a  
exprError s e
  = errorFmt s $ showPpr unsafeGlobalDynFlags e

nameError :: NamedThing n => String -> n -> a
nameError s x
  = errorFmt s $ showSDocDebug unsafeGlobalDynFlags (ppr (getName x))

errorFmt s e
  = error ("[BRISK] " ++ s ++ ": " ++ e)

