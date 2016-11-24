module Brisk.Model.Extract where
import GhcPlugins          hiding (Subst)
import Control.Monad.State

import           Brisk.Model.GhcInterface
import           Brisk.Model.Language

type MGen a  = State MGState a
data MGState = MGS { hscEnv  :: HscEnv
                   , modGuts :: ModGuts
                   , pureFn  :: Var
                   , appFn   :: Var
                   , absType :: Type
                   }

-- initialEState :: HscEnv -> ModGuts -> Var -> MGState
initialEState henv mg p a top t
  = MGS { hscEnv  = henv
        , modGuts = mg
        , pureFn  = p
        , appFn   = a
        , topFn   = top
        , absType = t
        }

runMGen :: HscEnv -> ModGuts -> CoreProgram -> IO CoreProgram
runMGen hsenv mg prog
  = do [p, app, top] <- ghcVar hsenv "Brisk.Model.Language" <$> ["pure", "app", "top"]
       t        <- ghcType hsenv "Brisk.Model.Language" "AbsVal"
       return $ evalState go (initialEState hsenv mg p app top t)
  where go = mapM mGenBind prog

mGenBind :: CoreBind -> MGen CoreBind
mGenBind (NonRec x b)
  = do a <- mGenExpr b
       t <- gets absType
       return (NonRec x { varType = t } a)

mGenExpr :: CoreExpr -> MGen CoreExpr
mGenExpr e
  | isPure e    = mGenPureExpr e
  | isProcess e = mGenProcessExpr e

isPure    = const True    
isProcess = const False

mGenPureExpr :: CoreExpr -> MGen CoreExpr
mGenPureExpr e
  = do p <- gets pureFn
       a <- gets absFn
       return $ mkCoreApps (Var p) [mkCoreApps (Var a) [Type $ exprType e]]
mGenProcessExpr e = undefined

-- mGenExpr :: Env.Env Name (AbsVal () () Conc)  -> CoreExpr -> MGen EType
-- mGenExpr g (Tick _ e)
--   = mGenExpr g e

-- mGenExpr g (Lit (LitInteger i t))
--   = return $ EffTyApp intTyCon [] Pure

-- mGenExpr g e@(Var x)
--   | Just e <- Env.lookup g (getName x)
--   = return e

-- mGenExpr g f@(Lam b e)
--   = do te <- mGenExpr (Env.insert g (getName b) t1) e
--        return $ EffTyArrow t1 (absTerm b te)
--   where
--     t1 = ofType (varType b)

-- mGenExpr g (App e t)
--   | isTypeArg t = mGenExpr g e

-- mGenExpr g (App e1 e2)
--   = do t1 <- mGenExpr g e1
--        t2 <- mGenExpr g e2
