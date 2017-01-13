module Brisk.Model.Promela (runPromela) where

import Type
import Data.List
import Data.Maybe
import Text.Printf
import Control.Monad.State
import Text.PrettyPrint.HughesPJ

import           Brisk.UX
import qualified Brisk.Model.Types as B
import           Brisk.Model.Types (EffExpr(..))
import           Brisk.Model.IceT  as IceT

data PromelaState = PS { procs    :: [String]
                       , symProcs :: [String]
                       , typeMap  :: [(Type, Int)]
                       , procMap  :: [(ProcessId, Int)]
                       , tmp      :: Int
                       , whileStack :: [Int]
                       }

type PM = State PromelaState

data Proc = Concr  ProcessId           -- ^ p
          | SymSet ProcessId ProcessId -- ^ sym(p:P)

---------------------------------------------------
runPromela :: (HasType a, Show a)
           => [IceT.IceTProcess a]
           -> String
---------------------------------------------------
runPromela ps = unlines $ [ recvMacro n
                          , sendMacro n
                          , channels  n (typeMap st)
                          ]
                       ++ [initProc pps p0]
             -- ++ procs pps
  where state0 = PS { procs      = [ p | IceT.Single p _    <- ps ]
                    , symProcs   = [ p | IceT.ParIter _ p _ <- ps ]
                    , typeMap    = []
                    , procMap    = []
                    , tmp        = 0
                    , whileStack = []
                    }
        (p0:pps, st) = runState (promelaProcs ps) state0
        n            = length (procs st)

initProc pps (Concr pid0, p0)
  = unlines $ [ "init {"
              , printf "%s = _pid;" pid0
              ]
           ++ [ runProc p | (p,_) <- pps ]
           ++ [ p0 ]
           ++ [ "}" ]
  where
    runProc (Concr p) = printf "%s = run %s();" p (procName p)

procName :: String -> String
procName p = printf "proc_%s" p

---------------------------------------------------
channels :: Int -> [(Type,Int)] -> String
---------------------------------------------------
channels nProcs tys
  = unlines (go <$> tys)
  where
    go (_, ti)
      = printf "chan chan_%s[%d] = [__K__] of { %s }"
                ("T" ++ show ti)
                (nProcs * nProcs)
                ("T" ++ show ti)

---------------------------------------------------
sendMacro, recvMacro :: Int -> String
---------------------------------------------------
recvMacro n
  = unlines $ [ "#define __RECV__(_ty, _x) atomic { _ty _x; if \\" ]
           ++ (tycase <$> [0..n-1])
           ++ [ "fi }" ]
  where
    tycase = printf ":: chan_##_ty[%d*%d + _pid]?_x\\" n

sendMacro
  = printf "#define __SEND__(_ty,_to,_msg) { chan_##_ty[%d*_pid + _to]!_msg }"

-- #define __RECV__(ty,from) \
-- if
--    :: chan_ty[pid0*N + _pid]?x
--    :: chan_ty[pid1*N + _pid]?x
--    :: chan_ty[pid2*N + _pid]?x
--    ...
-- fi
-- ...


---------------------------------------------------
promelaProcs :: (HasType a, Show a)
             => [IceT.IceTProcess a] -> PM [(Proc, String)]
---------------------------------------------------
promelaProcs ps
  = forM ps $ \p -> do
      pr <- uncurry promelaProc (go p)
      return (fst (go p), pr)
  where
    go (IceT.Single p s)     = (Concr p, s)
    go (IceT.ParIter p ps s) = (SymSet p ps, s)

---------------------------------------------------
promelaProc :: (Show a, HasType a)
            => Proc -> IceT.IceTStmt a -> PM String
---------------------------------------------------
promelaProc pid Skip
  = return "skip"

promelaProc pid (IceT.Assgn x _ e)
  = do e' <- promelaExpr e
       return $ printf "%s = %s" x e'

promelaProc pid (IceT.Recv t x)
  = recv <$> typeId t <*> pure (maybeVar x)
  where
    maybeVar = fromMaybe "_"

promelaProc pid (IceT.Send _ p m)
  = do ty  <- typeId (getType m)
       msg <- promelaExpr m
       to  <- promelaExpr p
       return $ send ty to msg

promelaProc pid (IceT.Seq ss)
  = do stmts <- mapM (promelaProc pid) ss
       let semis = (++";") <$> stmts
       return $ unlines semis

promelaProc pid (IceT.Case e alts md)
  = printf "if %s fi" <$> promelaCase pid e alts md

promelaProc pid IceT.Continue
  = do l <- head <$> gets whileStack
       return $ printf "goto L%d" l

promelaProc pid (IceT.While s)
  = do l  <- gets tmp
       ls <- gets whileStack
       modify $ \s -> s { tmp = l + 1, whileStack = l : ls}
       s' <- promelaProc pid s
       modify $ \s -> s { whileStack = ls}
       return $ printf "L%d: %s" l s'

promelaProc pid s
  = abort "promelaProc" s

send :: String -> String -> String -> String
send = printf "__SEND__(%s,%s,%s)"

recv :: String -> String -> String
recv = printf "__RECV__(%s,%s)"

promelaCase :: (Show a, HasType a)
            => Proc
            -> IceTExpr a
            -> [(IceTExpr a, IceTStmt a)]
            -> Maybe (IceTStmt a)
            -> PM String
promelaCase pid e alts md
  = do (conds, pAlts) <- unzip <$> mapM go alts
       pDef           <- goDef conds md
       return $ unwords (pAlts ++ pDef)
  where
    go :: (Show a, HasType a) => (IceTExpr a, IceTStmt a) -> PM (String, String)
    go (e',s)
      = do s' <- promelaProc pid s
           let patBinds = exprPatBinds e'
               body     = unwords (((++"; ") <$> patBinds) ++ [s'])
           return (cond e', printf ":: %s -> %s" (top [cond e']) body)

    goDef _ Nothing   = return []
    goDef cs (Just s) = do s' <- promelaProc pid s
                           let negCs = printf "!(%s)" <$> cs
                           return [printf ":: %s -> %s" (top negCs) s']

    cond :: IceTExpr a -> String
    cond e' = printf "%s.cstr == %s" (varId e) (conId e')

    top :: [String] -> String
    top = foldl (printf "%s || %s") (printf "%s.top == 1" (varId e))

exprPatBinds (ECon c as _)
  = undefined

promelaExpr :: (Show a, HasType a)
            => IceTExpr a -> PM String
promelaExpr (EVar x _)
  = return x
promelaExpr (ECon c args l)
  = promelaConstr c args (getType l)
promelaExpr e
  = abort "promelaExpr" e

promelaPid (Concr p)
  = return p
promelaPid (SymSet p _)
  = return p

promelaConstr c args t
  = do let aexps = filter ((/=t) . getType) args
       tid       <- typeId t
       argStrs   <- intercalate "," <$> mapM promelaExpr aexps
       return $ printf "__Mk_%s_%s__(%s)" tid c argStrs
{-
#define __Mk_T0_C0() \
atomic { \
  T0 T0new; \
  T0new.top = 0; \
} \
-}

---------------------------------------------------
typeId :: Type -> PM String
---------------------------------------------------
typeId t
  = do im <- lookup t <$> gets typeMap
       typeName <$> maybe (allocType t) return im
       where
         typeName i = "T" ++ show i

allocType :: Type -> PM Int
allocType t
  = do n <- length <$> gets typeMap
       let n' = n + 1
       modify $ \s -> s { typeMap = (t,n') : typeMap s }
       return n'

---------------------------------------------------
numProcs :: PM Int
---------------------------------------------------
numProcs = length <$> gets procs

{-
#define __RECV__(ty,from) \
if
   :: chan_ty[pid0*N + _pid]?x
   :: chan_ty[pid1*N + _pid]?x
   :: chan_ty[pid2*N + _pid]?x
   ...
fi
...
typedef T = {
  bit   top;
  mtype con;
  Targ0  t0;
  ..
  Targn  t1;
}
-}
