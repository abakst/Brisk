{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# Language UndecidableInstances #-}
module Brisk.Model.VCGen where
import Data.Char (toUpper, toLower)
import Prelude hiding (pred)
import System.Exit
import System.Directory
import System.Process
import System.IO
import Control.Monad.State
import Data.Set as Set hiding (foldl')
import Data.List hiding (union, (\\))
import qualified Data.List as L
import Text.Printf
import qualified Text.PrettyPrint.HughesPJ as PP

import Brisk.Pretty
import Brisk.UX
import Brisk.Model.IceT hiding (ANFM, fresh)
import qualified Brisk.Model.Types as T
import Brisk.Model.Types (Pred(..), Op(..))
import Brisk.Model.TheoryBuiltins

import Text.Show.Pretty (ppShow)
import qualified Debug.Trace as Dbg

dbg :: Show a => String -> a -> a
dbg m x = Dbg.trace (m ++ ": " ++ ppShow x) x

dbgPP :: Pretty a => String -> a -> a
dbgPP m x = Dbg.trace (m ++ ": " ++ render (pp x) ++ "\n") x

--------------------------------------------------------------------------------
-- VC Gen for ICET statements
--------------------------------------------------------------------------------
type VCPred = Pred T.Id
data VCState s = VC { ctr :: Int
                    , sideConditions :: [VCPred s]
                    , predicates :: [(String, Int)]
                    }
type VCM s a = State (VCState s) a

freshInt :: VCM s Int
freshInt = do c <- gets ctr
              modify $ \s -> s { ctr = c + 1 }
              return c

freshPred :: T.Id -> VCM s T.Id
freshPred p = do c <- freshInt
                 return $ (p ++ "_" ++ show c)

freshId :: T.Id -> VCM s T.Id
freshId x = do c <- freshInt
               return $ "X_" ++ show c
--------------------------------------------------------------------------------
-- System IO
--------------------------------------------------------------------------------
runVC :: (HasType s, Show s, T.Annot s) => IceTStmt s -> IO Bool
runVC s = do (fp, h) <- openTempFile "." "briskseq"
             hPutStr h hcs
             hFlush h
             let cmd = printf "qarmc %s" fp
             (hOut, hIn, hErr, pid) <- runInteractiveCommand cmd
             hClose hOut
             putStrLn hcs
             ec      <- waitForProcess pid
             output  <- hGetContents hIn
             err     <- hGetContents hErr
             putStrLn (printf "Created file at %s." fp)
             case ec of
               ExitSuccess   -> do
                 putStrLn output
                 removeFile fp
                 if isInfixOf "program is correct" output then
                 -- if x == "sat" then
                   putStrLn sat
                 else
                   putStrLn unsat
                 return True
               ExitFailure _ -> do
                 putStrLn (printf "%s: %s" unsat err) >> return False
                 return False
  where hcs = vcGenQARMC $ dbgPP "a-normalized" (anormalize True s)
        sat = "\x1b[1;32mSAT\x1b[0m"
        unsat = "\x1b[1;31mUNSAT\x1b[0m"

--------------------------------------------------------------------------------
-- VC Generation
--------------------------------------------------------------------------------

vcGen :: T.Annot s => VCPred s -> IceTStmt s -> (VCPred s, [VCPred s])
vcGen φ s = (ψ, sideConditions σ)
  where
    (ψ, σ) = runState (wlp φ s) σ0
    σ0     = VC { ctr            = 0
                , predicates     = []
                , sideConditions = []
                }
initState = VC { ctr            = 0
               , predicates     = []
               , sideConditions = []
               }

vcGenQARMC :: (Show s, T.Annot s) => IceTStmt s -> String
vcGenQARMC s
  = flip evalState initState $ do
      φ  <- wlp Top (annotStmt s)
      let clauses = toClauses (dbgPP "VC" φ)
      ψs     <-  mapM horn clauses
      -- is <- gets predicates
      -- let pdecls = unlines $ pdecl <$> is
      --     prelude = "(set-logic HORN)"
      --     check   = "(check-sat)"
      return (unlines ψs)
pdecl (p, n)
  = printf "(declare-fun %s (%s ) Bool)" p (concat $ replicate n " Int")
    -- sidecs  = (\p -> printf "(assert %s)" (smt p)) <$> ps
    -- (p, ps) = vcGen Top s
--------------------------------------------------------------------------------
-- Weakest Liberal Preconditions
--------------------------------------------------------------------------------

----------------------------------------------------------------------------------
-- Need to get all the PID literals that are in scope so we can quantify over them
----------------------------------------------------------------------------------
predPids (BRel _ e1 e2) = nub (exprPids e1 ++ exprPids e2)
predPids (Conj ps) = nub (concatMap predPids ps)
predPids (Disj ps) = nub (concatMap predPids ps)
predPids (p :==>: q) = nub (predPids p ++ predPids q)
predPids (CHC xs p q) = nub ((predPids p ++ predPids q) L.\\ xs)
predPids _ = []

exprPids (T.EVal (Just (T.CPid p)) _ _) = [p]
exprPids (T.EVal (Just (T.CPidSet p)) _ _) = [p]
exprPids (T.EVal _ (Just (_, p)) _) = predPids p
exprPids _ = []

--------------------------------------------------------------------------------
-- This function marks loops with the IDs that are in scope
annotStmt :: IceTStmt s -> IceTStmt s
--------------------------------------------------------------------------------
annotStmt s = evalState (markLoops s) []

markLoops :: IceTStmt s -> State [T.Id] (IceTStmt s)
markLoops (ForEach x xs s) = do g  <- get
                                s' <- markLoops s
                                return $ XForEach x g xs s'
markLoops (While l xs s) = do g <- get
                              s' <- markLoops s
                              return $ While l g s'
markLoops (Seq ss) = Seq <$> mapM markLoops ss
markLoops s@(Recv _ _ x) = do g <- get
                              let g' = maybe g (:g) x
                              put (nub g')
                              return s
markLoops s@(XAssgn p x q e) = do g <- get
                                  put (nub (x : g))
                                  return s
markLoops s@(Assgn x _ _) = do g <- get
                               put (nub (x : g))
                               return s
markLoops s = return s


--------------------------------------------------------------------------------
wlp :: T.Annot s => VCPred s -> IceTStmt s -> VCM s (VCPred s)
--------------------------------------------------------------------------------
wlp φ Skip             = return φ
wlp φ Fail             = return Bot
wlp φ (XAssgn p x q e) = do x' <- freshId x
                            return $ pred e x x φ
wlp φ (Assgn x _ e)    = do x' <- freshId x
                            return $ pred e x x φ
wlp φ (Case e es d)    = wlpCase φ e es d
wlp φ (Seq ss)         = foldM wlp φ (reverse ss)
wlp φ (While l xs s)   = wlpWhile φ l xs s
wlp φ (XForEach x us xs s) = wlpForEach φ x us xs s
wlp φ (Continue l)     = return $ T.substPred [(l, T.EVal (Just $ T.CInt 1) Nothing T.dummyAnnot)] φ
wlp φ (Assert ψ)       = return $ Conj [φ, T.Prop ψ]
wlp φ (Assume ψ)       = return $ T.Prop ψ :==>: φ

wlpForEach φ x us xs s
  = do p  <- freshPred "L"
       let vs = nub (assignVars s ++ us)
           es = T.idExpr <$> vs
       ψ <- wlp (PVar p es) s
       addPredicate p (length vs)
       let φ' = Conj [ PVar p es
                     , CHC (assignVars s) (PVar p es) ψ
                     , CHC (assignVars s) (PVar p es) φ
                     ]

       return φ'

wlpWhile φ l xs s
  = do let vs = nub (assignVars s ++ xs)
       vs'    <- mapM freshId vs
       let exs = T.idExpr <$> vs
           θ   = zip vs exs
       ψ <- wlp (PVar l exs) s
       addPredicate l (length vs)
       let φ' = Conj [ CHC [] Top (PVar l (T.idExpr <$> vs))
                     , CHC (assignVars s) (PVar l exs) ψ
                     , CHC (assignVars s) (PVar l exs) φ
                     ]
       return φ'
   where

wlpCase φ e es d
  = do (gs, φs) <- unzip <$> mapM (wlpAlt φ e) es
       φs'      <- maybe (return []) ((return <$>) . wlp φ) d
       return $ Conj (φs ++ ((Conj (LNot <$> gs) :==>:) <$> φs'))

wlpAlt φ e (p, s)
  = do ψ <- wlp φ s
       return (g, g :==>: ψ)
  where
    g  = BRel Eq e p

addPredicate p n = modify $ \vc -> vc { predicates = (p,n) : predicates vc }
addSideCondition φ = modify $ \vc -> vc { sideConditions = φ : sideConditions vc }

--------------------------------------------------------------------------------
-- Expr Preds
--------------------------------------------------------------------------------
class AsPred a where
  pred :: T.Annot s => a s -> T.Id -> T.Id -> VCPred s -> VCPred s

instance AsPred (T.EffExpr T.Id) where
  pred v@(T.EVal (Just _) _ l) x x' φ
    = T.substPred [(x, v)] φ
  pred (T.EVal _ (Just (v, p)) l) x x' φ
    = T.substPred [(v,T.EVar x' l)] p :==>: T.substPred [(x, T.EVar x l)] φ
  pred (T.EAny _ _) x x' φ
    = φ
  pred e x x' φ
    = T.substPred [(x, e)] φ

--------------------------------------------------------------------------------
-- SMTLIB2 Format
--------------------------------------------------------------------------------

-- class SMTLIB a where
--   smt :: a -> String

-- instance SMTLIB String where
--   smt s = s

-- instance SMTLIB T.Op where
--   smt T.Eq  = "="
--   smt T.Plus = "+"
--   smt T.Minus = "-"
--   smt T.Le  = "<="

-- instance Show a => SMTLIB (IceTExpr a) where
--   smt (T.EVar x _)                         = x
--   smt (T.EVal (Just (T.CPid x)) _ _)       = x
--   smt (T.EVal (Just (T.CInt n)) Nothing _) = show n
--   smt (T.EVal Nothing (Just (v, p)) _)     = smt p
--   smt (T.ECon "True" [] _)                 = "true"
--   smt (T.ECon "False" [] _)                = "false"
--   smt (T.ECon c [] _)                      = c
--   smt (T.ECon c xs _)                      = printf "(%s %s)" c (smtList xs)
--   smt e@(T.EApp _ _ _)                     = printf "(%s %s)" (smt f) (smtList args)
--     where
--       (f, args) = T.collectAppArgs e
--   smt e = "true"
--   smt e = abort "smt" e

-- instance Show a => SMTLIB (VCPred a) where
--   smt Top              = "true"
--   smt Bot              = "false"
--   smt (Prop p)         = printf ("(= %s 1)") (smt p)
--   smt (p :==>: q)      = printf "(=> %s %s)" (smt (Conj p')) (smt q')
--     where
--       (p', q') = mergeImplies p q
--   smt (Conj ps)        = printf "(and %s)" $ smtList ps
--   smt (Disj ps)        = printf "(or %s)" $ smtList ps
--   smt (BRel op e1 e2)  = printf "(%s %s %s)" (smt op) (smt e1) (smt e2)
--   smt (LNot p)         = printf "(not %s)" (smt p)
--   smt (PVar x [])      = x
--   smt (PVar x xs)      = printf "(%s %s)" x (smtList xs)
--   smt (CHC [] p q)     = (smt (p :==>: q))
--   smt (CHC xs p q)     = printf "(forall (%s ) %s)" (quantList xs) (smt (p :==>: q))

class QARMC a where
  qarmc :: a -> String

instance (Eq a, Show a) => QARMC (IceTExpr a) where
  qarmc (T.EVar x _) = toUpper . xlate <$> x
  qarmc (T.EVal (Just (T.CPid x)) _ _) = toUpper . xlate <$> x
  qarmc (T.EVal (Just (T.CInt n)) _ _) = show n
  qarmc (T.EVal _ (Just (v, p)) _) = qarmc p
  qarmc (T.EVal _ _ _)  = "_"
  qarmc (T.ECon c as _) = printf "%s([%s])" c (tupled as)
  qarmc (BinApp "+" _ e1 _ e2 _) = printf "%s+%s" (qarmc e1) (qarmc e2)
  qarmc (T.EAny _ _) = "_"
  qarmc e = abort "qarmc" e

xlate '$' = '_'
xlate c   = c

pattern BinApp f l1 e1 l2 e2 l3 = T.EApp (T.EApp (T.EVar f l1) e1 l2) e2 l3

tupled xs = intercalate "," (qarmc <$> xs)

instance QARMC Op where
  qarmc Eq = "="
  qarmc Le = "=<"
  qarmc NEq = "=\\="

instance (Eq a, Show a) => QARMC (VCPred a) where
  qarmc Top          = "true"
  qarmc Bot          = "false"
  qarmc (BRel op e1 e2) = printf "%s%s%s" (qarmc e1) (qarmc op) (qarmc e2)
  qarmc (p :==>: q)  = printf "(%s)" (qarmc $ Disj [LNot p', q'])
    where
      (p' :==>: q') = push p q
  qarmc (Prop p)     = printf "%s=1" (qarmc p)
  qarmc (Conj [])    = "true"
  qarmc (Conj [p])   = qarmc p
  qarmc (Conj ps)    = printf "(%s)" (intercalate "," (qarmc <$> ps))
  qarmc (Disj [p])   = qarmc p
  qarmc (Disj [])    = "false"
  qarmc (Disj ps)    = printf "(%s)" (intercalate ";" (qarmc <$> ps))
  qarmc (LNot p@(PVar x xs)) = printf "\\+(%s)" (qarmc p)
  qarmc (LNot (Prop p)) = printf "%s=0" (qarmc p)
  qarmc (LNot p)     = printf "%s" (qarmc (neg p))
  qarmc (CHC xs p q) = printf "%s :- %s." (qarmc q) (qarmc p)
  qarmc (PVar x xs)  = printf "%s(%s)" (toLower <$> x) (tupled xs)

neg Top = Bot
neg Bot = Top
neg (BRel Eq e1 e2) = BRel NEq e1 e2
neg (BRel Le e1 e2) = Conj [ BRel Le e2 e1, BRel NEq e1 e2 ]
neg (Conj ps) = Disj (neg <$> ps)
neg (Disj ps) = Conj (neg <$> ps)
neg (p :==>: q) = conj p (neg q)
neg p = LNot p

compact (Disj ps) = Disj (compact <$> ps)
compact (CHC xs p q) = CHC xs (compact p) (compact q)
compact (Conj ps)
  = case [ p | p <- compact <$> ps, p /= Top ] of
     [] -> Top
     [p] -> p
     ps' -> Conj ps'
compact (p :==>: q) = compact p :==>: compact q
compact (LNot p) = LNot (compact p)
compact p = p

toClauses (p :==>: q)   = push p <$> toClauses q
toClauses (Conj (p:ps)) = p : concatMap toClauses ps
toClauses (CHC xs p q) = [CHC xs p' q']
  where (p' :==>: q') = push p q
toClauses p@(Prop e) = [CHC [] Top p]
toClauses p = abort "toClauses" p

push p (q :==>: r)      = push (conj p q) r
push p (CHC xs q r)     = CHC xs p' r'
  where
    p' :==>: r' = push (conj p q) r
push p q                = compact p :==>: compact q

conj (Conj ps) (Conj qs) = Conj (ps ++ qs)
conj p (Conj qs)         = Conj (p : qs)
conj (Conj ps) q         = Conj (q : ps)
conj p q                 = Conj [p,q]

mergeImplies p = go [p]
  where
    go ps (p :==>: q) = go (p:ps) q
    go ps q           = (ps, q)

horn :: (Show a, T.Annot a) => VCPred a -> VCM a String
horn p = unlines <$> horn' p

horn' (p :==>: Conj qs)
  = concat <$> mapM horn' ((p :==>:) <$> qs)
horn' (p :==>: CHC xs q r)
  = do xs' <- mapM freshId xs
       let q' = T.substPred θ q
           r' = T.substPred θ r
           θ  = [ (x, T.EVar x' T.dummyAnnot) | (x,x') <- zip xs xs' ]
       horn' $ CHC xs' (compact $ conj p q') r'
horn' (Conj ps)
  = concat <$> mapM horn' ps
horn' chc@(CHC xs p q)
  = return [qarmc $ CHC (toList xs') p q]
  where
    xs' = unions [T.fvPred p, T.fvPred q, fromList xs]
          \\ (fromList ["+"])
horn' p
  = horn' (CHC [] Top p)


-- quantList :: [T.Id] -> String
-- quantList xs = foldl' go "" xs
--   where
--     go a x = printf "%s (%s Int)" a (smt x)

----- Testing
p0 = Top
s0 = Seq [ Case (T.ECon "True" [] ())
           [ ( T.ECon "True"  [] ()
             , Skip
             )
           ]
           (Just Fail)
         ,
           Skip
         ]
s1 = Seq [ Case (T.ECon "True" [] ())
           [ ( T.ECon "False"  [] ()
             , Skip
             )
           ]
           (Just Fail)
         ,
           Skip
         ]

s2 = Seq [ Assgn "x" Nothing (T.EVal (Just $ T.CInt 0) Nothing ())
         , Assgn "y" Nothing (T.EVal (Just $ T.CInt 1) Nothing ())
         , While "i" ["x", "y"] (Assgn "x" Nothing (T.EVal (Just $ T.CInt 1) Nothing ()))
         , Assert (T.val $ \_ -> (T.EVar "y" ()) T..=
                                 (T.val $ \v -> v T..= (T.EApp (T.EApp (T.EVar "+" ()) (T.EVar "x" ()) ()) (T.int 1) ())))
         ]

s3 = Seq [ XAssgn "p" "phi0" "q" (T.EVal Nothing (Just ("$vv", BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 0)) Nothing ()))) ())
         , Assert (T.EVar "phi0" ())
         -- , While "I" ["x", "y"] (XAssgn "p" "x" "q" (T.EVal (Just (T.CInt 1)) Nothing ()))
         -- , XAssgn "p" "phi1" "q" (T.EVal Nothing (Just ("$vv", Disj [ BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 0)) Nothing ())
         --                 , BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 1)) Nothing ())
         --                 ])) ())
         -- , Assert $ T.EVar "phi1" ()
         ]

-- s4 = Seq [ Assume (BRel Eq (T.EVar "f" ()) (T.EVal (Just (T.CInt 0)) Nothing ()))
--          , XAssgn "p" "z" "q" (T.EVal (Just (T.CPid "aaaa")) Nothing ())
--          -- , ForEach "x" (False, T.EVar "xs" ())
--          --     $ XAssgn "p" "a" "q" (T.EVal (Just (T.CInt 1)) Nothing ())
--          , Assert $ Disj [ BRel Eq (T.EVar "a" ()) (T.EVal (Just (T.CInt 0)) Nothing ())
--                          , BRel Eq (T.EVar "a" ()) (T.EVal (Just (T.CInt 1)) Nothing ())
--                          ]
--          ]

prop x = T.Prop x
one = (T.EVal (Just (T.CInt 1)) Nothing ())
foo = Seq [ Assert (T.val $ \v -> (T.int 2 T..< T.int 3) )
          ] :: IceTStmt ()
instance HasType () where
  getType () = Nothing
  setType _ _ = ()
