{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# Language UndecidableInstances #-}
module Brisk.Model.VCGen where

import System.Exit
import System.Process
import System.IO
import Control.Monad.State
import Data.Set as Set hiding (foldl')
import Data.List hiding (union, (\\))
import Text.Printf
import qualified Text.PrettyPrint.HughesPJ as PP

import Brisk.Pretty
import Brisk.Model.IceT hiding (ANFM, fresh)
import qualified Brisk.Model.Types as T
import Brisk.Model.Types (Pred(..), Op(..))

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

freshId :: T.Id -> VCM s T.Id
freshId x = do c <- gets ctr
               modify $ \s -> s { ctr = c + 1 }
               return $ "x!" ++ show c

--------------------------------------------------------------------------------
-- Substitution
-------------------------------------------------------------------------------
substPred :: T.Subst T.Id (IceTExpr a)
          =>  [(T.Id, IceTExpr a)]
          -> VCPred a
          -> VCPred a
substPred θ (φ :==>: ψ)    = substPred θ φ :==>: substPred θ ψ
substPred θ (Conj φs)      = Conj (substPred θ <$> φs)
substPred θ (Disj φs)      = Disj (substPred θ <$> φs)
substPred θ (LNot φ)       = LNot $ substPred θ φ
substPred θ (BRel o e1 e2) = BRel o (T.subst θ e1) (T.subst θ e2)
substPred θ (PVar p xs)    = PVar p (T.subst θ <$> xs)
substPred θ (CHC xs p q)   = CHC xs (substPred θ' p) (substPred θ' q)
  where θ' = [ (x,e) | (x,e) <- θ, x `notElem` xs ]
substPred θ φ              = φ

fvPred :: T.Subst T.Id (IceTExpr a)
          => VCPred a
          -> Set T.Id
fvPred (φ :==>: ψ) = union (fvPred φ) (fvPred ψ)
fvPred (Conj φs)   = unions (fvPred <$> φs)
fvPred (Disj φs)   = unions (fvPred <$> φs)
fvPred (LNot φ)    = fvPred φ
fvPred (BRel o e1 e2) = union (T.fv e1) (T.fv e2)
fvPred (PVar p xs)    = unions (T.fv <$> xs)
fvPred (CHC xs p q)   = union (fvPred p) (fvPred q) \\ fromList xs
fvPred Top            = Set.empty
fvPred Bot            = Set.empty
--------------------------------------------------------------------------------
-- System IO
--------------------------------------------------------------------------------
runVC :: T.Annot s => IceTStmt s -> IO Bool
runVC s = do (hOut, hIn, _, pid) <- runInteractiveCommand "z3 -smt2 -in"
             hPutStrLn hOut smtlib2
             ec <- waitForProcess pid
             case ec of
               ExitSuccess   -> do
                 putStrLn sat
                 return True
               ExitFailure _ -> do
                 x <- hGetLine hIn
                 putStrLn smtlib2
                 putStrLn (printf "%s: %s" unsat x) >> return False
                 return False
  where smtlib2 = vcGenSMT s
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

vcGenSMT :: T.Annot s => IceTStmt s -> String
vcGenSMT s = flip evalState initState $ do
               φ  <- wlp Top s
               ψs <- horn φ
               is <- gets predicates
               let pdecls = unlines $ pdecl <$> is
                   prelude = "(set-logic HORN)"
                   check   = "(check-sat)"
               return $ unlines [ prelude
                                , pdecls
                                , ψs
                                , check
                                ]
pdecl (p, n)
  = printf "(declare-fun %s (%s ) Bool)" p (concat $ replicate n " Int")
    -- sidecs  = (\p -> printf "(assert %s)" (smt p)) <$> ps
    -- (p, ps) = vcGen Top s
--------------------------------------------------------------------------------
-- Weakest Liberal Preconditions
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
wlp :: T.Annot s => VCPred s -> IceTStmt s -> VCM s (VCPred s)
--------------------------------------------------------------------------------
wlp φ Skip             = return φ
wlp φ Fail             = return Bot
wlp φ (XAssgn p x q e) = return $ substPred [(x,e)] φ
wlp φ (Case e es d)    = wlpCase φ e es d
wlp φ (Seq ss)         = foldM wlp φ (reverse ss)
wlp φ (While l xs s)   = wlpWhile φ l xs s
wlp φ (Continue l)     = return $ substPred [(l, T.EVal (Just $ T.CInt 1) T.dummyAnnot)] φ
wlp φ (Assert ψ)       = return $ Conj [φ, ψ]
wlp φ (Assume ψ)       = return $ ψ :==>: φ

wlpWhile φ l xs s
  = do ψ <- wlp (PVar l exs) s
       addPredicate l (length xs)
       let φ' = Conj [ PVar l exs
                     , CHC xs (PVar l exs) ψ
                     , CHC xs (PVar l exs) φ
                     ]
       return φ'
   where
     exs = flip T.EVar T.dummyAnnot <$> xs

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
-- SMTLIB2 Format
--------------------------------------------------------------------------------

class SMTLIB a where
  smt :: a -> String

instance SMTLIB String where
  smt s = s

instance SMTLIB T.Op where
  smt T.Eq = "="
  smt T.Le = "<="

instance SMTLIB (IceTExpr a) where
  smt (T.EVar x _)    = x
  smt (T.EVal (Just (T.CInt n)) _) = show n
  smt (T.ECon "True" [] _) = "true"
  smt (T.ECon "False" [] _) = "false"
  smt (T.ECon c [] _) = c
  smt (T.ECon c xs _) = printf "(%s %s)" c (smtList xs)

instance SMTLIB (VCPred a) where
  smt Top              = "true"
  smt Bot              = "false"
  smt (p :==>: q)      = printf "(=> %s %s)" (smt p) (smt q)
  smt (Conj ps)        = printf "(and %s)" $ smtList ps
  smt (Disj ps)        = printf "(or %s)" $ smtList ps
  smt (BRel op e1 e2)  = printf "(%s %s %s)" (smt op) (smt e1) (smt e2)
  smt (LNot p)         = printf "(not %s)" (smt p)
  smt (PVar x [])      = x
  smt (PVar x xs)      = printf "(%s %s)" x (smtList xs)
  smt (CHC [] p q)     = (smt (p :==>: q))
  smt (CHC xs p q)     = printf "(forall (%s ) %s)" (quantList xs) (smt (p :==>: q))

horn :: T.Annot a => VCPred a -> VCM a String
horn p = (unlines . fmap mkAssert) <$> horn' p
  where mkAssert p = printf "(assert %s)" p

horn' (p :==>: Conj qs)
  = concat <$> mapM horn' ((p :==>:) <$> qs)
horn' (p :==>: CHC xs q r)
  = do xs' <- mapM freshId xs
       let q' = substPred θ q
           r' = substPred θ r
           θ  = [ (x, T.EVar x' T.dummyAnnot) | (x,x') <- zip xs xs' ]
       horn' $ CHC xs' (Conj [p, q']) r'
horn' (Conj ps)
  = concat <$> mapM horn' ps
horn' (CHC xs p q)
  = return [smt $ CHC (toList xs') p q]
  where
    xs' = unions [fvPred p, fvPred q, fromList xs]
horn' p
  = horn' (CHC [] Top p)


quantList :: [T.Id] -> String
quantList xs = foldl' go "" xs
  where
    go a x = printf "%s (%s Int)" a (smt x)

smtList :: SMTLIB a => [a] -> String
smtList = foldl' (\a x -> printf "%s %s" a (smt x)) ""

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

s2 = Seq [ XAssgn "p" "x" "q" (T.EVal (Just $ T.CInt 0) ())
         , XAssgn "p" "y" "q" (T.EVal (Just $ T.CInt 1) ())
         , While "I" ["x", "y"] (XAssgn "p" "x" "q" (T.EVal (Just $ T.CInt 1) ()))
         ]

s3 = Seq [ Assume (BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 0)) ()))
         , While "I" ["x", "y"] (XAssgn "p" "x" "q" (T.EVal (Just (T.CInt 1)) ()))
         , Assert $ Disj [ BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 0)) ())
                         , BRel Eq (T.EVar "x" ()) (T.EVal (Just (T.CInt 1)) ())
                         ]
         ]
