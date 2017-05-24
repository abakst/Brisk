{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# Language AllowAmbiguousTypes #-}
module Brisk.Model.VCGen where
import Data.Function
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

data TransitionState s = TS { tsSets     :: [ProcessId]
                            -- ^ Xs
                            , tsUnfolded :: [(ProcessId, [ProcessId])]
                            -- ^ (x in X)
                            , tsVars     :: [(ProcessId, [T.Id])]
                            , tsSingVars :: [T.Id]
                            -- ^ The (X, [v1, v2, v3...])
                            , tsLoopVars :: [T.Id]
                            -- ^ while_X, for(x in X)
                            , tsPC       :: Int
                            -- ^ fresh program counter
                            , tsLoop     :: Int
                            -- ^ fresh loop counter
                            , tsAssumes  :: [VCPred s]
                            , tsQueries  :: [VCPred s]
                            }
  
freshPc :: TXM s Int
freshPc = do i <- gets tsPC
             modify $ \s -> s { tsPC = i + 1 }
             return i

freshLoopVar :: TXM s T.Id
freshLoopVar = do i <- gets tsLoop
                  modify $ \s -> s { tsLoop = i + 1 }
                  return ("W__" ++ show i)

addLoopVar :: T.Id -> TXM s ()
addLoopVar x = modify $ \s -> s { tsLoopVars = x $:$ tsLoopVars s }  

type TXM s a = State (TransitionState s) a

data UnfoldState = US { ufs    :: [(ProcessId, [ProcessId])]
                      , ufvars :: [(ProcessId, [T.Id])]
                      }
  deriving (Eq, Show)

data VarBind a  = System T.Id a
                | Concr  T.Id a
                | Abs    ProcessId ProcessId T.Id a

  deriving (Eq, Show)
type Upd s = VarBind (T.Pred T.Id s)

data Transition s = Tx { pcIn   :: Int
                       , pcOut  :: Maybe Int
                       , txRel  :: [Upd s]
                       , txGrd  :: [VCPred s]
                       , txStmt :: IceTStmt s
                       , txUfs  :: UnfoldState
                       }
                  | Loop { pcIn      :: Int
                         , pcOut     :: Maybe Int
                         , loopCond  :: VCPred s
                         , loopEnter :: [Upd s]
                         , loopExit  :: [Upd s]
                         , loopTxs   :: [Transition s]
                         , txGrd  :: [VCPred s]
                         }
                  | Branch { pcIn      :: Int
                           , cond      :: VCPred s
                           , pcOut     :: Maybe Int
                           , branchTxs :: [Transition s]
                           , txGrd     :: [VCPred s]
                           }
  deriving (Show, Eq)

-- inv([x0, x1, ...], [(ps, [y0, y1,...]), (qs, [z0,...])])
data Invariant = Inv [T.Id] [(ProcessId, [T.Id])]

initTxState :: TransitionState s
initTxState = TS { tsSets     = []
                 , tsUnfolded = []
                 , tsVars     = []
                 , tsSingVars = []
                 , tsLoopVars = []
                 , tsPC       = 0
                 , tsLoop     = 0
                 , tsAssumes  = []
                 , tsQueries  = []
                 }
--------------------------------------------------------------------------------
-- Operations on transitions
--------------------------------------------------------------------------------
composeTxns :: T.Annot s => [Transition s] -> [Transition s]
composeTxns ts
  = [ t | Just t <- ts' ]
  where
    tgs = group ([], []) ts
    ts' = composeSimple <$> tgs

    group (c, ts) []           = reverse (reverse c : ts)
    group (c, ts) (t@Tx{}:ts') = group (t:c, ts) ts'
    group (c, ts) (t:ts')      = group ([], [t] : reverse c : ts) ts'

composeSimple :: T.Annot s => [Transition s] -> Maybe (Transition s)
composeSimple []
  = Nothing
composeSimple [t]
  = Just t
composeSimple ts
  | all isSimpleTxn ts
  = Just t { txRel = txRel t ++ (setFinal <$> sub') }
  | otherwise
  = abort "composeSimple: unexpected" ()
  where
    setFinal :: T.Annot s => VarBind Int -> Upd s
    setFinal (System x n)
      = System x $ mkVal x n
    setFinal (Concr x n)
      = Concr x $ mkVal x n
    setFinal (Abs ps p x n)
      = Abs ps p x $ mkVal (qvarName p x) n

    mkVal x n = T.vvExpr T..= T.EVar (x ++ show (n - 1)) T.dummyAnnot
    
    isSimpleTxn Tx{} = True
    isSimpleTxn _    = False

    (sub', Just t @ Tx{}) = foldl' go ([], Nothing) ts

    go ([], Nothing) t  = initialSub t
    go (sub, Just t) t' = compose sub t t'

initialSub :: T.Annot s => Transition s -> ([VarBind Int], Maybe (Transition s))
initialSub t@Tx {}
  = (sub, Just t { txRel = rels})
  where
    (sub, rels)      = foldl' go ([], []) (txRel t)
    go (sub, rels) u = let (su', [u']) = do1Upd [] (sub, []) u in
                       (su', u':rels)
initialSub _
  = abort "initialSub: unexpected" ()

compose :: T.Annot s
        => [VarBind Int] -> Transition s -> Transition s -> ([VarBind Int], Maybe (Transition s))
compose sub t1 @ Tx{} t2 @ Tx {}
  = (sub', t')
  where
    t' = Just Tx { pcIn   = pcIn t1
                 , pcOut  = pcOut t2
                 , txRel  = txRel t1 ++ rel'
                 , txStmt = seqStmts [txStmt t1, txStmt t2]
                 , txUfs  = txUfs t2 -- FIXME
                 , txGrd  = txGrd t1 ++ (T.substPred esub <$> txGrd t2)
                 }
    esub         = bindSub <$> sub

    bindSub (System x n)   = (x, T.EVar (x ++ show (n - 1)) T.dummyAnnot)
    bindSub (Concr x n )   = (x, T.EVar (x ++ show (n - 1)) T.dummyAnnot)
    bindSub (Abs ps p x n) = (x, T.EVar (qvarName p x ++ show (n - 1)) T.dummyAnnot)
    (sub', rel') = foldl' (do1Upd esub) (sub, []) (txRel t2)
compose sub _ _
  = (sub, Nothing)

do1Upd esub (su, upds) b@(System x e)
  = let (n', su') = nextSub b su in
    (su', System (x ++ show n') (T.substPred esub e) : upds)
do1Upd esub (su, upds) b@(Concr x e)
  = let (n', su') = nextSub b su in
    (su', Concr (x ++ show n') (T.substPred esub e) : upds)
do1Upd esub (su, upds) b@(Abs ps p x e)
  = let (n', su') = nextSub b su in
    (su', Abs ps p (x ++ show n') (T.substPred esub e) : upds)

nextSub :: Upd s -> [VarBind Int] -> (Int, [VarBind Int])
nextSub (System x _) (System x' n : sub)
  | x == x'
  = (n, System x (n+1):sub)
nextSub (Concr x _) (Concr x' n : sub)
  | x == x'
  = (n, Concr x (n+1):sub)
nextSub (Abs ps p x _) (Abs ps' p' x' n : sub)
  | ps == ps', p == p', x == x'
  = (n, Abs ps p x (n+1) : sub)
nextSub b (b':sub)
  = (b':) <$> nextSub b sub
nextSub b []
  = (0, [b' 1])
  where b' = case b of
               System x _   -> System x
               Concr x _    -> Concr x
               Abs ps p x _ -> Abs ps p x
    

{- 
composeTx :: (T.Annot s, Show s) => Int -> Transition s -> Transition s -> Maybe (Transition s)
composeTx n t1 @ Tx {} t2 @ Tx {}
  = Just  Tx { pcIn   = pcIn t1
             , pcOut  = pcOut t2
             , txRel  = composeRels n (txRel t1) (txRel t2)
             , txStmt = seqStmts [ txStmt t1, txStmt t2 ]
             , txUfs  = txUfs t2 -- FIXME
             , txGrd  = txGrd t2 -- FIXME
             }
composeTx _ t1 t2
  = Nothing

composeTxs :: (T.Annot s, Show s) => [Transition s] -> [Transition s]
composeTxs ts
  = snd $ foldl' go (0, []) ts
  where
    go (n, []) t       = (n, [t])
    go (n, tlast:ts) t
      | Just t' <- composeTx n tlast t
      = (n+1, t':ts)
      | otherwise
      = (n, t:tlast:ts)
                         

composeRels :: (T.Annot s, Show s) => Int -> [Upd s] -> [Upd s] -> [Upd s]
composeRels n u1s u2s
  = [ System x e | (x, e) <- composeSingleUs n u1Sys u2Sys ] ++ 
    [ System x e | (x, e) <- u2Sys, x `notElem` sysCommon  ] ++
   
    [ Concr  x e | (x, e) <- composeSingleUs n u1Con u2Con ] ++ 
    [ Concr  x e | (x, e) <- u2Con, x `notElem` conCommon  ] ++

    [ Abs ps p x e | ((ps,p,x), e) <- composeAbsUs n u1Abs u2Abs           ] ++
    [ Abs ps p x e | ((ps,p,x), e) <- u2Abs, (ps,p,x) `notElem` absCommon  ]
    
  where
    u1Sys     = [ (x, e) | System x e <- u1s ]
    u2Sys     = [ (x, e) | System x e <- u2s ]
    sysCommon = L.intersect (fst <$> u1Sys) (fst <$> u2Sys)
    

    u1Con = [ (x, e) | Concr x e <- u1s ]
    u2Con = [ (x, e) | Concr x e <- u2s ]
    conCommon = L.intersect (fst <$> u1Con) (fst <$> u2Con)

    u1Abs = [ ((ps, p, x), e) | Abs ps p x e <- u1s ]
    u2Abs = [ ((ps, p, x), e) | Abs ps p x e <- u2s ]
    absCommon = L.intersect (fst <$> u1Abs) (fst <$> u2Abs)

    composeSingleUs n l1 l2
      = do (x,e) <- l1
           case L.lookup x l2 of
             Just e' -> return $composeSingle n (x,e) e'
             _       -> return (x, e)
    composeAbsUs n l1 l2
      = do (x,e) <- l1
           case L.lookup x l2 of
             Just e' -> return $ composeAbs n (x,e) e'
             _       -> return (x, e)

composeSingle n (x1,e1) e2
  = (x1, conj e1' e2')
  where
    x1' = T.EVar (x1 ++ show n) T.dummyAnnot
    e1' = T.substPred [(T.vv, x1')] e1
    e2' = T.substPred [(x1, x1')] e2
composeAbs n (v1@(ps1,p1,x1),e1) e2
  = (v1,  conj e1' e2')
  where
    x1' = T.EVar (x1 ++ show n) T.dummyAnnot
    e1' = T.substPred [(T.vv, x1')] e1
    e2' = T.substPred [(x1, x1')] e2
-}
--------------------------------------------------------------------------------
-- unfold p:P in s...
-- let v be a var of P
-- let p0 be unfolded of P
-- forall p:P. inv(x,y,v)  ==> inv(x,y,p,p_v)
-- inv(x_next,y_next,p_next,p_v_next) :- ...-
--    inv(x,y,p0,p0_v),((p0=p_next, p0_v_next=p_v_next) ; ...
--------------------------------------------------------------------------------
-- Invariant templates
--------------------------------------------------------------------------------
invTemplate :: [T.Id] -> [(ProcessId, [T.Id])] -> String
invTemplate vs qvs
  = printf "inv%s" (tupled vstrs)
  where
    vstrs = vs ++ concat [ q : (qvarName q <$> xs) | (q, xs) <- qvs ]

qvarName :: ProcessId -> T.Id -> String
qvarName p x = printf "%s__%s" p x

--------------------------------------------------------------------------------
-- Debugging
--------------------------------------------------------------------------------
instance Show s => Pretty (Upd s) where
  ppPrec _ (Abs ps p x e)
    = pp x PP.<+> PP.text ":=" PP.<+> pp e
  ppPrec _ (Concr x e)
    = pp x PP.<+> PP.text ":=" PP.<+> pp e
  ppPrec _ (System x e)
    = pp x PP.<+> PP.text ":=" PP.<+> pp e
  

instance Show s => Pretty (Transition s) where
  ppPrec _ Tx {pcIn=pc, pcOut=Just pc', txRel=preds, txStmt=s}
    = PP.int pc PP.<+> PP.text "==>" PP.<+> PP.int pc' PP.<> PP.text ":" PP.<+> pp preds
  ppPrec _ Tx {pcIn=pc, pcOut=Nothing, txRel=preds, txStmt=s}
    = PP.int pc PP.<+> PP.text ":" PP.<+> pp preds
  ppPrec _ t
    = abort "pp transition" t

--------------------------------------------------------------------------------
-- Compute the transition relation
--------------------------------------------------------------------------------
exprPred :: (Show s, T.Annot s) => IceTExpr s -> T.Pred T.Id s
exprPred v@(T.EVal (Just (T.CInt i)) _ l)
  = T.BRel T.Eq (T.vvExpr { T.annot = l }) (T.EVal (Just (T.CInt i)) Nothing l)
exprPred v@(T.EVal _ (Just (vv, p)) l)
  = p
exprPred e
  = abort "exprPred" e
-- x := {v | v = x + 1} ===> inv(x1) :- inv(x0), x1=x0+1
nextVar :: String -> String
nextVar v = v ++ "_NEXT"

-- findVar :: ProcessId -> T.Id -> TXM s (T.Id
-- findVar p x
--   = do sets    <- gets tsSets
--        unfolds <- gets tsUnfolded
--        vs      <- gets tsVars
--        return $ findVar' sets unfolds vs
--   where
--     findVar' sets unfolds vs
--      | Just _ <- lookup p unfolds = qvarName p x 
--      | otherwise                  = x

varUpd :: T.Annot s => ProcessId -> T.Id -> TXM s (T.Pred T.Id s -> Upd s)
varUpd p x
  = do us  <- gets tsUnfolded
       case [ q | (q, qs) <- us, p `elem` qs  ] of
         []   -> return $ Concr x
         [ps] -> return $ Abs ps p x
         qs   -> abort "varUpd" (p, qs)

tx :: (Eq s, Show s, T.Annot s) => IceTStmt s -> TXM s [Transition s]
tx (Assume p)
  = do modify $ \s -> s { tsAssumes = T.BRel T.Eq p (T.int 1) : tsAssumes s }
       return []

tx (Assert p)
  = undefined
  
tx s@(Assgn x _ e)
  = do pc <- freshPc
       us <- gets tsUnfolded
       vs <- gets tsVars
       gs <- gets tsAssumes
       let rel = exprPred e
       addSysVar x
       return [ Tx pc Nothing [System x rel] gs s US { ufs = us, ufvars = vs } ]

tx s@(XAssgn p x _ e)
  = do updf <- varUpd p x
       pc   <- freshPc
       us   <- gets tsUnfolded
       vs   <- gets tsVars
       gs   <- gets tsAssumes
       addVar p x
       return [ Tx pc Nothing [updf (exprPred e)] gs s US { ufs = us, ufvars = vs } ]

tx Skip
  = return []

tx (Continue l)
  = tx (Assgn l Nothing $ T.val $ \v -> v T..= T.int 1)

tx (XUnfold ps p s)
  = do let upd v = maybe [p] (p$:$) v
       addSysVar p
       modify $ \st -> st { tsUnfolded = ins ps upd (tsUnfolded st) }
       tx s

tx (Seq ss)
  = do ts <- mapM tx ss
       let ts0 = L.foldl' stitchPcs [] ts
       return (reverse . concat $ ts0)
  where
    stitchPcs [] ts
     = [ts]
    stitchPcs ((t0:t0s):prevs) (t:ts1)
     = reverse (t:ts1):(t0 { pcOut = Just $ pcIn t} : t0s):prevs
    stitchPcs ts []
     = ts

tx (While c _ s)
  = do pc   <- freshPc
       ts_s <- composeTxns <$> tx s
       addLoopVar c
       let t = Loop { pcIn      = pc
                    , pcOut     = Nothing
                    , loopEnter = [System c (T.vvExpr T..= T.int 0)]
                    , loopExit  = []
                    , loopCond  = T.EVar c T.dummyAnnot T..= T.int 1
                    , loopTxs   = setPcOut pc `onLast` ts_s
                    , txGrd     = []
                    }
       return [t]
  
tx s
  = abort "tx" s

setPcOut :: Int -> Transition s -> Transition s
setPcOut pc t = t { pcOut = Just pc }  

onLast :: (Transition s -> Transition s)
       -> [Transition s] -> [Transition s]
onLast f ts
  = case reverse ts of
      t_n:ts' -> reverse $ f t_n : ts'
      []      -> []

addSysVar :: T.Id -> TXM s ()
addSysVar x
  = modify $ \s -> s { tsSingVars = x $:$ tsSingVars s }

findSet :: ProcessId -> TXM s (Maybe ProcessId)
findSet p
  = do us <- gets tsUnfolded
       return $ case [ ps | (ps, ufs) <- us, p `elem` ufs ] of
                 ps:_ -> Just ps
                 _    -> Nothing

addVar :: ProcessId -> T.Id -> TXM s ()  
addVar p x
  = do vs <- gets tsVars
       ps <- findSet p
       let f v = maybe [x] (x$:$) v
       case ps of
         Just ps' ->
           modify $ \s -> s { tsVars = ins ps' f vs }
         _ ->
           modify $ \s -> s { tsSingVars = x $:$ tsSingVars s }
         

ins :: Eq k => k -> (Maybe v -> v) -> [(k,v)] -> [(k,v)]
ins k v []           = [(k,v Nothing)]
ins k v ((k',v'):vs)
  | k == k'   = (k',v (Just v')) : vs
  | otherwise = (k',v') : ins k v vs


($:$) :: T.Id -> [T.Id] -> [T.Id]
x $:$ xs = L.nub (x:xs)
-------------------------------------------------------------------------------  
-- From an IceT Stmt
-------------------------------------------------------------------------------  
fromIceT s
  = undefined

runStmt :: (Show s, Eq s, T.Annot s) => [ProcessId] -> IceTStmt s -> String
runStmt sets s
  = unlines (qarmcTx vs arrs <$> ts)
  where
    vs       = tsSingVars st ++ tsLoopVars st
    arrs     = tsVars st
    (ts, st) = runStmt' sets s

runStmt' :: (Show s, Eq s, T.Annot s)
         => [ProcessId] -> IceTStmt s -> ([Transition s], TransitionState s)
runStmt' sets s
  = runState (run s) (initTxState {tsSets = sets})
  where
    run s = composeTxns <$> tx s
-------------------------------------------------------------------------------  
-- Printing transitions to strings for Q'ARMC
-------------------------------------------------------------------------------  
qarmcTx :: (Show s, Eq s, T.Annot s)
        => [T.Id]
        -> [(ProcessId, [T.Id])]
        -> Transition s
        -> String
qarmcTx vs arrs t@Loop{}
  = unlines (branch : body)
            
  where
    body = qarmcTx vs arrs <$> loopTxs t 
    branch = printf "inv%s :- inv%s, PC=%s, ite(%s, %s, PC_NEXT=%s)."
               (tupled (nextVar "PC" : allXs))
               (tupled ("PC" : allXs))
               (qarmc $ pcIn t)
               (qarmc $ loopCond t)
               enter
               (qarmc $ maybe (-1) id (pcOut t))

    allXs   = qarmc . flip T.EVar () <$> allVars
    allVars = vs ++ concatMap snd arrs

    enter :: String
    enter = tupled ( printf "PC_NEXT=%s" (qarmc $ pcIn (head (loopTxs t)))
                   : (qarmcUpd vs arrs <$> loopEnter t)
                   )


qarmcTx vs arrs t@Tx{}
    = printf "/*\n%s\n*/\n%s\n" (render . pp $ txStmt t) txString
  where
    txString :: String
    txString = printf "inv%s :- \n\t  inv%s,%s\n%s\t."
                 (tupled nextxs) (tupled xs) pcstr (unlines tstr)

    pcstr :: String
    pcstr   = printf "PC=%s,PC_NEXT=%s" (qarmc $ pcIn t) (qarmc $ maybe (-1) id (pcOut t))

    tstr    = ("\t, "++) <$> assumes ++ unfolds ++ rels ++ folds
    assumes = qarmc            <$> txGrd t
    rels    = qarmcUpd vs arrs <$> txRel t
    unfolds = unfoldVars (txUfs t)
    folds   = foldVars fvs (txUfs t)
    fvs     = [ x | Abs _ _ x _ <- txRel t ]

    nextv v | v `elem` changed = nextVar v
            | otherwise        = v
    nextxs  = qarmc . flip T.EVar () . nextv <$> allVars
    xs      = qarmc . flip T.EVar ()         <$> allVars
    allVars = "PC" : (vs ++ concatMap snd arrs)
    changed = "PC" : updVars (txRel t)

updVars us
  = go <$> us
  where
    go (System x _)  = x
    go (Concr x _)   = x
    go (Abs _ _ x _) = x

qarmcUpd xs arrs (System x e)
  = qarmc pred
  where
    pred = T.substPred [(T.vv, T.EVar v' T.dummyAnnot)] e
    v'   = if x `elem` xs then nextVar x else x
qarmcUpd xs arrs (Concr x e)
  = qarmc pred
  where
    pred = T.substPred [(T.vv, T.EVar v' T.dummyAnnot)] e
    v'   = if x `elem` xs then nextVar x else x
qarmcUpd xs arrs (Abs ps p x e)  
  = qarmc pred
  where
    pred = T.substPred [(T.vv, T.EVar v' T.dummyAnnot)] e
    v'   = case lookup ps arrs of
             Just vs | x `elem` vs -> nextVar $ qvarName p x
             _                     -> qvarName p x

unfoldVars :: UnfoldState -> [String]  
unfoldVars US { ufs = us, ufvars = vs }
  = [ unfoldVar (varStr p0) (varStr x)
    | (p, xs) <- vs
    , Just ps <- return $ L.lookup p us
    , p0 <- (toUpper <$>) <$> ps
    , x <- (toUpper <$>) <$> xs
    ]

foldVars :: [T.Id] -> UnfoldState -> [String]
foldVars xs US { ufs = us, ufvars = vs } 
  = [ foldVar (varStr p0) (varStr y) (varStr $ nextVar (qvarName p0 y)) (varStr$nextVar y)
    | (p, ys) <- vs
    , Just ps <- return $ L.lookup p us
    , p0 <- ps
    , y  <- ys
    , y `elem` xs
    ]

unfoldVar :: ProcessId -> T.Id -> String
unfoldVar p x
  = printf "sel(%s,%s,%s)" x p (qvarName p x)

foldVar :: ProcessId -> T.Id -> T.Id -> T.Id -> String
foldVar p x v x'
  = printf "upd(%s,%s,%s,%s)" x p v x'
  
tupled :: [String] -> String
tupled xs = printf "(%s)" (intercalate "," xs)


type VCPred = Pred T.Id
-- data VCState s = VC { ctr :: Int
--                     , sideConditions :: [VCPred s]
--                     , predicates :: [(String, Int)]
--                     }
-- type VCM s a = State (VCState s) a

-- freshInt :: VCM s Int
-- freshInt = do c <- gets ctr
--               modify $ \s -> s { ctr = c + 1 }
--               return c

-- freshPred :: T.Id -> VCM s T.Id
-- freshPred p = do c <- freshInt
--                  return $ (p ++ "_" ++ show c)

-- freshId :: T.Id -> VCM s T.Id
-- freshId x = do c <- freshInt
--                return $ "X_" ++ show c
-- --------------------------------------------------------------------------------
-- -- System IO
-- --------------------------------------------------------------------------------
-- runVC :: (HasType s, Show s, T.Annot s) => IceTStmt s -> IO Bool
-- runVC s = do (fp, h) <- openTempFile "." "briskseq"
--              hPutStr h hcs
--              hFlush h
--              let cmd = printf "qarmc %s" fp
--              (hOut, hIn, hErr, pid) <- runInteractiveCommand cmd
--              hClose hOut
--              putStrLn hcs
--              ec      <- waitForProcess pid
--              output  <- hGetContents hIn
--              err     <- hGetContents hErr
--              putStrLn (printf "Created file at %s." fp)
--              case ec of
--                ExitSuccess   -> do
--                  putStrLn output
--                  removeFile fp
--                  if isInfixOf "program is correct" output then
--                  -- if x == "sat" then
--                    putStrLn sat
--                  else
--                    putStrLn unsat
--                  return True
--                ExitFailure _ -> do
--                  putStrLn (printf "%s: %s" unsat err) >> return False
--                  return False
--   where hcs = vcGenQARMC $ dbgPP "a-normalized" (anormalize True s)
--         sat = "\x1b[1;32mSAT\x1b[0m"
--         unsat = "\x1b[1;31mUNSAT\x1b[0m"

-- --------------------------------------------------------------------------------
-- -- VC Generation
-- --------------------------------------------------------------------------------

-- vcGen :: T.Annot s => VCPred s -> IceTStmt s -> (VCPred s, [VCPred s])
-- vcGen φ s = (ψ, sideConditions σ)
--   where
--     (ψ, σ) = runState (wlp φ s) σ0
--     σ0     = VC { ctr            = 0
--                 , predicates     = []
--                 , sideConditions = []
--                 }
-- initState = VC { ctr            = 0
--                , predicates     = []
--                , sideConditions = []
--                }

-- vcGenQARMC :: (Show s, T.Annot s) => IceTStmt s -> String
-- vcGenQARMC s
--   = flip evalState initState $ do
--       φ  <- wlp Top (annotStmt s)
--       let clauses = toClauses (dbgPP "VC" φ)
--       ψs     <-  mapM horn clauses
--       -- is <- gets predicates
--       -- let pdecls = unlines $ pdecl <$> is
--       --     prelude = "(set-logic HORN)"
--       --     check   = "(check-sat)"
--       return (unlines ψs)
-- pdecl (p, n)
--   = printf "(declare-fun %s (%s ) Bool)" p (concat $ replicate n " Int")
--     -- sidecs  = (\p -> printf "(assert %s)" (smt p)) <$> ps
--     -- (p, ps) = vcGen Top s
-- --------------------------------------------------------------------------------
-- -- Output to QARMC horn clauses (Head :- Body)
-- --------------------------------------------------------------------------------

class QARMC a where
  qarmc :: a -> String

instance QARMC Int where
  qarmc x | x < 0     = printf "(%d)" x
          | otherwise = printf "%d" x
  
instance QARMC T.Const where
  qarmc (T.CInt x) = qarmc x
  qarmc (T.CPid p) = toUpper.xlate <$> p

instance (Eq a, Show a) => QARMC (IceTExpr a) where
  qarmc (T.EVar x _) = toUpper . xlate <$> x
  qarmc (T.EVal (Just c) _ _) = qarmc c
  qarmc (T.EVal _ (Just (v, p)) _) = qarmc p
  qarmc (T.EVal _ _ _)  = "_"
  qarmc (T.ECon c as _) = printf "%s([%s])" c (tupled (qarmc <$> as))
  qarmc (BinApp "+" _ e1 _ e2 _) = printf "%s+%s" (qarmc e1) (qarmc e2)
  qarmc (T.EAny _ _) = "_"
  qarmc e = abort "qarmc" e

varStr :: String -> String
varStr = fmap (toUpper . xlate)

xlate '$' = '_'
xlate c   = c

pattern BinApp f l1 e1 l2 e2 l3 = T.EApp (T.EApp (T.EVar f l1) e1 l2) e2 l3

qarmcTupled xs = intercalate "," (qarmc <$> xs)

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
  qarmc (PVar x xs)  = printf "%s(%s)" (toLower <$> x) (tupled (qarmc <$> xs))

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

-- horn :: (Show a, T.Annot a) => VCPred a -> VCM a String
-- horn p = unlines <$> horn' p

-- horn' (p :==>: Conj qs)
--   = concat <$> mapM horn' ((p :==>:) <$> qs)
-- horn' (p :==>: CHC xs q r)
--   = do xs' <- mapM freshId xs
--        let q' = T.substPred θ q
--            r' = T.substPred θ r
--            θ  = [ (x, T.EVar x' T.dummyAnnot) | (x,x') <- zip xs xs' ]
--        horn' $ CHC xs' (compact $ conj p q') r'
-- horn' (Conj ps)
--   = concat <$> mapM horn' ps
-- horn' chc@(CHC xs p q)
--   = return [qarmc $ CHC (toList xs') p q]
--   where
--     xs' = unions [T.fvPred p, T.fvPred q, fromList xs]
--           \\ (fromList ["+"])
-- horn' p
--   = horn' (CHC [] Top p)


-- -- quantList :: [T.Id] -> String
-- -- quantList xs = foldl' go "" xs
-- --   where
-- --     go a x = printf "%s (%s Int)" a (smt x)

----- Testing
p0 = Top

sa :: IceTStmt ()
sa =  While "l" [] $
         XUnfold "ps" "p" $ Seq [
              XAssgn "p" "y" "q" $ T.val $ \v -> v T..= T.int 4
            , XAssgn "p" "y" "q" $ T.val $ \v -> v T..= (T.EVar "y" () T..+ T.int 1)
            , XAssgn "q" "z" "p" $ T.val $ \v -> v T..= (T.EVar "y" () T..+ T.int 1)
            ]

runSA = concat (qarmcTx [] [("P", ["x","y"])] <$> (composeTxns $ evalState foo initTxState))
  where foo = do modify $ \s -> s { tsUnfolded = [("P", ["p"])]
                                  , tsVars     = [("P", ["x","y"])]
                                  }
                 tx sa

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
foo = Seq [ Assert (T.val $ \_ -> (T.int 2 T..< T.int 3) )
          ] :: IceTStmt ()
instance HasType () where
  getType () = Nothing
  setType _ _ = ()
