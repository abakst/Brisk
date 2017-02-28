{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Brisk.Model.Rewrite where

import Data.Function
import Data.List as L (reverse, nub, lookup, foldl', group, groupBy, (\\))
import Data.Char
import Data.Maybe
import Control.Monad.State
import           Brisk.Model.Types (Id)
import qualified Brisk.Model.Types as T
import Brisk.Model.IceT hiding (Store, fresh)
import Brisk.Model.Env as Env
import Brisk.Pretty
import Brisk.UX
import Text.Show.Pretty (ppShow)
import Text.PrettyPrint.HughesPJ (($$))
import qualified Debug.Trace as Dbg

dbg :: Show a => String -> a -> a
dbg m x = Dbg.trace (m ++ ": " ++ ppShow x) x

dbgPP :: Pretty a => String -> a -> a  
dbgPP m x = Dbg.trace (m ++ ": " ++ render (pp x) ++ "\n") x

type Store  s  = Env (ProcessId, Id) (IceTExpr s)
type Buffer s  = Env (T.Type Id, ProcessId, ProcessId) [IceTExpr s]
type RWTrace s = IceTStmt s
type ExtMap s  = Env ProcessId (IceTStmt s)

type RWAnnot s = (T.Annot s, Eq s, Show s)
data RWState a = RWS { ctr        :: !Int
                     , pidSets    :: ![ProcessId]
                     , external   :: ![ProcessId]
                     , exts       :: !(ExtMap a)
                     , mems       :: ![(Id, IceTExpr a)]
                     , buffers    :: !(Buffer a)
                     , consts     :: !(Store a)
                     , trace      :: !(RWTrace a)
                     , concrSends :: !(Env.Env IceTType [ProcessId])
                     , symSends   :: !(Env.Env IceTType [ProcessId])
                     }
type RWM s a = StateT (RWState s) [] a       
    
initState :: RWState s
initState = RWS { ctr        = 0
                , pidSets    = []
                , external   = []
                , exts       = empty
                , mems       = []
                , buffers    = empty
                , consts     = empty
                , trace      = Skip
                , concrSends = empty
                , symSends   = empty
                }

freshInt :: RWM s Int
freshInt = do c <- gets ctr
              modify $ \s -> s { ctr = c + 1 }
              return c

class Fresh a where
  fresh :: a -> RWM s a

instance Fresh Id where
  fresh x = do i <- freshInt
               return (x ++ "$" ++ show i)

fromIceT :: RWAnnot a
         => [IceTProcess a]
         -> RWResult (RWTrace a) [RWTrace a]
fromIceT ps
  = case rfRes of
      Nothing       -> abort "Not Race Free!" ps
      Just (m1, m2) ->
        runRWM (doRewrite (all done1) ps) initState { concrSends = m1
                                                    , symSends   = m2
                                                    , pidSets    = psets
                                                    }
  where
    psets = [ pset | ParIter _ pset _ <- ps ]
    rfRes = tySenders ps

runRWM :: RWM s (RWResult a (RWTrace s)) -> RWState s -> RWResult (RWTrace s) [RWTrace s]
runRWM rwm s0
  = fromMaybe failures success 
  where
    rewrites = runStateT rwm s0
    success  = (Result . trace) <$> listToMaybe [ s | (Result _, s) <- rewrites ]
    failures = Stuck [ t | (Stuck t, _) <- rewrites ]

enqueue :: T.Type Id -> ProcessId -> ProcessId -> IceTExpr s -> RWM s ()
enqueue t p q m
  = do buf <- flip Env.lookup (t,p,q) <$> gets buffers
       modify $ \s -> s { buffers = Env.insert (buffers s)
                                               (t,p,q)
                                               (enqueue' buf m)
                        }
  where
    enqueue' buf m = maybe [m] (++[m]) buf

dequeue :: Show s => T.Type Id -> ProcessId -> ProcessId -> RWM s (IceTExpr s)
dequeue t p q
  = do msgss <- (maybe [] return . flip Env.lookup (t,p,q) <$> gets buffers)
       (h, buf') <- lift $ do msgs <- msgss
                              dequeue' msgs
       modify $ \s -> s { buffers = Env.insert (buffers s)
                                               (t,p,q)
                                               buf'
                          }
       return h
  where
    dequeue' []    = []
    dequeue' (h:t) = [(h, t)]

bind :: (ProcessId, Id) -> IceTExpr s -> RWM s ()
bind (p,x) e
  = modify $ \s -> s { consts = Env.insert (consts s) (p,x) e }

eval :: RWAnnot s => ProcessId -> IceTExpr s -> RWM s (IceTExpr s)
eval _ e@(T.EVal _ _)
  = return e
eval p e@(T.EVar x _)
  = fromMaybe e . flip Env.lookup (p,x) <$> gets consts     
eval p (T.ECon c es l)
  = do es' <- mapM (eval p) es
       return $ T.ECon c es' l
eval p _
  = return $ T.EVal Nothing T.dummyAnnot

getPidMaybe :: RWAnnot s => ProcessId -> IceTExpr s -> RWM s ProcessId
getPidMaybe pid m
  = do m' <- eval pid m
       case m' of
         T.EVal (Just (T.CPid p)) _  -> return p
         _                           -> mzero

type PairRule s = IceTProcess s
               -> IceTProcess s      
               -> RWM s (RWResult (IceTProcess s, IceTProcess s) (RWTrace s))
data RWResult a b = Result a
                  | Stuck b
instance (Pretty a, Pretty b) => Pretty (RWResult a b) where
  ppPrec _ (Result a) = text "OK!" $$ pp a
  ppPrec _ (Stuck b)  = text "Stuck :(" $$ pp b

split1 :: IceTProcess s -> Maybe (ProcessId, IceTStmt s, IceTStmt s)
split1 (Single p s) = Just (p,s1,s2)
  where
    (s1,s2) = split1stmt s 
split1 (Unfold p _ _ s _) = Just (p,s1,s2)
  where
    (s1,s2) = split1stmt s 
split1 _                 = Nothing

split1stmt (Seq (s:s')) = (s, seqStmts s')
split1stmt s            = (s, Skip)

setStmt s (Single p _)         = Single p s
setStmt s (Unfold p' p ps _ t) = Unfold p' p ps s t

seqTrace :: RWAnnot s => RWTrace s -> RWM s ()
seqTrace t
  = modify $ \s -> s { trace = seqStmts [trace s, t] }

procPid :: IceTProcess s -> Maybe ProcessId                   
procPid (Single p _)     = Just p
procPid (Unfold p _ _ _ _) = Just p
procPid _                = Nothing

buffersUnchanged :: Buffer a -> Buffer a -> Bool
buffersUnchanged b b'
  = all good keys
  where
    keys   = nub (Env.dom b ++ Env.dom b')
    good k = case (Env.lookup b k, Env.lookup b' k) of
               (Nothing, Nothing) -> True
               (Just [], Nothing) -> True
               (Nothing, Just []) -> True
               (Just xs, Just ys) ->
                   toUnit xs == toUnit ys
                 where
                   toUnit = fmap (fmap (const ()))
               _                  -> False

extendExt :: ExtMap a -> ExtMap a -> ExtMap a
extendExt e0 e1
  = Env.foldlWithKey go e0 e1
  where
    go e p s
      = Env.insert e p $ seqStmts [Env.findWithDefault e Skip p, s]

rewriteLocal :: RWAnnot s => PairRule s
rewriteLocal a b
  | Just (p, Assgn x t e, s') <- split1 a
  = do e' <- eval p e
       bind (p,x) e'
       seqTrace (XAssgn p x p e')
       return $ Result (setStmt s' a, b)
  | Just (p, Case e cs md, s') <- split1 a
  = do e' <- eval p e
       case e' of
         T.ECon c xs _ ->
           let s = matchingCase c xs cs md in
           return $ Result (setStmt (seqStmts [s,s']) a, b)
         _             ->
           do Result ps <- rewriteAllCases a s' cs md b
              return $ Result (ps !! 0, ps !! 1)
rewriteLocal a b
  = mzero

rewriteAllCases a s [] Nothing b
  = return $ Result [setStmt s a, b]
rewriteAllCases a s [] (Just d) b
  = doRewrite (all done1) [setStmt d a, b]
rewriteAllCases a s ((T.ECon _ bs _, s'):alts) def b
  = doRewrite (isDone a) [setStmt s' a, b]
  where
    isDone (Single p _) ps = all (==Skip) [ s | Single p' s <- ps, p' == p ]

matchingCase :: RWAnnot s
             => Id
             -> [IceTExpr s]
             -> [(IceTExpr s, IceTStmt s)]
             -> Maybe (IceTStmt s)
             -> IceTStmt s 
matchingCase c xs cs md = go cs
  where
    go []
      = fromMaybe Skip md
    go ((T.ECon c' xs' _, s):cs')
      | c == c'
      = L.foldl' subst s (zip xs' xs)
      | otherwise
      = go cs'
    subst s (T.EVar x _, e) = substStmt x e s

rewriteWhileLoop :: RWAnnot s => PairRule s
rewriteWhileLoop a b
  | Just (p, While s, s') <- split1 a
  , not (done1 b)
  = do Result ps <- doRewrite (loopCont p) [setStmt s a, b]
       let b' = ps !! 1
       return $ Result (a, b')
  where
    loopCont p ps = all (check p) ps
    check p c@(Single p' s)     = check' p p' s c
    check p c@(Unfold p' _ _ s _) = check' p p' s c
    check' p p' s c
      | p == p'   = s == Continue
      | otherwise = done1 c
rewriteWhileLoop _ _
  = mzero

rewriteWhileExit :: RWAnnot s => PairRule s
rewriteWhileExit a b
  | Just (p, While s, s') <- split1 a
  = do Result ps <- doRewrite (\ps -> done1 (ps !! 0)) [setStmt s a, b]
       let (a',b') = (ps !! 0, ps !! 1)
       return $ Result (setStmt s' a', b')
rewriteWhileExit _ _
  = mzero

eraseConsts :: ProcessId -> RWM s [(Id, IceTExpr s)]
eraseConsts p
  = do cs <- gets consts  
       let cenv = Env.updateAll del cs
       modify $ \s -> s { consts = cenv }
       return [ (x',c) | ((p',x'),c) <- Env.toList cs, p == p' ]
         where
           del (p',x) v
             | p == p'   = Nothing
             | otherwise = Just v

withResult :: RWM s (RWResult a b) -> (a -> RWM s (RWResult c b)) -> RWM s (RWResult c b)
withResult act f
  = do res <- act
       case res of
         Stuck t   -> return $ Stuck t
         Result ps -> f ps


rewriteForEach :: RWAnnot s => PairRule s
rewriteForEach a b@(ParIter q qs _)
  | Just (p, ForEach x xs body, s') <- split1 a
  = do x0    <- fresh x
       buf0  <- gets buffers
       t0    <- gets trace
       exts0 <- gets exts
       mems0 <- gets mems
       -- let s0 = substStmt x (T.EVal (Just (T.CPid x0)) T.dummyAnnot) body
       bind (p,x) (T.EVal (Just (T.CPid x0)) T.dummyAnnot)
       modify $ \s -> s { mems = (x0, xs) : mems0, trace = Skip }

       withResult (doRewrite (\ps -> done1 (ps !! 0) && (unfoldProg (ps!!1))) [Single p body, b]) $
         \ps -> do
         let Unfold _ _ _ s _ = ps !! 1
         buf1  <- gets buffers
         t1    <- gets trace
         force $ buffersUnchanged buf0 buf1
         oldcs <- eraseConsts x0
         cs    <- gets consts
         let c0       = Env.addsEnv cs [ ((q,x), T.txExprPid revSub c) | (x,c) <- oldcs, x /= q ]
             revSub r l
               | r == x0   = T.EVar q l
               | otherwise = T.EVal (Just (T.CPid r)) l
         modify $ \s -> s { mems   = mems0
                          , trace  = seqStmts [t0, ForEach x xs (substStmt x0 (T.EVar x T.dummyAnnot) t1) ]
                            -- This has bugs: 1. need to replace q0 with q
                            --                2. DELETE vars that were assigned
                            --                   in the loop body
                          , consts = c0
                          -- Need to nondet and lift these
                          , exts   = exts0 `extendExt` exts s
                          }
         -- Need to update the thinger here.
         return $ Result (Single p s', ParIter q qs s) -- {(unSubstPid q0 q s))
         where
           unfoldProg (ParIter _ _ _) = False
           unfoldProg (Unfold q0 q qs s t)
             = s /= t
rewriteForEach _ _
  = mzero

rewriteForIter :: RWAnnot s => PairRule s
rewriteForIter a b@(ParIter q qs t)
  | Just (p, ForEach x xs body, s') <- split1 a
  = do x0   <- fresh x
       buf0 <- gets buffers
       t0   <- gets trace
       mems <- gets mems
       let s0 = substStmt x (T.EVar x0 T.dummyAnnot) body
       modify $ \s -> s { mems = (x0, xs) : mems, trace = Skip }
       Result _ <- doRewrite (all (pdone p)) [Single p s0, b]
       buf1  <- gets buffers
       t1    <- gets trace
       force $ buffersUnchanged buf0 buf1
       oldcs <- eraseConsts x0
       modify $ \s -> s { mems   = mems
                        , trace  = seqStmts [t0, ForEach x xs (substStmt x0 (T.EVar x T.dummyAnnot) t1) ]
                          -- This has bugs: 1. need to replace q0 with q
                          --                2. DELETE vars that were assigned
                          --                   in the loop body
                        }
       return $ Result (setStmt s' a, b)
         where
           pdone p a
             | Just p' <- procPid a, p' == p
             = done1 a
           pdone p (Unfold q0 q qs' x t)
             | qs' == qs
             = x == t
             -- = x == substStmt q (T.EVal (Just (T.CPid q0)) T.dummyAnnot) t
           done1ForEach (Single p s')
             | Just p' <- procPid a, p' == p
             = s' == Skip
           done1ForEach (Unfold q0' q' qs' t' t'')
             | qs' == qs
             = t' == substStmt q' (T.EVal (Just (T.CPid q')) T.dummyAnnot) t''
           done1ForEach _
             = False
rewriteForIter a b
  = mzero

rewriteUnfoldSend :: RWAnnot s => PairRule s
rewriteUnfoldSend a (ParIter q qs t)
  | Just (p, Send ty e_q e_m, s') <- split1 a
  = do q'  <- getPidMaybe p e_q
       qs' <- L.lookup q' <$> gets mems
       flip (maybe mzero) qs' $ \qs' -> 
         case qs' of
           T.EVal (Just (T.CPidSet qs')) _ 
             | qs' == qs -> do
               let qpid = T.EVal (Just (T.CPid q')) T.dummyAnnot
               bind (q',q) qpid
               rewriteSend a (Unfold q' q qs t t)
               -- in rewriteSend a (Unfold q' q qs (substStmt q qpid t) t)
               -- return (a, Unfold q' qs (substStmt q (T.EVar q' T.dummyAnnot) t) t)
           _ -> mzero
rewriteUnfoldSend _ _
  = mzero

rewriteFold :: RWAnnot s => PairRule s
rewriteFold (Unfold p0 p ps s t) b
  | s == t = return $ Result (ParIter p ps s, b)
rewriteFold _ _ = mzero

instantiateConsts :: ProcessId -> ProcessId -> RWM s ()
instantiateConsts q0 q
  = do c       <- gets consts
       let cxs    = [ ((q0,pidvar x), v) | ((q',x), v) <- Env.toList c, q' == q ]
           pidvar x | x == q    = q0
                    | otherwise = x
       modify $ \s -> s { consts = Env.addsEnv c cxs }
       
rewriteUnfoldRecv :: RWAnnot s => PairRule s
rewriteUnfoldRecv a (ParIter q qs t)
  | Just (p, Recv ty Nothing mx, s') <- split1 a
  = do q0      <- fresh q
       senders <- flip Env.lookup ty <$> gets symSends
       sender  <- lift $ fromMaybe [] senders
       instantiateConsts q0 q

       force (sender == qs)

       seqTrace (Assgn q0 Nothing (T.ESymElt (T.EVar qs T.dummyAnnot) T.dummyAnnot))
       let q0pid = T.EVal (Just (T.CPid q0)) T.dummyAnnot
       bind (q0,q) q0pid
       return $ Result (setStmt (seqStmts [Recv ty (Just q0pid) mx,s']) a, Unfold q0 q qs t t)
{-       ps <- doRewrite (all aProgress)
          [ setStmt (Recv ty (Just q0pid) mx) a
          , Unfold q0 q qs t t
          ]
       return (setStmt s' a, ps !! 1) -}
       -- let a' = ps !! 0
       --     b' = ps !! 1
       -- Dbg.trace "Unfold (b)" $ return ()
       -- return (setStmt Skip a, Unfold q0 qs Skip t)
         where
           aProgress a'
             | procPid a == procPid a' = done1 a'
             | otherwise               = True
rewriteUnfoldRecv _ _
  = mzero

rewriteSend :: RWAnnot s => PairRule s
rewriteSend a b 
  | Just (p, Send ty e_q e_m, s') <- split1 a
  , Just q                        <- procPid b
  = do c <- gets consts
       q' <- getPidMaybe p e_q
       forceM (notExternal q')
       if q == q' then do
         m <- eval p e_m
         enqueue ty p q m
         return $ Result (setStmt s' a, b)
       else
         mzero 
rewriteSend _ _
  = mzero

rewriteRecvFrom :: RWAnnot s => PairRule s
rewriteRecvFrom a b
  | Just (q, Recv ty Nothing mx, s') <- split1 a
  , Just p <- procPid b
  = do senders <- flip Env.lookup ty <$> gets concrSends
       sender  <- lift $ fromMaybe [] senders
       force (sender == p)
       let recv' = Recv ty (Just (T.EVal (Just (T.CPid p)) T.dummyAnnot)) mx
       rewriteRecvFrom (setStmt (seqStmts [recv',s']) a) b
rewriteRecvFrom a b
  | Just (q, Recv ty (Just e_p) mx, s') <- split1 a
  , Just p <- procPid b
  = do p' <- getPidMaybe q e_p
       if p == p' then do
         e <- dequeue ty p q
         flip (maybe (return ())) mx $ \x -> do
           bind (q,x) e
           seqTrace (XAssgn q x p e)
         return $ Result (setStmt s' a, b)
       else
         mzero
  -- "Need" a case here for receiving from a specific
  -- but not-yet-unfolded pid
rewriteRecvFrom a _
  = mzero

split :: IceTProcess s -> RWM s (IceTProcess s, IceTProcess s)
split (Single p s)
  = lift (mkProc <$> splitStmts s)
  where
    mkProc (s,t) = (Single p s, Single p t)
split (ParIter p ps s)
  = lift (mkProc <$> splitStmts s)
  where
    mkProc (s,t) = (ParIter p ps s, ParIter p ps t)
split (Unfold p0 p ps s t)
  = lift (mkProc <$> splitStmts s)
  where
    mkProc (s',s'') = (Unfold p0 p ps s' t, Unfold p0 p ps s'' t)

splitStmts :: IceTStmt a -> [(IceTStmt a, IceTStmt a)]
splitStmts (Seq stmts)
  -- = [(s, seqStmts stmts)]
  = [ seqify $ splitAt i stmts | i <- [n,n-1 .. 0] ]
  where
    seqify (s,t) = (seqStmts s, seqStmts t)
    n            = length stmts
splitStmts s
  = [(s, Skip)]

force :: Bool -> RWM s ()
force True  = return ()
force False = mzero

forceM :: RWM s Bool -> RWM s ()  
forceM act = act >>= force

notExternal :: ProcessId -> RWM s Bool  
notExternal p = not . elem p <$> gets external

{-
paste (Single p s) (Single p' t)
  | p == p' = Single p (seqStmts [s,t])
paste (ParIter p ps s) (ParIter p' ps' t)
  | p == p' && ps == ps' = ParIter p ps (seqStmts [s,t])
paste (Unfold p0 p ps s0 s) (Unfold p0' p' ps' s0' s')
  | p0 == p0' && ps == ps' = Unfold p0 p ps (seqStmts [s0, s0']) s
paste (Unfold p0 p ps s0 s) (ParIter p' ps' t)
  | ps == ps' = Unfold p0 p ps s0 (seqStmts [s,t])
paste (ParIter p' ps' t) (Unfold p0 p ps s0 s) 
  | ps == ps' = Unfold p0 p ps s0 (seqStmts [t,s])
paste x y
  = error ("paste:\n" ++ ppShow x ++ "\n" ++ ppShow y)
-}
done p q = done1 p && done1 q

done1 (Single _ Skip)        = True
done1 (Unfold _  _ _ Skip _) = True
done1 (ParIter _ _ Skip)     = True
done1 _                      = False

{-
doPairRewrite :: RWAnnot s
          => (IceTProcess s -> IceTProcess s -> Bool)
          -> IceTProcess s
          -> IceTProcess s
          -> RWM s (IceTProcess s, IceTProcess s)
doPairRewrite = runRules (rules ++ map flipRule rules)
-}

doRewrite :: RWAnnot s
          => ([IceTProcess s] -> Bool)
          -> [IceTProcess s]
          -> RWM s (RWResult [IceTProcess s] (RWTrace s))
doRewrite stop ps
  = go $ Env.fromList (zip [0..] ps)
  where
    n     = length ps
    procs = (snd <$>) . Env.toList
    pairs = [ (i,j) | i <- [0..n-1], j <- [0..n-1], i /= j ]
    go m
      | stop (procs m)
      = return $ Result (procs m)
    go m = do (i, j) <- lift pairs
              let p = fromJust $ Env.lookup m i
                  q = fromJust $ Env.lookup m j
              r                <- lift allrules
              result           <- r p q
              case result of
                Stuck t        -> return (Stuck t)
                Result (p',q') -> do
                 force (p /= p' || q /= q')
                 go $ Env.addsEnv m [(i,p'),(j,q')] 
  
allrules :: RWAnnot s => [PairRule s]
allrules = rules ++ map flipRule rules

rules :: RWAnnot s => [PairRule s]
rules = [ rewriteLocal
        , rewriteUnfoldRecv
        , rewriteSend
        , rewriteRecvFrom
        , rewriteForIter
        , rewriteForEach
        , rewriteUnfoldSend
        , rewriteWhileExit
        , rewriteWhileLoop
        -- This needs to be last!
        , rewriteStuck
        ]

rewriteStuck :: RWAnnot s => PairRule s
rewriteStuck _ _ = do t <- gets trace
                      return $ Stuck t

flipRule r p q = do res <- r q p
                    case res of
                      Result (q', p') -> return $ Result (p', q')
                      Stuck t         -> return $ Stuck t

tySenders :: [IceTProcess a] -> Maybe (Env.Env IceTType [ProcessId], Env.Env IceTType [ProcessId])
tySenders ps
  | all (rf concrSend symSend) [ (p, s)  | Single p s <- ps ] &&
    all (rf concrSend symSend) [ (ps, s) | ParIter _ ps s <- ps ]
  = Just (concrSend, symSend)
  | otherwise
  = Nothing
  where
    -- -- For each type: who recvs it?
    -- concrRecv = tyMap [ (t, p) | (p, (_,ts)) <- concrs, t <- ts ]
    -- symRecv   = tyMap [ (t, p) | (p, (_,ts)) <- syms, t <- ts ]
    -- For each type: who sends it?
    concrSend = tyMap [ (t, p) | (p, ts) <- concrs, t <- ts ]
    symSend   = tyMap [ (t, p) | (p, ts) <- syms,   t <- ts ]
    -- For each process, which types are sent/received?
    concrs  = [ (p, msgSends s) | Single p s <- ps    ]
    syms    = [ (p, msgSends s) | ParIter _ p s <- ps ]

    tyMap l = Env.addsEnv Env.empty
              [ (fst . head $ grp, nub (snd <$> grp)) | grp <- groupBy ((==) `on` fst) l ]

rf :: Env.Env IceTType [ProcessId] -> Env.Env IceTType [ProcessId] -> (ProcessId, IceTStmt a) -> Bool
rf concrs syms (p,s)
  = queryMsgTys const check True s
  where
    check False _ = False
    check _     t = length (lookupConcr t) + length (lookupSym t) <= 1

    lookupConcr t = maybe [] (\ps -> group (ps L.\\ [p])) $ Env.lookup concrs t
    lookupSym t   = maybe [] (\ps -> ps L.\\ [p]) $ Env.lookup syms t

msgSends:: IceTStmt a -> [IceTType]
msgSends s = sends
  where
    send1 snds t = t:snds
    recv1 snds t = snds
    sends        = queryMsgTys send1 recv1 [] s


pingLoop = Single "A" $ Seq [
  ForEach "p" (T.EVar "P_Set" ()) $
    Send (T.TyVar "T0") (T.EVar "p" ()) (T.EVal (Just (T.CInt 0)) ())
  ,
  ForEach "p" (T.EVar "P_Set" ()) $
    Send (T.TyVar "T0") (T.EVar "p" ()) (T.EVal (Just (T.CInt 0)) ())
  ]
pongLoop = ParIter "P" "P_Set" $
              Seq [ Recv (T.TyVar "T0") (Just (T.EVar "A" ())) (Just "zzz")
                  , Recv (T.TyVar "T0") (Just (T.EVar "A" ())) (Just "zzz")
                  ]

body0 = Seq [ Recv (T.TyVar "a") Nothing (Just "z")
            , Send (T.TyVar "b") (T.EVar "z" ()) (T.EVal (Just (T.CInt 0)) ())
            ]

loop0 b = Single "A" $
          ForEach "x" (T.EVar "xs" ()) b

sym0 = ParIter "P" "P_Set" $ Seq [
  Send (T.TyVar "a") (T.EVar "A" ()) (T.EVar "P" ())
   -- , Recv (T.TyVar "b") (Just (T.EVar "A" ())) (Just "w")
  ]
sym1 = ParIter "P" "P_Set" $ Seq [
     Send (T.TyVar "a") (T.EVar "A" ()) (T.EVar "P" ())
   , Recv (T.TyVar "b") (Just (T.EVar "A" ())) (Just "w")
  ]

p0  = Single "A" (Send (T.TyVar "a") (T.EVal (Just (T.CPid "B")) ()) (T.EVal (Just (T.CInt 0)) ()))
p1  = Single "B" (Skip)
p2  = Single "B" (Recv (T.TyVar "a") (Just (T.EVal (Just (T.CPid "A")) ())) (Just "x"))
p2' = Single "B" (Recv (T.TyVar "b") (Just (T.EVar "A" ())) (Just "x"))

ps = Single "A"
      $ seqStmts [ Send (T.TyVar "a") (T.EVar "B" ()) (T.EVar "m" ())
                 , Send (T.TyVar "b") (T.EVar "B" ()) (T.EVar "n" ())
                 ]
ps' = Single "A"
      $ seqStmts [ Send (T.TyVar "a") (T.EVar "B" ()) (T.EVar "m" ())
                 ]
      
qs = Single "B"
      $ seqStmts [ Recv (T.TyVar "a") (Just (T.EVar "A" ())) (Just "x")
                 , Recv (T.TyVar "b") (Just (T.EVar "A" ())) (Just "y")
                 ]

rs = Single "B"
      $ seqStmts [ Recv (T.TyVar "a") (Just (T.EVar "A" ())) (Just "x")
                 , Recv (T.TyVar "b") (Just (T.EVar "A" ())) (Just "y")
                 ]

c0 = Single "A" $ Seq [ Recv (T.TyVar "a") (Just (T.EVar "P$1" ())) (Just "z")
                      , Send (T.TyVar "b") (T.EVar "z" ()) (T.EVal (Just (T.CInt 0)) ())
                      ]
c1 = Single "P$1" $ Send (T.TyVar "a") (T.EVar "A" ()) (T.EVar "P$1" ())
