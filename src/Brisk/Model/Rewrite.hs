{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Brisk.Model.Rewrite where

import Data.Function
import Data.List as L
import Data.Char
import Data.Maybe
import Control.Monad.State
import Control.Monad.Logic
import           Brisk.Model.Types (Id)
import qualified Brisk.Model.Types as T
import           Brisk.Model.RewriteTypes
import Brisk.Model.IceT hiding (Store, fresh)
import Brisk.Model.Env as Env
import Brisk.Pretty
import Brisk.UX
import Text.Show.Pretty (ppShow)
import Text.PrettyPrint.HughesPJ as PP (($$), (<+>), (<>), vcat, hcat, parens)
import qualified Debug.Trace as Dbg

--------------------------------------------------------------------------------
-- Context Manipulation
--------------------------------------------------------------------------------
splitContext :: RWAnnot s => RewriteContext s -> [(RewriteContext s, RewriteContext s)]
splitContext (One p True (Seq s))
  = [ (One p True (seqStmts (take i s)), One p True (seqStmts (drop i s)))
    | i <- [length s,length s - 1..1]
    ]
splitContext (One p sp s)
  = [ (One p sp s, One p sp Skip) ]
splitContext (Par xs bag s)
  = do (pre, post) <- splitContext s
       return (Par xs bag pre, Par xs bag post)
splitContext (Sum xs bag s)
  = do (pre, post) <- splitContext s
       return (Sum xs bag pre, Sum xs bag post)
splitContext (Ast s)
  = do (pre, post) <- splitContext s
       return (Ast pre, Ast post)

splitContext (FinPar [c])
  = do (pre, post) <- splitContext c
       return (FinPar [pre], FinPar [post])
splitContext (FinPar (c:cs))
  = do (c_pre, c_post)           <- splitContext c
       (FinPar pre, FinPar post) <- splitContext (FinPar cs)
       return (FinPar (c_pre : pre), FinPar (c_post : post))

splitContext (Sequence _ [])
  = []
splitContext (Sequence split (c:cs))
  | (Par p ps (One (Concrete _) _ _)) <- c
  = [(c, Sequence split cs)]
  | otherwise
  = do (pre, post) <- splitContext c
       (pre, Sequence split (post:cs)):[ (Sequence split [c, pre'], post')
                                       | (pre', post') <- splitContext (Sequence split cs)
                                       ]
splitContext c
  = abort "splitContext" c

dbg :: Show a => String -> a -> a
dbg m x = Dbg.trace (m ++ ": " ++ ppShow x) x

dbgPP :: Pretty a => String -> a -> a
dbgPP m x = Dbg.trace (m ++ ": " ++ render (pp x) ++ "\n") x

-- collectStmts :: ProcessIdSpec -> IceTStmt s -> RewriteContext s
-- collectStmts p = go
--   where
--     go (ForEach x (_, T.EVar{T.varId = xs}) s)
--       = Par [x] (Singleton xs) (One p False s)
--     go (While x s)
--       = Ast (One p False s)
--     go s
--       = One p True s

runAssign :: RWAnnot s => RewriteContext s -> RWM s (RewriteContext s)
runAssign (One p split (Assgn x t rhs@(T.ECase t' e alts Nothing l)))
  -- Here we can see if we're removing a join
  = do e' <- eval p e
       case e' of
         -- OMG THIS CODE IS SO GROSS FIX ME PLEASE
         T.EUnion es -> do
           es' <- dbgPP "es!!" <$> mapM (\e -> eval p (dbgPP "new expr" $ T.ECase t' e alts Nothing l)) es
           case L.nub es' of
             [e] -> do
               modify $ \st -> st { consts = Env.addsEnv (consts st) [((p,x), e)] }
               return $ dbgPP "aha!" (One p split Skip)
             _   -> return (One p split Skip)
         _ -> eval p rhs >>= \e -> do modify $ \st -> st { consts =  Env.addsEnv (consts st) [((p,x), e)] }
                                      return (One p split Skip)
  -- where
  --   s'    = Case e alts' Nothing
  --   alts' = [(T.ECon c (flip T.EVar T.dummyAnnot <$> xs) T.dummyAnnot,
  --             Assgn x t e) | (c,xs,e) <- alts ]
runAssign (One p sp (Assgn x _ e))
  = do eVal <- eval p e
       modify $ \st -> st { consts = Env.addsEnv (consts st) [dbgPP "newAdd" ((p,x), eVal)] }
       seqTrace (XAssgn (specPid p) x (specPid p) e)
       return (One p sp Skip)
runAssign _
  = mzero

runSimplifyCase (One p sp (Case e alts md))
  = do eVal    <- eval p e
       (env,s) <- ofList alts >>= unifies p eVal
       modify $ \st -> st { consts = Env.addsEnv (consts st) env }
       return (One p sp s)
    --    undefined
    -- runMatch p ps (env, s)
    --   = do modify $ \st -> st { consts = Env.addsEnv (consts st) env }
    --        c <- gets consts
    --        return (One p s : ps)
runSimplifyCase (Par x xs c@(One p@(Unfolded u us) sp s))
  = do env0    <- gets consts
       let env1 = instantiateConsts env0 p
       modify $ \st -> st { consts = env1 }
       c'      <- runSimplifyCase (One p sp s)
       env1    <- gets consts
       let env2 = generalizeConsts env1 p
       modify $ \st -> st { consts = env2 }
       return $ Par x xs c'
      -- Par x xs $ runSimplifyCase c

       -- eVal                           <- eval p e
       -- ifte (ofList alts >>= unifies p eVal)
runSimplifyCase _
  = mzero

pullUpMatch :: RWAnnot s
            => RewriteContext s
            -> RWM s (RewriteContext s)
pullUpMatch (One p sp (Seq ((Case e alts md):ss)))
  | not (isContinue (head ss))
  = return $ One p sp (seqStmts (case' : s1))
  where
    case'    = Case e [ (p, seqStmts (s:s0)) | (p,s) <- alts ]
                      ((seqStmts . (:s0)) <$> md)
    (s0, s1) = (takeWhile (not . isContinue) ss, dropWhile (not . isContinue) ss)
pullUpMatch _
  = mzero

isContinue (Continue _) = True
isContinue _            = False

runAssert :: RWAnnot s
          => RewriteContext s
          -> RWM s (RewriteContext s)
runAssert (One p sp (Assert q))
  = do seqTrace (Assert q)
       return (One p sp Skip)
runAssert (One p sp (Assume q))
  = do seqTrace (Assume q)
       return (One p sp Skip)
runAssert _
  = mzero

runSend :: RWAnnot s
        => RewriteContext s
        -> RWM s (RewriteContext s)
runSend (One p sp (Send t q m))
  = do c    <- gets consts
       qPid <- getPidMaybe p q

       mv   <- eval p m
       enqueue t pPid qPid mv

       return $ One p sp Skip
         where
           pPid = specPid p
runSend _
  = mzero

runRecvFrom :: RWAnnot s
            => RewriteContext s
            -> RWM s (RewriteContext s)
runRecvFrom (One q sp (Recv t (Just p) mx))
  = do pPid <- getPidMaybe q p
       buf  <- gets buffers
       msg  <- dequeue t pPid qPid

       maybeM mx $ \x -> do
        bind (q, x) msg
        seqTrace (XAssgn qPid x pPid msg)

       return (One q sp Skip)
         where
           qPid = specPid q
runRecvFrom (One q sp (Recv t Nothing mx))
  = do senders <- gets concrSends
       p       <- ofList (fromMaybe [] $ Env.lookup senders t)
       runRecvFrom (One q sp (Recv t (Just (pidLit p)) mx))
runRecvFrom _
  = mzero

runCollect :: RWAnnot s
           => RewriteContext s
           -> RWM s (RewriteContext s)
runCollect c
  = do Just c' <- collectContext c
       return c'

splitCase (One p sp s@(Case _ _ _))
  = return (One p sp s, Skip)
splitCase (One p sp (Seq (s0@(Case _ _ _):ss)))
  = return (One p sp s0, seqStmts ss)
splitCase _
  = mzero

doCaseStmt :: RWAnnot s
           => [RewriteContext s]
           -> RWM s [RewriteContext s]
doCaseStmt cs
  = do ([c], ps)                          <- ofList $ partitions cs
       (One p sp (Case e alts md), rest)  <- splitCase c
       eVal                               <- eval p e
       ifte (ofList alts >>= unifies p eVal)
            (runMatch p sp rest ps) $ do
              (ps', ps'') <- ofList $ partitions ps
              (pre, post) <- ofList $ choosePrefixes ps'
              dbgPP "Rewrite Case" (One p sp (Case e alts md) : pre) `seq`
                rewriteAll (\s -> One p sp s : pre) e alts md
              return $ dbgPP "caseStmt Done" ([One p sp rest] ++ post ++ ps'')
  where
    -- Just reduce the case statement to the single matching branch
    runMatch :: ProcessIdSpec
             -> Bool
             -> IceTStmt s
             -> [RewriteContext s]
             -> ([((ProcessIdSpec, Id), IceTExpr s)], IceTStmt s)
             -> RWM s [RewriteContext s]
    runMatch p sp rest ps (env, s)
      = do modify $ \st -> st { consts = Env.addsEnv (consts st) env }
           c <- gets consts
           return (One p sp (seqStmts ([s, rest])) : ps)

    -- Need to rewrite *each* branch now...
    rewriteAll f e alts Nothing
      = do t0          <- gets trace
           b0          <- gets buffers
           env0        <- gets consts
           (env, ts)   <- foldM (rewriteAlt b0 f env0) ([], []) alts
           -- Also do default
           modify $ \st -> st { trace = seqStmts [
                                    t0
                                  , Case e ts Nothing
                                  ]
                              , consts = joinEnvs env
                              }
           return []

    rewriteAlt b f e0 (es, ts) (c, s)
      = do modify $ \st -> st { trace  = Skip
                              , consts = e0
                              }

           runRewrites null (dbgPP "rewrite ==>" $ concatMap filterSkips $ f s)
           b' <- gets buffers
           cond $ buffersUnchanged b b'
           t' <- gets trace
           e  <- dbg "rewrote!" () `seq` gets consts
           return ((e:es, (c,t') : ts))

unifies p e1@(T.ECon c xs l) (e2@(T.ECon c' xs' l'), s)
  | c == c' && length xs == length xs'
  = return $ (patternEnv p xs xs', s)
  where
    patternEnv p es1 es2
      = [((p, x), e) | e <- es1 | T.EVar x _ <- es2]
unifies _ _ _
  = mzero
-- unifies p e1 e2
--   = abort "unifies" (p, e1, e2)

doWhileContExit :: RWAnnot s
                => [RewriteContext s]
                -> RWM s [RewriteContext s]
doWhileContExit cs
  = do ([One p sp (While l xs s)], ps) <- ofList $ partitions cs
       let p' = One p sp s
       ps'                             <- runRewrites (all (finished p l)) (p' : ps)
       return $ dbgPP "doWhileContExit" $ fmap (fixup p l xs s) ps'
  where
    fixup pid l xs s (One p sp (Continue l'))
     | l == l' = One p sp (While l xs s)
    fixup pid _ _ _ c = c

    finished pid l (One p _ (Continue l'))  = p /= pid || l == l'
    finished pid l (One p _ s)              = p /= pid || s == Skip
    finished _ _ _                          = True

doReactiveWhile :: RWAnnot s
                => [RewriteContext s]
                -> RWM s [RewriteContext s]
doReactiveWhile cs
  = do css <- collectSome cs
       let (while, notwhile) = L.partition isAst css
       cond $ while /= []

       t0 <- gets trace
       modify $ \st -> st { trace = Skip }
       runRewrites (all continue) [c | Ast c <- while]
       modify $ \st -> st { trace = seqStmts [ t0, While "*" [] (trace st) ] }

       return notwhile
  where
    continue (One _ _ (Continue l)) = True
    continue (Par _ _ c)            = continue c
    continue (Sum _ _ c)            = continue c
    continue (FinPar cs)            = all continue cs
    continue _                     = False
    isAst (Ast _)                  = True
    isAst _                        = False
  -- = do (Ast s, rest) <- ofList css
  --      cond $ rest /= []
  --      runRewrites (finished cs) $ (s : rest)
  -- where
  --   isContinue (One _ _ (Continue _)) = True
  --   isContinue _ = False
  --   finished ps ps' = all isContinue ps' && length ps == length ps'
  --   -- finished [One _ _ (Continue _)] = True
  --   -- finished _ = False
  --   css = [ (c, rest) | ([c@(Ast _)], rest) <- partitions cs ]

--------------------------------------------------------------------------------
ofList :: MonadPlus m => [a] -> m a
--------------------------------------------------------------------------------
ofList = msum . map return

--------------------------------------------------------------------------------
symSenders :: RWAnnot s => IceTType -> RWM s ProcessId
--------------------------------------------------------------------------------
symSenders t
  = do senders <- gets symSends
       ofList . fromMaybe [] $ Env.lookup senders t

--------------------------------------------------------------------------------
-- Computing Instantiations for induction
--------------------------------------------------------------------------------
data Instance = Maybe Id :?-->: Id | Maybe Id :!-->: Id
                deriving (Eq, Show)


-- --------------------------------------------------------------------------------
-- bubbleUpInstStmt :: RWAnnot s
--                     => [Id]
--                     -> IceTStmt s
--                     -> RWM s (IceTStmt s, [Instance])
-- --------------------------------------------------------------------------------
-- bubbleUpInstStmt sets r@(Recv t Nothing mx)
--   = do sender <- symSenders t
--        if sender `elem` sets then
--          do p <- fresh sender
--             let inst = [sender :?-->: p]
--                 r'   = Recv t (Just (T.EVal (Just $ T.CPid p) T.dummyAnnot)) mx
--             return (r', inst)
--        else
--          return (r, [])

-- bubbleUpInstStmt sets (Seq ss)
--   = do (ss', inst) <- foldM go ([], []) $ reverse ss
--        return $ (Seq ss', inst)
--   where
--     go (stmts, inst) s = do (s', i) <- bubbleUpInstStmt sets s
--                             return $ (s' : stmts, i ++ inst)

-- bubbleUpInstStmt sets s
--   = return (s, [])

-- This shold only be called on a list of Ones
findProcess :: [Id]
            -> [RewriteContext s]
            -> Maybe ((ProcessIdSpec,Bool), IceTStmt s, [(Id, (ProcessIdSpec,Bool), IceTStmt s)])
findProcess xs ps
  = case procs of
      [(x,(p,sp),s)] -> Just ((p, sp), s, notprocs)
      _              -> Nothing
  where
    procs    = [ (x, (p, sp), s) | (x, One p sp s) <- zip xs ps, specPid p == x ]
    notprocs = [ (x, (p, sp), s) | (x, One p sp s) <- zip xs ps, specPid p /= x ]

walkStmtInsts :: RWAnnot s
              => [Id]
              -> ProcessIdSpec
              -> Maybe Id
              -> (ProcessIdSpec, IceTStmt s)
              -> RWM s ([Instance], IceTStmt s)
walkStmtInsts sets p0 myP (me, s) = go [] s
  where
    go :: RWAnnot s => [Instance] -> IceTStmt s -> RWM s ([Instance], IceTStmt s)
    go is s@(Send t (T.EVar p l) m)
      | Just myP' <- myP
      , p == myP' = return ( Just myP' :!-->: specPid p0 : is
                           , substStmt myP' (T.EVal (Just (T.CPid $ specPid p0)) Nothing l) s
                           ) -- Sending to "the proc"
    go is s@(Send t x@(T.EVar xid _) m)
      = do c0 <- gets consts
           let try = do (T.ESymElt (T.EVal (Just (T.CPidSet xs)) _  _) l) <- eval me x
                        if xs `elem` sets then
                          return ( Just xid :!-->: specPid p0 : is
                                 , Send t (T.EVal (Just (T.CPid $ specPid p0)) Nothing l) m
                                 )
                        else
                         return (is, s)
           try `mplus` return (is, s)
    go is s@(Recv t Nothing mx)
      = do sender <- symSenders t
           if sender `elem` sets then
             return ( myP :?-->: specPid p0 : is
                    , Recv t (Just (T.EVal (Just (T.CPid $ specPid p0)) Nothing T.dummyAnnot)) mx
                    )
           else
             return (is, s)
    go is (Seq ss)
      = do (i, ss') <- foldM goFold (is, []) $ reverse ss
           return (i, Seq ss')
    go is s
      = return (is, s)

    goFold (is, ss) s = do (is', s') <- go is s
                           return (is', s':ss)

freshInst :: RWAnnot s
          => RewriteContext s
          -> RWM s (Maybe ProcessIdSpec, [RewriteContext s])
freshInst p@(Par xs@(x:xs0) (Zipped n s) (FinPar ps))
  | length xs == n && length ps == n
  , Just ((p0,p0sp), s0, rest) <- findProcess xs ps
  = do p1    <- fresh $ dbgPP "p0" p0
       let p1pid = specPid p1
           p1Lit = pidLit p1pid
       rest' <- forM rest $ \(x,(p,sp),s) ->
                  do -- This is not QUITE right, need to freshen x
                     -- in case it appears in some other expression,
                     -- but let's do that later...
                     (is, s') <- walkStmtInsts sets p1 (Just x) (p, s)
                     if toUnify is
                       then return (One p sp $ substStmt x p1Lit s')
                       else return (One p sp s)
       return $ (Just p1, One p1 p0sp (substStmt (specPid p0) p1Lit s0) : rest')

  | length xs == n && length ps == n
  = do xs' <- mapM fresh xs
       cs <- forM (zip (zip xs xs') ps) $ \((x,x'), One p sp s) -> do
             (_, s') <- walkStmtInsts sets p Nothing (p, s)
             return (One p sp $ substStmt x (T.EVar x' T.dummyAnnot) s')
       return (Nothing, cs)

  | otherwise
  = mzero
  where
    sets                 = collectSets s

    toUnify []           = False
    toUnify [_ :?-->: _] = True
    toUnify ls           = all isSend ls
    isSend (_ :!-->: _)  = True
    isSend _             = False

collectAndMerge :: RWAnnot s => [RewriteContext s] -> [[RewriteContext s]]
collectAndMerge cs
  = groupBy samePar $ L.sort cs
  where
    samePar (Par _ x _) (Par _ y _) = x == y
    samePar (Sequence _ (c:cs)) d     = samePar c d
    samePar d (Sequence _ (c:cs))     = samePar c d
    samePar _           _           = False

partitionUntilLoop (One p sp s)
  = (One p sp pre, One p sp post)
  where
    (pre, post) = partitionStmtUntilLoop s
partitionUntilLoop (Par p b s)
  = (Par p b pre, Par p b post)
  where
    (pre, post) = partitionUntilLoop s
partitionUntilLoop c
  = abort "AWFWEFA" c

partitionStmtUntilLoop (Seq ss)
  = (seqStmts $ takeWhile notLoop ss, seqStmts $ dropWhile notLoop ss)
  where
    notLoop (ForEach _ _ _) = False
    notLoop (While _ _ _)   = False
    notLoop s               = True
partitionStmtUntilLoop s
  = (s, Skip)

collectSomeForeverLoops :: RWAnnot s => [RewriteContext s] -> RWM s [RewriteContext s]
collectSomeForeverLoops cs
  = do sets <- gets pidSets
       mapM (go (dbgPP "sets" sets)) cs
  where
    go sets c@(One p sp (While l xs s))
     | whileReactive l s
     = ofList ([ Sequence True [Par ["_"] (Singleton set) (One p sp (dropCont l s)), c]| set <- sets ] ++ [ c ])
    go sets c
     = return c

    dropCont l (Seq ss) = seqStmts (take (length ss - 1) ss ++ [dropCont l (last ss)])
    dropCont l (Case e alts d) = Case e (fmap (dropCont l <$>) alts) (dropCont l <$> d)
    dropCont l (Continue l') | l == l' = Skip
    dropCont _ s = s


doInduction :: RWAnnot s
            => [RewriteContext s]
            -> RWM s [RewriteContext s]
doInduction ps
  = do gets induct >>= cond . not
       (ps0, ps00)                     <- ofList $ partitions ps
       ps1                             <- collectSomeForeverLoops ps0
       (pre, post)                     <- ofList $ choosePrefixes ps1
       let ps'                          = collectAndMerge pre
       (toSkipPre, [], toSame)         <- ofList $ chooseInduction $ ps'
       consts0                         <- gets consts

       -- let consts1 = instantiateConsts consts0

       (p0, toSkipPre')                <- instantiate toSkipPre

       -- Instantiate quantified constants of instantiated process
       -- (Assuming one for now)
       let consts1       = maybe consts0 (instantiateConsts consts0) p0

       b0 <- gets buffers
       t0 <- gets trace
       modify $ \s -> s { consts = consts1
                        , trace  = Skip
                        , induct = True
                        }
       dbgPP "doInduction" (toSkipPre' , toSame) `seq`
         runRewrites ((== toSame)) (toSkipPre' ++ toSame)
       b1 <- gets buffers
       t1 <- gets trace

       cond $ buffersUnchanged b0 b1
       consts2          <- gets consts
       let consts3       = maybe consts2 (generalizeConsts consts2) p0
       modify $ \s -> s { consts = consts3
                        , trace  = seqStmts [t0, iterateTrace toSkipPre t1]
                        , induct = False
                        }

       -- return $ ({- toSkipPost ++ -} toSame)
       return $ dbgPP "OUT" (ps00 ++ {- toSkipPost ++ -} toSame `stitchContexts` post)
  where
    iterateTrace (Par xs bag _) t
      = ForEach ("(" ++ intercalate "," xs ++ ")")
                (False, bagIds bag)
                t

    instantiate :: RWAnnot s
                => RewriteContext s
                -> RWM s (Maybe ProcessIdSpec, [RewriteContext s])
    instantiate p@(Par xs bag (FinPar ps))
      = freshInst p
    instantiate (Par xs bag (One p sp ps))
      = return (Nothing, [One p sp ps])
    instantiate p
      = mzero

doInstantiateSum :: RWAnnot s
                 => [RewriteContext s]
                 -> RWM s [RewriteContext s]
doInstantiateSum ps
  = do (p@(Sum _ _ _), p0, rest) <- chooseCaseSplit ps
       (p0pid@(Unfolded x xs), rest') <- do
         p0pid <- contextPid p0
         rest' <- freshInstOther p0pid rest
         return (p0pid, rest')
       seqTrace (Assgn x Nothing (T.ESymElt (T.EVar xs T.dummyAnnot) T.dummyAnnot))
       return (p0 : rest')


doCaseSplit :: RWAnnot s
            => [RewriteContext s]
            -> RWM s [RewriteContext s]
doCaseSplit ps
  = do -- let ps' = concat $ collectAndMerge ps
       (p@(Par _ _ _), p0, rest)  <- chooseCaseSplit ps
       (p0pid@(Unfolded x xs), rest') <- do
         p0pid <- contextPid p0
         rest' <- freshInstOther p0pid rest
         return (p0pid, rest')
       seqTrace (Assgn x Nothing (T.ESymElt (T.EVar xs T.dummyAnnot) T.dummyAnnot))
       runRewrites ((== 1) . length) (p0 : rest')
       return [p]
       -- consts0     <- gets consts
       -- let consts1  = maybe consts0 (instantiateConsts consts0) $ contextPid p
       -- undefined

freshInstOther spec@(Unfolded p ps) qs
  = do (is, qs') <- foldM go ([], []) qs -- go (walkStmtsInst [ps] p Nothing <$> qs)
       if toInst is then return qs' else mzero
  where
    toInst []           = True
    toInst is           = distinct $ [p | p :?-->: _ <- is] ++
                                     [p | p :!-->: _ <- is]
                       {- && allRecvs is -}
    distinct []         = True
    distinct (x:xs)     = x `notElem` xs && distinct xs
    -- Why did I have this?
    -- allRecvs            = all isRecv
    -- isRecv (_ :?-->: _) = True
    -- isRecv _            = False

    go (is, qs) (One q sp s)
      = do (i, s') <- walkStmtInsts [ps] spec (Just (specPid q)) (q, s)
           return (i ++ is, One q sp s':qs)
    go _ _
      = mzero
freshInstOther _ _
  = mzero
    -- go (One p s)
    --   = do (i, s') <- walkStmtInsts [ps] p Nothing s
    --        undefined


generalizeConsts :: RWAnnot s => Store s -> ProcessIdSpec -> Store s
generalizeConsts c p@(Unfolded p0 ps)
  = Env.fromList newBinds `Env.unionEnvs` Env.fromList filterBinds
  where
    newBinds = [ ((Forall ps, x), v)
               | ((Unfolded p0' ps', x), v) <- Env.toList c
               ,  p0 == p0' && ps == ps'
               ]
    filterBinds = [ ((p', x), v)
                  | ((p', x), v) <- Env.toList c
                  , p' /= p
                  ]
generalizeConsts c _
  = c

instantiateConsts c (Unfolded p0 ps)
  = Env.addsEnv c myConsts
  where
    myConsts = [ ((Unfolded p0 ps, x), v)
               | ((Forall ps',x), v) <- Env.toList c, ps == ps'
               ]
instantiateConsts c _
  = c

chooseCaseSplit :: RWAnnot s
                => [RewriteContext s]
                -> RWM s (RewriteContext s, RewriteContext s, [RewriteContext s])
chooseCaseSplit ps
  -- = do (p, s, rest) <- ofList [ (Par ps bag s, s, ps') | ([Par ps bag s], ps') <- partitions ps ]
  --      case s of
  --        (Unfolded
  = do ([c]{-[Par ps bag (One p sp s)]-}, ps') <- ofList $ partitions ps
       case c of
         Par ps bag (One p sp s) ->
           case p of
             Unfolded x xs -> do
               x0 <- fresh x
               return  (Par ps bag (One p sp s)
                       ,One (Unfolded x0 xs) sp (substStmt x (pidLit x0) s)
                       ,ps')
             _ -> mzero
         Sum ps bag (One p sp s) ->
           case p of
             Unfolded x xs -> do
               x0 <- fresh x
               return ( Sum ps bag (One p sp s)
                      , One (Unfolded x0 xs) sp (substStmt x (pidLit x0) s)
                      , ps'
                      )
         _ -> mzero

chooseInduction :: [[RewriteContext s]]
                -> [(RewriteContext s, [RewriteContext s], [RewriteContext s])]
chooseInduction []
  = []
chooseInduction (c:cs)
  = let me = maybe [] (\m -> [(m, catMaybes posts, concat cs)]) merged in
    me ++ [ (m,p,c ++ cs') | (m,p,cs') <- chooseInduction cs ]
  where
    merged = maybeMerge pres
    maybeMerge :: [RewriteContext s] -> Maybe (RewriteContext s)
    maybeMerge (m:ms) = foldl' (\mc -> (mc >>=). mergeContexts) (Just m) ms
    (pres, posts)                = unzip (split <$> c)
    split c@(Par x y s)          = (c, Nothing)
    split c@(Sum x y s)          = (c, Nothing)
    split c@(Ast s)              = (c, Nothing)
    split c@(One b _ s)          = (c, Nothing)
    split c@(Sequence _ [c0])    = (c0, Nothing)
    split c@(Sequence True ([c0,cs]))  = (c0, Just cs)
    split c@(Sequence True (c0:cs))  = (c0, Just (Sequence True cs))
    split c@(Sequence False (c0:cs)) = (c, Nothing)

alwaysRules :: RWAnnot s => [RewriteContext s -> RWM s (RewriteContext s)]
alwaysRules = [ pullUpMatch
              , applyToOneRule runAssign
              , applyToOneRule runSend
              , applyToOneRule runAssert
              , applyToOneRule runRecvFrom
              , applyToOneRule runSimplifyCase
              , runCollect
              ]
rules :: RWAnnot s => [[RewriteContext s] -> RWM s [RewriteContext s]]
rules = [ doReactiveWhile
        , doCaseStmt
        , doCaseSplit
        , doInstantiateSum
        , doInduction
        , doWhileContExit
        ]

cond b | b         = return ()
       | otherwise = mzero


applyToOneRule :: RWAnnot s
           => (RewriteContext s -> RWM s (RewriteContext s))
           -> RewriteContext s
           -> RWM s (RewriteContext s)
applyToOneRule r c
  = do (_, c') <- applyToOne r' c
       return c'
         where
           r' c = do c' <- r c
                     return ((), c')

applyToOne :: RWAnnot s
           => (RewriteContext s -> RWM s (a, RewriteContext s))
           -> RewriteContext s
           -> RWM s (a, RewriteContext s)
applyToOne rule (One p sp (Seq (s:ss)))
  = do (info, One p sp' Skip) <- rule (One p sp s)
       return (info, One p sp' (seqStmts ss))
applyToOne rule c
  = rule c

findRewrite :: RWAnnot s
            => RWM s a
            -> RWState s
            -> (a, RWState s)
findRewrite query st
  = observe (runStateT query st)
  -- = evalState (observeT query) st

runRewrites :: RWAnnot s
            => ([RewriteContext s] -> Bool)
            -> [RewriteContext s]
            -> RWM s [RewriteContext s]
runRewrites done ps
  | done ps
  = return ps
runRewrites done ps
  = do ps' <- once $ (runRewriteSingle done ps `mplus` runRewritesGroup done ps)
       runRewrites done (concatMap filterSkips ps')
  -- = do ifte (runRewriteSingle done ps)
  --           (\ps' -> do
  --              let psFilter = concatMap filterSkips ps'
  --              runRewrites done psFilter{- `mplus` runRewritesGroup done psFilter -})
  --           (runRewritesGroup done ps)

runRewriteSingle :: RWAnnot s
                 => ([RewriteContext s] -> Bool)
                 -> [RewriteContext s]
                 -> RWM s [RewriteContext s]
runRewriteSingle done []
  = mzero
runRewriteSingle done (p:ps)
  = do r  <- ofList alwaysRules
       ifte (r p) (\p' -> return (p':ps))
                  (do ps' <- runRewriteSingle done ps
                      return (p:ps'))

runRewritesGroup :: RWAnnot s
                 => ([RewriteContext s] -> Bool)
                 -> [RewriteContext s]
                 -> RWM s [RewriteContext s]
runRewritesGroup done ps
 | done ps
 = return ps
runRewritesGroup done ps
  = do doRewrite                   <- ofList rules
       b <- gets buffers
       ps'                  <- {- dbgPP ("Rewrote:\n"++render(pp(someStmts))++"\n"++render(pp(otherStmts))++"\n") <$> -}
                                        (doRewrite ({- dbgPP "trying:" -} ps))
       b' <- gets buffers

       -- Marked is set up so that the list of processes is still aligned.
       -- This works if the processes we expected to "go away" actually do,
       -- hence the following check:
       -- cond $ concatMap filterSkips someStmts' == concatMap filterSkips toNotSkip
       cond $ ps' /= ps || not (buffersUnchanged b b')
       runRewrites done $ concatMap filterSkips ps'

stitchContexts cs cs'
  = let (cs'', rest) = L.foldl' go ([], cs') cs
    in cs'' ++ rest
  where
    go (out,cs) c = let (c', cs') = stitchOne c [] cs in
                    (c':out, cs')


stitchOne c oldCs []
  = (c, oldCs)
stitchOne c1@(One p1 _ s1) oldCs (c2@(One p2 _ s2):cs)
  | p1 == p2 = (joinContext c1 c2, oldCs ++ cs)
stitchOne c1@(Par x1 xs1 s1) oldCs (c2@(Par x2 xs2 s2):cs)
  | x1 == x2 && xs1 == xs2 = (joinContext c1 c2, oldCs ++ cs)
stitchOne c oldCs (c':cs)
  = stitchOne c (c':oldCs) cs

joinContexts [] []
  = []
joinContexts (x:xs) (y:ys)
  = (joinContext x y) : joinContexts xs ys

joinContext :: RWAnnot s => RewriteContext s -> RewriteContext s -> RewriteContext s

joinContext (Par x xs c) (Par y ys d)
  | x == y && xs == ys
  = Par x xs (joinContext c d)
joinContext (One p sp s1) (One p' sp' s2)
  | p == p' && sp == sp'
  = (One p sp (seqStmts [s1, s2]))
joinContext ToSkip c
  = c
joinContext c ToSkip
  = c
joinContext c1 c2
  = Sequence True [c1, c2]

collectContext :: RWAnnot s
               => RewriteContext s
               -> RWM s (Maybe (RewriteContext s))
collectContext (Par x xs c)
  = do Just (Ast c') <- collectContext c
       return . Just $ Ast (Sum x xs c')
-- collectContext (One p sp (While l _ s))
--   | whileReactive l s
--   = return . Just $ Ast (One p sp s)
collectContext (One p sp (ForEach x (_, T.EVar xs _) s))
  = return . Just $ Par [x] (Singleton xs) (One p False s)
collectContext (One p sp (ForEach x (_, e) s))
  = do mxs <- getPidSetMaybe p e
       return $ do xs <- mxs
                   return $ Par [x] (Singleton xs) (One p False s)
collectContext (One p True (Seq (s:ss)))
  = do Just c@(Par _ _ _) <- collectContext (One p True s)
       return . Just $ Sequence True [c, One p True (seqStmts ss)]
collectContext c
  = return Nothing

collectSome :: RWAnnot s => [RewriteContext s] -> RWM s [RewriteContext s]
collectSome []
  = return []
collectSome (c:cs')
  = do csColl <- collectSome cs'
       mcColl  <- collectContext c
       case mcColl of
         Nothing -> return (c:csColl)
         Just c' -> ofList [c':csColl, c:csColl]

allDone ps = null ps

filterSkips :: RWAnnot s => RewriteContext s -> [RewriteContext s]
filterSkips c = go c
  where
    go :: RWAnnot s => RewriteContext s -> [RewriteContext s]
    go (FinPar xs)   = concatMap filterSkips xs
    go (Par x xs s)  = Par x xs <$> filterSkips s
    go (Sum x xs s)  = Sum x xs <$> filterSkips s
    go (Ast c)       = Ast <$> filterSkips c
    go (One p _ Skip) = []
    go (One p sp s)   = [One p sp s]
    go (Sequence s cs) = case concatMap filterSkips cs of
                           []  -> []
                           [x] -> filterSkips x
                           cs' -> [Sequence s cs']
    go c = abort "filterSkips" c

chooseToSkips :: [RewriteContext s] -> [([RewriteContext s], [RewriteContext s], [RewriteContext s])]
chooseToSkips []
  = [([], [], [])]
chooseToSkips (c:cs)
  = concat [ [
               (c:toSkip, toStay, ToSkip:csMarked)
             , (toSkip, c:toStay, c:csMarked)
             ]
           | (toSkip, toStay, csMarked) <- chooseToSkips cs
           ]

choosePrefixes :: RWAnnot s => [RewriteContext s] ->  [([RewriteContext s], [RewriteContext s])]
choosePrefixes []
  = return ([], [])
choosePrefixes (c:cs)
  = do (pres, posts)   <- choosePrefixes cs
       (c_pre, c_post) <- splitContext c
       return (c_pre:pres, c_post:posts)

chooseMerges []
  = return ([], [])
chooseMerges (p@(Par _ _ _) : cs)
  = do (ms, notms) <- chooseMerges cs
       ofList [(p:ms, notms), (ms, p:notms)]
chooseMerges (p : cs)
  = do (ms, notms) <- chooseMerges cs
       return (ms, p:notms)

partitions []
  = [([], [])]
partitions (x : xs)
  = concat [ [(x : ps, qs), (ps, x : qs)]  | (ps, qs) <- partitions xs ]

maybeM mv act = maybe (return ()) act mv
freshInt :: RWM s Int
freshInt = do c <- gets ctr
              modify $ \s -> s { ctr = c + 1 }
              return c

class Fresh a where
  fresh :: a -> RWM s a

instance Fresh Id where
  fresh x = do i <- freshInt
               return (x ++ "$" ++ show i)

instance Fresh ProcessIdSpec where
  fresh (Forall q)      = return $ Forall q
  fresh (Unfolded q qs) = flip Unfolded qs <$> fresh q
  fresh (Concrete q)    = Concrete <$> fresh q

fromIceT :: RWAnnot a
         => [IceTProcess a]
         -> RWTrace a --[RewriteContext a]
fromIceT ps
  = case rfRes of
      Nothing       -> abort "Not Race Free!" ps
      Just (m1, m2) ->
        trace . snd $ findRewrite (runRewrites allDone cs) initState { concrSends = m1
                                                                     , symSends   = m2
                                                                     , pidSets    = psets
                                                                     }
  where
    allDone ps'
      | ps' /= cs = all nonTermLoop ps'
      | otherwise = False
    nonTermLoop (One p _ (While l _ s)) = whileReactive l s
    nonTermLoop (Par _ _ c)             = nonTermLoop c
    nonTermLoop (Ast _)                 = True
    nonTermLoop _                       = False

    cs    = dbgPP "cs!" (toContext <$> ps)
    psets = [ pset | ParIter _ pset _ <- ps ]
    rfRes = tySenders $ dbgPP "ps" ps

toContext :: RWAnnot a => IceTProcess a -> RewriteContext a
toContext (Single p s)     = One (Concrete p) True s
toContext (ParIter p ps s) = Par [p] (Singleton ps) $ One (Unfolded p ps) True s
-- runRWM :: RWM s (RWResult a (RWTrace s)) -> RWState s -> RWResult (RWTrace s) [RWTrace s]
-- runRWM rwm s0
--   = fromMaybe failures success
--   where
--     rewrites = runStateT rwm s0
--     success  = (Result . trace) <$> listToMaybe [ s | (Result _, s) <- rewrites ]
--     failures = Stuck [ t | (Stuck t, _) <- rewrites ]

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
       (h, buf') <- ofList $ do msgs <- msgss
                                dequeue' msgs
       modify $ \s -> s { buffers = Env.insert (buffers s)
                                               (t,p,q)
                                               buf'
                          }
       return h
  where
    dequeue' []    = []
    dequeue' (h:t) = [(h, t)]

bind :: (ProcessIdSpec, Id) -> IceTExpr s -> RWM s ()
bind (p,x) e
  = modify $ \s -> s { consts = Env.insert (consts s) (p,x) e }

eval :: RWAnnot s => ProcessIdSpec -> IceTExpr s -> RWM s (IceTExpr s)
eval p e@(T.EUnion es)
  = T.EUnion <$> mapM (eval p) es
eval _ e@(T.EVal _ _ _)
  = return e
eval p (T.ESymElt set l)
  = do set' <- eval p set
       return (T.ESymElt set' l)
eval p e@(T.EVar x _)
  = do c <- gets consts
       case Env.lookup c (p,x) of
         Just v -> return v
         _      -> return e
eval p e@(T.ECase _ x alts _ l)
  = do eVal <- eval p x
       ifte (ofList alts >>= unifyExpr eVal)
            (return)
            (return e)
         where
           unifyExpr :: RWAnnot s => IceTExpr s
                     -> (Id, [Id], IceTExpr s)
                     -> RWM s (IceTExpr s)
           unifyExpr (T.ECon c xs _) (c', xs', e')
             | c == c' && length xs == length xs'
             = eval p $ T.subst (zip xs' xs) e'
           unifyExpr _ _
             = mzero
eval p (T.ECon c es l)
  = do es' <- mapM (eval p) es
       return $ T.ECon c es' l
eval p e@(T.EApp _ _ l)
  = do as' <- mapM (eval p) as
       return $ foldl' (\a x -> T.EApp a x l) f as'
  where
    (f, as) = T.collectAppArgs e
eval p _
  = return $ T.EVal Nothing Nothing T.dummyAnnot

getPidMaybe :: RWAnnot s => ProcessIdSpec -> IceTExpr s -> RWM s ProcessId
getPidMaybe pid m
  = do m' <- eval pid m
       case m' of
         T.EVal (Just (T.CPid p)) _ _  -> return p
         _                           -> mzero

getPidSetMaybe :: RWAnnot s => ProcessIdSpec -> IceTExpr s -> RWM s (Maybe ProcessId)
getPidSetMaybe pid m
  = do m' <- eval pid m
       return $ case m' of
                  T.EVal (Just (T.CPidSet p)) _ _ -> Just p
                  _                             -> Nothing
-- type PairRule s = IceTProcess s
--                -> IceTProcess s
--                -> RWM s (RWResult (IceTProcess s, IceTProcess s) (RWTrace s))
-- data RWResult a b = Result a
--                   | Stuck b
-- instance (Pretty a, Pretty b) => Pretty (RWResult a b) where
--   ppPrec _ (Result a) = text "OK!" $$ pp a
--   ppPrec _ (Stuck b)  = text "Stuck :(" $$ pp b

-- split1 :: IceTProcess s -> Maybe (ProcessId, IceTStmt s, IceTStmt s)
-- split1 (Single p s) = Just (p,s1,s2)
--   where
--     (s1,s2) = split1stmt s
-- split1 (Unfold p _ _ s _) = Just (p,s1,s2)
--   where
--     (s1,s2) = split1stmt s
-- split1 _                 = Nothing

-- split1stmt (Seq (s:s')) = (s, seqStmts s')
-- split1stmt s            = (s, Skip)

-- setStmt s (Single p _)         = Single p s
-- setStmt s (Unfold p' p ps _ t) = Unfold p' p ps s t

seqTrace :: RWAnnot s => RWTrace s -> RWM s ()
seqTrace t
  = modify $ \s -> s { trace = seqStmts [trace s, t] }

-- procPid :: IceTProcess s -> Maybe ProcessId
-- procPid (Single p _)     = Just p
-- procPid (Unfold p _ _ _ _) = Just p
-- procPid _                = Nothing

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

-- extendExt :: ExtMap a -> ExtMap a -> ExtMap a
-- extendExt e0 e1
--   = Env.foldlWithKey go e0 e1
--   where
--     go e p s
--       = Env.insert e p $ seqStmts [Env.findWithDefault e Skip p, s]

-- rewriteLocal :: RWAnnot s => PairRule s
-- rewriteLocal a b
--   | Just (p, Assgn x t e, s') <- split1 a
--   = do e' <- eval p e
--        bind (p,x) e'
--        seqTrace (XAssgn p x p e')
--        return $ Result (setStmt s' a, b)
--   | Just (p, Case e cs md, s') <- split1 a
--   = do e' <- eval p e
--        case e' of
--          T.ECon c xs _ ->
--            let s = matchingCase c xs cs md in
--            return $ Result (setStmt (seqStmts [s,s']) a, b)
--          _             ->
--            do Result ps <- rewriteAllCases a s' cs md b
--               return $ Result (ps !! 0, ps !! 1)
-- rewriteLocal a b
--   = mzero

-- rewriteAllCases a s [] Nothing b
--   = return $ Result [setStmt s a, b]
-- rewriteAllCases a s [] (Just d) b
--   = doRewrite (all done1) [setStmt d a, b]
-- rewriteAllCases a s ((T.ECon _ bs _, s'):alts) def b
--   = doRewrite (isDone a) [setStmt s' a, b]
--   where
--     isDone (Single p _) ps = all (==Skip) [ s | Single p' s <- ps, p' == p ]

-- matchingCase :: RWAnnot s
--              => Id
--              -> [IceTExpr s]
--              -> [(IceTExpr s, IceTStmt s)]
--              -> Maybe (IceTStmt s)
--              -> IceTStmt s
-- matchingCase c xs cs md = go cs
--   where
--     go []
--       = fromMaybe Skip md
--     go ((T.ECon c' xs' _, s):cs')
--       | c == c'
--       = L.foldl' subst s (zip xs' xs)
--       | otherwise
--       = go cs'
--     subst s (T.EVar x _, e) = substStmt x e s

-- rewriteWhileLoop :: RWAnnot s => PairRule s
-- rewriteWhileLoop a b
--   | Just (p, While s, s') <- split1 a
--   , not (done1 b)
--   = do Result ps <- doRewrite (loopCont p) [setStmt s a, b]
--        let b' = ps !! 1
--        return $ Result (a, b')
--   where
--     loopCont p ps = all (check p) ps
--     check p c@(Single p' s)     = check' p p' s c
--     check p c@(Unfold p' _ _ s _) = check' p p' s c
--     check' p p' s c
--       | p == p'   = s == Continue
--       | otherwise = done1 c
-- rewriteWhileLoop _ _
--   = mzero

-- rewriteWhileExit :: RWAnnot s => PairRule s
-- rewriteWhileExit a b
--   | Just (p, While s, s') <- split1 a
--   = do Result ps <- doRewrite (\ps -> done1 (ps !! 0)) [setStmt s a, b]
--        let (a',b') = (ps !! 0, ps !! 1)
--        return $ Result (setStmt s' a', b')
-- rewriteWhileExit _ _
--   = mzero

-- eraseConsts :: ProcessId -> RWM s [(Id, IceTExpr s)]
-- eraseConsts p
--   = do cs <- gets consts
--        let cenv = Env.updateAll del cs
--        modify $ \s -> s { consts = cenv }
--        return [ (x',c) | ((p',x'),c) <- Env.toList cs, p == p' ]
--          where
--            del (p',x) v
--              | p == p'   = Nothing
--              | otherwise = Just v

-- withResult :: RWM s (RWResult a b) -> (a -> RWM s (RWResult c b)) -> RWM s (RWResult c b)
-- withResult act f
--   = do res <- act
--        case res of
--          Stuck t   -> return $ Stuck t
--          Result ps -> f ps


-- rewriteForEach :: RWAnnot s => PairRule s
-- rewriteForEach a b@(ParIter q qs _)
--   | Just (p, ForEach x xs body, s') <- split1 a
--   = do x0    <- fresh x
--        buf0  <- gets buffers
--        t0    <- gets trace
--        exts0 <- gets exts
--        mems0 <- gets mems
--        -- let s0 = substStmt x (T.EVal (Just (T.CPid x0)) T.dummyAnnot) body
--        bind (p,x) (T.EVal (Just (T.CPid x0)) T.dummyAnnot)
--        modify $ \s -> s { mems = (x0, xs) : mems0, trace = Skip }

--        withResult (doRewrite (\ps -> done1 (ps !! 0) && (unfoldProg (ps!!1))) [Single p body, b]) $
--          \ps -> do
--          let Unfold _ _ _ s _ = ps !! 1
--          buf1  <- gets buffers
--          t1    <- gets trace
--          force $ buffersUnchanged buf0 buf1
--          oldcs <- eraseConsts x0
--          cs    <- gets consts
--          let c0       = Env.addsEnv cs [ ((q,x), T.txExprPid revSub c) | (x,c) <- oldcs, x /= q ]
--              revSub r l
--                | r == x0   = T.EVar q l
--                | otherwise = T.EVal (Just (T.CPid r)) l
--          modify $ \s -> s { mems   = mems0
--                           , trace  = seqStmts [t0, ForEach x xs (substStmt x0 (T.EVar x T.dummyAnnot) t1) ]
--                             -- This has bugs: 1. need to replace q0 with q
--                             --                2. DELETE vars that were assigned
--                             --                   in the loop body
--                           , consts = c0
--                           -- Need to nondet and lift these
--                           , exts   = exts0 `extendExt` exts s
--                           }
--          -- Need to update the thinger here.
--          return $ Result (Single p s', ParIter q qs s) -- {(unSubstPid q0 q s))
--          where
--            unfoldProg (ParIter _ _ _) = False
--            unfoldProg (Unfold q0 q qs s t)
--              = s /= t
-- rewriteForEach _ _
--   = mzero

-- rewriteForIter :: RWAnnot s => PairRule s
-- rewriteForIter a b@(ParIter q qs t)
--   | Just (p, ForEach x xs body, s') <- split1 a
--   = do x0   <- fresh x
--        buf0 <- gets buffers
--        t0   <- gets trace
--        mems <- gets mems
--        let s0 = substStmt x (T.EVar x0 T.dummyAnnot) body
--        modify $ \s -> s { mems = (x0, xs) : mems, trace = Skip }
--        Result _ <- doRewrite (all (pdone p)) [Single p s0, b]
--        buf1  <- gets buffers
--        t1    <- gets trace
--        force $ buffersUnchanged buf0 buf1
--        oldcs <- eraseConsts x0
--        modify $ \s -> s { mems   = mems
--                         , trace  = seqStmts [t0, ForEach x xs (substStmt x0 (T.EVar x T.dummyAnnot) t1) ]
--                           -- This has bugs: 1. need to replace q0 with q
--                           --                2. DELETE vars that were assigned
--                           --                   in the loop body
--                         }
--        return $ Result (setStmt s' a, b)
--          where
--            pdone p a
--              | Just p' <- procPid a, p' == p
--              = done1 a
--            pdone p (Unfold q0 q qs' x t)
--              | qs' == qs
--              = x == t
--              -- = x == substStmt q (T.EVal (Just (T.CPid q0)) T.dummyAnnot) t
--            done1ForEach (Single p s')
--              | Just p' <- procPid a, p' == p
--              = s' == Skip
--            done1ForEach (Unfold q0' q' qs' t' t'')
--              | qs' == qs
--              = t' == substStmt q' (T.EVal (Just (T.CPid q')) T.dummyAnnot) t''
--            done1ForEach _
--              = False
-- rewriteForIter a b
--   = mzero

-- rewriteUnfoldSend :: RWAnnot s => PairRule s
-- rewriteUnfoldSend a (ParIter q qs t)
--   | Just (p, Send ty e_q e_m, s') <- split1 a
--   = do q'  <- getPidMaybe p e_q
--        qs' <- L.lookup q' <$> gets mems
--        flip (maybe mzero) qs' $ \qs' ->
--          case qs' of
--            T.EVal (Just (T.CPidSet qs')) _
--              | qs' == qs -> do
--                let qpid = T.EVal (Just (T.CPid q')) T.dummyAnnot
--                bind (q',q) qpid
--                rewriteSend a (Unfold q' q qs t t)
--                -- in rewriteSend a (Unfold q' q qs (substStmt q qpid t) t)
--                -- return (a, Unfold q' qs (substStmt q (T.EVar q' T.dummyAnnot) t) t)
--            _ -> mzero
-- rewriteUnfoldSend _ _
--   = mzero

-- rewriteFold :: RWAnnot s => PairRule s
-- rewriteFold (Unfold p0 p ps s t) b
--   | s == t = return $ Result (ParIter p ps s, b)
-- rewriteFold _ _ = mzero

-- instantiateConsts :: ProcessId -> ProcessId -> RWM s ()
-- instantiateConsts q0 q
--   = do c       <- gets consts
--        let cxs    = [ ((q0,pidvar x), v) | ((q',x), v) <- Env.toList c, q' == q ]
--            pidvar x | x == q    = q0
--                     | otherwise = x
--        modify $ \s -> s { consts = Env.addsEnv c cxs }

-- rewriteUnfoldRecv :: RWAnnot s => PairRule s
-- rewriteUnfoldRecv a (ParIter q qs t)
--   | Just (p, Recv ty Nothing mx, s') <- split1 a
--   = do q0      <- fresh q
--        senders <- flip Env.lookup ty <$> gets symSends
--        sender  <- lift $ fromMaybe [] senders
--        instantiateConsts q0 q

--        force (sender == qs)

--        seqTrace (Assgn q0 Nothing (T.ESymElt (T.EVar qs T.dummyAnnot) T.dummyAnnot))
--        let q0pid = T.EVal (Just (T.CPid q0)) T.dummyAnnot
--        bind (q0,q) q0pid
--        return $ Result (setStmt (seqStmts [Recv ty (Just q0pid) mx,s']) a, Unfold q0 q qs t t)
-- {-       ps <- doRewrite (all aProgress)
--           [ setStmt (Recv ty (Just q0pid) mx) a
--           , Unfold q0 q qs t t
--           ]
--        return (setStmt s' a, ps !! 1) -}
--        -- let a' = ps !! 0
--        --     b' = ps !! 1
--        -- Dbg.trace "Unfold (b)" $ return ()
--        -- return (setStmt Skip a, Unfold q0 qs Skip t)
--          where
--            aProgress a'
--              | procPid a == procPid a' = done1 a'
--              | otherwise               = True
-- rewriteUnfoldRecv _ _
--   = mzero

-- rewriteSend :: RWAnnot s => PairRule s
-- rewriteSend a b
--   | Just (p, Send ty e_q e_m, s') <- split1 a
--   , Just q                        <- procPid b
--   = do c <- gets consts
--        q' <- getPidMaybe p e_q
--        forceM (notExternal q')
--        if q == q' then do
--          m <- eval p e_m
--          enqueue ty p q m
--          return $ Result (setStmt s' a, b)
--        else
--          mzero
-- rewriteSend _ _
--   = mzero

-- rewriteRecvFrom :: RWAnnot s => PairRule s
-- rewriteRecvFrom a b
--   | Just (q, Recv ty Nothing mx, s') <- split1 a
--   , Just p <- procPid b
--   = do senders <- flip Env.lookup ty <$> gets concrSends
--        sender  <- lift $ fromMaybe [] senders
--        force (sender == p)
--        let recv' = Recv ty (Just (T.EVal (Just (T.CPid p)) T.dummyAnnot)) mx
--        rewriteRecvFrom (setStmt (seqStmts [recv',s']) a) b
-- rewriteRecvFrom a b
--   | Just (q, Recv ty (Just e_p) mx, s') <- split1 a
--   , Just p <- procPid b
--   = do p' <- getPidMaybe q e_p
--        if p == p' then do
--          e <- dequeue ty p q
--          flip (maybe (return ())) mx $ \x -> do
--            bind (q,x) e
--            seqTrace (XAssgn q x p e)
--          return $ Result (setStmt s' a, b)
--        else
--          mzero
--   -- "Need" a case here for receiving from a specific
--   -- but not-yet-unfolded pid
-- rewriteRecvFrom a _
--   = mzero

-- split :: IceTProcess s -> RWM s (IceTProcess s, IceTProcess s)
-- split (Single p s)
--   = lift (mkProc <$> splitStmts s)
--   where
--     mkProc (s,t) = (Single p s, Single p t)
-- split (ParIter p ps s)
--   = lift (mkProc <$> splitStmts s)
--   where
--     mkProc (s,t) = (ParIter p ps s, ParIter p ps t)
-- split (Unfold p0 p ps s t)
--   = lift (mkProc <$> splitStmts s)
--   where
--     mkProc (s',s'') = (Unfold p0 p ps s' t, Unfold p0 p ps s'' t)

-- splitStmts :: IceTStmt a -> [(IceTStmt a, IceTStmt a)]
-- splitStmts (Seq stmts)
--   -- = [(s, seqStmts stmts)]
--   = [ seqify $ splitAt i stmts | i <- [n,n-1 .. 0] ]
--   where
--     seqify (s,t) = (seqStmts s, seqStmts t)
--     n            = length stmts
-- splitStmts s
--   = [(s, Skip)]

-- force :: Bool -> RWM s ()
-- force True  = return ()
-- force False = mzero

-- forceM :: RWM s Bool -> RWM s ()
-- forceM act = act >>= force

-- notExternal :: ProcessId -> RWM s Bool
-- notExternal p = not . elem p <$> gets external

-- {-
-- paste (Single p s) (Single p' t)
--   | p == p' = Single p (seqStmts [s,t])
-- paste (ParIter p ps s) (ParIter p' ps' t)
--   | p == p' && ps == ps' = ParIter p ps (seqStmts [s,t])
-- paste (Unfold p0 p ps s0 s) (Unfold p0' p' ps' s0' s')
--   | p0 == p0' && ps == ps' = Unfold p0 p ps (seqStmts [s0, s0']) s
-- paste (Unfold p0 p ps s0 s) (ParIter p' ps' t)
--   | ps == ps' = Unfold p0 p ps s0 (seqStmts [s,t])
-- paste (ParIter p' ps' t) (Unfold p0 p ps s0 s)
--   | ps == ps' = Unfold p0 p ps s0 (seqStmts [t,s])
-- paste x y
--   = error ("paste:\n" ++ ppShow x ++ "\n" ++ ppShow y)
-- -}
-- done p q = done1 p && done1 q

-- done1 (Single _ Skip)        = True
-- done1 (Unfold _  _ _ Skip _) = True
-- done1 (ParIter _ _ Skip)     = True
-- done1 _                      = False

-- {-
-- doPairRewrite :: RWAnnot s
--           => (IceTProcess s -> IceTProcess s -> Bool)
--           -> IceTProcess s
--           -> IceTProcess s
--           -> RWM s (IceTProcess s, IceTProcess s)
-- doPairRewrite = runRules (rules ++ map flipRule rules)
-- -}

-- doRewrite :: RWAnnot s
--           => ([IceTProcess s] -> Bool)
--           -> [IceTProcess s]
--           -> RWM s (RWResult [IceTProcess s] (RWTrace s))
-- doRewrite stop ps
--   = go $ Env.fromList (zip [0..] ps)
--   where
--     n     = length ps
--     procs = (snd <$>) . Env.toList
--     pairs = [ (i,j) | i <- [0..n-1], j <- [0..n-1], i /= j ]
--     go m
--       | stop (procs m)
--       = return $ Result (procs m)
--     go m = do (i, j) <- lift pairs
--               let p = fromJust $ Env.lookup m i
--                   q = fromJust $ Env.lookup m j
--               r                <- lift allrules
--               result           <- r p q
--               case result of
--                 Stuck t        -> return (Stuck t)
--                 Result (p',q') -> do
--                  force (p /= p' || q /= q')
--                  go $ Env.addsEnv m [(i,p'),(j,q')]

-- allrules :: RWAnnot s => [PairRule s]
-- allrules = rules ++ map flipRule rules

-- rules :: RWAnnot s => [PairRule s]
-- rules = [ rewriteLocal
--         , rewriteUnfoldRecv
--         , rewriteSend
--         , rewriteRecvFrom
--         , rewriteForIter
--         , rewriteForEach
--         , rewriteUnfoldSend
--         , rewriteWhileExit
--         , rewriteWhileLoop
--         -- This needs to be last!
--         , rewriteStuck
--         ]

-- rewriteStuck :: RWAnnot s => PairRule s
-- rewriteStuck _ _ = do t <- gets trace
--                       return $ Stuck t

-- flipRule r p q = do res <- r q p
--                     case res of
--                       Result (q', p') -> return $ Result (p', q')
--                       Stuck t         -> return $ Stuck t

tySenders :: [IceTProcess a] -> Maybe (Env.Env IceTType [ProcessId], Env.Env IceTType [ProcessId])
tySenders ps
  | all (rf concrSend symSend) [ (p, s)  | Single p s     <- ps ] &&
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

pidLit p = T.EVal (Just (T.CPid p)) Nothing T.dummyAnnot
