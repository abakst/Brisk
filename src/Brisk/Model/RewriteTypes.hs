{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Brisk.Model.RewriteTypes where

import Data.Function
import Data.List as L
--   (sort, sortBy, reverse, nub, lookup, foldl', group, groupBy, (\\), intersperse, intercalate)
-- import Data.Char
-- import Data.Maybe
import Control.Monad.State
import Control.Monad.Logic
import           Brisk.Model.Types (Id)
import qualified Brisk.Model.Types as T
import Brisk.Model.IceT hiding (Store, fresh)
import Brisk.Model.Env as Env
import Brisk.Pretty
import Brisk.UX
import Text.Show.Pretty (ppShow)
import Text.PrettyPrint.HughesPJ as PP (($$), (<+>), (<>), vcat, hcat, parens) 
import qualified Debug.Trace as Dbg

--------------------------------------------------------------------------------
-- Rewrite Types
--------------------------------------------------------------------------------
-- type RWM s a = StateT (RWState s) [] a       
-- type RWM s a = LogicT (State (RWState s)) a
type RWM s a = StateT (RWState s) Logic a

type Store  s  = Env (ProcessIdSpec, Id) (IceTExpr s)
type Buffer s  = Env (T.Type Id, ProcessId, ProcessId) [IceTExpr s]
type RWTrace s = IceTStmt s
type ExtMap s  = Env ProcessId (IceTStmt s)
type RWAnnot s = (T.Annot s, Eq s, Show s)

data RWState a = RWS { ctr        :: !Int
                     , pidSets    :: ![ProcessId]
                     , exts       :: !(ExtMap a)
                     , mems       :: ![(Id, IceTExpr a)]
                     , buffers    :: !(Buffer a)
                     , consts     :: !(Store a)
                     , trace      :: !(RWTrace a)
                     , concrSends :: !(Env.Env IceTType [ProcessId])
                     , symSends   :: !(Env.Env IceTType [ProcessId])
                     }
    
initState :: RWState s
initState = RWS { ctr        = 0
                , pidSets    = []
                , exts       = empty
                , mems       = []
                , buffers    = empty
                , consts     = empty
                , trace      = Skip
                , concrSends = empty
                , symSends   = empty
                }

data ProcessIdSpec = Forall ProcessId
                   | Unfolded ProcessId ProcessId
                   | Concrete ProcessId
                     deriving (Eq, Ord, Show)

data RewriteContext s = One ProcessIdSpec Bool (IceTStmt s)
                      | FinPar [RewriteContext s]
                      | Ast (RewriteContext s)
                      | Par [Id] SetBag (RewriteContext s)
                      | Sum [Id] SetBag (RewriteContext s)
                      | Sequence Bool [RewriteContext s]
                      -- Special context:
                      | ToSkip
                      deriving (Eq, Show)

data SetBag = Zipped Int SetBag
            | Product [SetBag]
            | Singleton Id
              deriving (Show, Eq, Ord)

bagIds :: RWAnnot s => SetBag -> IceTExpr s
bagIds (Singleton x) = T.EVar x T.dummyAnnot
bagIds (Zipped n b)  = T.EApp (T.EApp (T.EVar "$zip" T.dummyAnnot)
                                      (T.EVal (Just (T.CInt n)) T.dummyAnnot)
                                      T.dummyAnnot)
                              be T.dummyAnnot
  where
    be = bagIds b

specPid :: ProcessIdSpec -> ProcessId
specPid (Unfolded p _) = p
specPid (Concrete p)   = p
specPid p              = abort "specPid" p

contextPid (One p _ _)
  = return  p
contextPid (Par xs _ cs)
  = do p <- contextPid cs
       if specPid p `elem` xs then return p else mzero
                               
instance Eq s => Ord (RewriteContext s) where
  compare (Par xs sb c) (Par xs' sb' c') = compare sb sb'
  compare (Sequence _ (c:cs)) d          = compare c d
  compare c (Sequence _ (d:ds))          = compare c d
  compare (Par _ _ _) _                  = LT
  compare _           (Par _ _ _)        = GT
  compare _           _                  = EQ
                               
mergeSetBags :: SetBag -> SetBag -> Maybe SetBag
mergeSetBags (Zipped n1 s1) (Zipped n2 s2)
  | s1 == s2 = Just $ Zipped (n1 + n2) s1
mergeSetBags (Singleton s) (Singleton s')
  | s == s'
  = Just $ Zipped 2 (Singleton s)
mergeSetBags (Zipped n s) s'
  | s == s' = Just $ Zipped (n+1) s
mergeSetBags s' (Zipped n s)
  | s == s'
  = Just $ (Zipped (n+1) s)
mergeSetBags _ _
  = Nothing

collectSets :: SetBag -> [Id]
collectSets (Zipped n s)  = collectSets s
collectSets (Product sb)  = L.nub $ concatMap collectSets sb
collectSets (Singleton i) = [i]

mergeAllContexts :: RWAnnot s
                 => [RewriteContext s]
                 -> RWM s (Maybe (RewriteContext s))
mergeAllContexts []     = return Nothing
mergeAllContexts (x:xs) = foldM go (Just x) xs
  where
    go (Just c) c'      = return $ mergeContexts c c'
    go _        _       = return Nothing

mergeContexts :: RewriteContext s
              -> RewriteContext s
              -> Maybe (RewriteContext s)
mergeContexts (Par idxs sets s) (Par idxs' sets' s')
  = do sets'' <- mergeSetBags sets sets'
       Just (Par (idxs ++ idxs') sets'' (finPar s s'))
  where
    finPar (FinPar s) (FinPar t) = FinPar (s ++ t)
    finPar (FinPar s) t          = FinPar (s ++ [t])
    finPar s (FinPar t)          = FinPar (s : t)
    finPar s t                   = FinPar [s,t]
mergeContexts _ _
  = Nothing
instance (Pretty a, Pretty b) => Pretty (Env.Env a b) where
  ppPrec _ e = vcat [ pp a <+> text ":=" <+> pp b | (a,b) <- Env.toList e ]

instance Pretty a => Pretty (Maybe a) where
  ppPrec _ Nothing  = text "<Nothing>"
  ppPrec z (Just s) = ppPrec z s

instance Pretty ProcessIdSpec where
  ppPrec _ (Concrete p)    = pp p
  ppPrec _ (Unfolded p ps) = pp p <+> text "∈" <+> pp ps
  ppPrec _ (Forall ps)     = text "∀" <> pp ps

instance Pretty (RewriteContext s) where
  ppPrec _ (One p False s)
    = text "<<<" <+> pp p <> text ":" <+> pp s <+> text ">>>"
  ppPrec _ (One p _ s)
    = text "<" <+> pp p <> text ":" <+> pp s <+> text ">"
  ppPrec _ (Ast c)
    = text "*" <> pp c
  ppPrec _ (Par xs bag c)
    = text "Π" <> pp xs <> text ":" <> pp bag <> text".[" <> pp c <> text "]"
  ppPrec _ (Sum xs bag c)
    = text "Σ" <> pp xs <> text ":" <> pp bag <> text "." <> pp c <> text "]"
  ppPrec _ (Sequence _ cs)
    = text "Seq" <+> parens (hcat (pp <$> cs))
  ppPrec _ (FinPar [s])
    = pp s
  ppPrec _ (FinPar (c:cs))
    = pp c <+>
      hcat (map ((text "||" <+>). pp) cs)

instance Pretty SetBag where
  ppPrec _ (Singleton xs) = text xs
  ppPrec _ (Zipped n xs)  = pp xs

instance (Pretty a, Pretty b) => Pretty (a,b) where
  ppPrec _ (x,y) = parens (pp x <> text "," <+> pp y)
instance (Pretty a, Pretty b, Pretty c) => Pretty (a,b, c) where
  ppPrec _ (x,y,z) = parens (pp x <> text "," <+> pp y <> text "," <+> pp z)

joinEnvs :: RWAnnot s => [Store s] -> Store s
joinEnvs es = Env.fromList joined
  where
    joined = map joinBindings binds
    binds  = groupBy ((==) `on` fst)
           . sortBy (compare `on` fst)
           $ concatMap Env.toList es

    joinBindings ((p,e):pes) = foldl' go (p,e) pes
    go (p,e) (p',e')
      | p == p'   = (p, T.join e e')
