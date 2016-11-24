module Brisk.Model.Env (empty, lookup, insert, addsEnv, toList, Env(..)) where

import Prelude hiding (lookup, insert)
import qualified Data.Map.Strict as M

type Env k v = M.Map k v

empty :: Ord k => M.Map k v
empty = M.empty               

lookup :: Ord k => M.Map k v -> k -> Maybe v
lookup e k = M.lookup k e

insert :: Ord k => M.Map k v -> k -> v -> M.Map k v
insert e k v = M.insert k v e

toList :: M.Map k v -> [(k,v)]
toList = M.toList

addsEnv :: Ord k => Env k v -> [(k,v)] -> Env k v
addsEnv = foldl go 
  where
    go e (k,v) = insert e k v
