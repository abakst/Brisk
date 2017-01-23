{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.Process.SymmetricProcess (
    SymSet
  , spawnSymmetric
  ) where

import Control.Monad
import Control.Distributed.Process
import Control.Distributed.Process.Closure

data SymSet a = SymSet {
    size  :: Int
  , elems :: [a]
  }

type SymProcessSet = SymSet ProcessId

instance Functor SymSet where
  fmap f SymSet{size = s, elems = es}
    = SymSet{size = s, elems = fmap f es}

instance Foldable SymSet where
  foldr f b SymSet{elems = es}
    = foldr f b es

instance Traversable SymSet where
  traverse f SymSet{size=s, elems=es}
    = fmap fromList es'
    where
      es' = traverse f es

fromList :: [a] -> SymSet a
fromList xs = SymSet { size  = length xs
                     , elems = xs
                     }

---------------------------------------------------------------------------
spawnSymmetric :: [NodeId] -> Closure (Process ()) -> Process SymProcessSet
---------------------------------------------------------------------------
spawnSymmetric nodes p
  = do ps <- foldM go [] nodes -- nodes $ \node -> undefined
       return SymSet { size = length nodes, elems = ps }
  where
    go a n = do pid <- spawn n p
                return (pid : a)
