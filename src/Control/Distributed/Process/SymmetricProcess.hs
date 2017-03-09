{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.Process.SymmetricProcess (
    SymSet
  , selfSign, payload
  , expectFrom
  , spawnSymmetric
  , chooseSymmetric, (?!)
  , empty
  ) where

import Control.Monad
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)
import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Control.Distributed.Process.Closure

---------------------------------------------------------------------------
-- Self Signed Messages
---------------------------------------------------------------------------
data SelfSigned a = SelfSigned { sender  :: ProcessId
                               , payload :: a
                               }
                    deriving (Typeable, Generic)
instance Binary a => Binary (SelfSigned a)

selfSign :: a -> Process (SelfSigned a)
selfSign m = do me <- getSelfPid
                return $ SelfSigned { sender = me, payload = m }

expectFrom :: Serializable a => ProcessId -> Process a
expectFrom p = receiveWait recv
  where
    pred = (==p) . sender
    recv = [ matchIf pred (return . payload) ]

---------------------------------------------------------------------------
-- Symmetric Sets
---------------------------------------------------------------------------
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

---------------------------------------------------------------------------
fromList :: [a] -> SymSet a
---------------------------------------------------------------------------
fromList xs = SymSet { size  = length xs
                     , elems = xs
                     }


---------------------------------------------------------------------------
(?!), chooseSymmetric :: SymSet a -> Int -> a
---------------------------------------------------------------------------
chooseSymmetric SymSet { elems = xs } i = xs !! i
(?!) = chooseSymmetric

---------------------------------------------------------------------------
spawnSymmetric :: [NodeId] -> Closure (Process ()) -> Process SymProcessSet
---------------------------------------------------------------------------
spawnSymmetric nodes p
  = do ps <- foldM go [] nodes
       return SymSet { size = length nodes, elems = ps }
  where
    go a n = do pid <- spawn n p
                return (pid : a)

empty :: SymSet a
empty = fromList []
