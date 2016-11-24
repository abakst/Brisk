{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
  
> module Test00 where
> import Control.Distributed.Process
> import Control.Distributed.Process.Serializable
> import Data.Generic

{-@ test00 :: forall p. (send p {v:Int | v = 3 }) @-}
  
> test00 :: ProcessId -> Process ()
> test00 p = send p (3 :: Int)

{-@ test01 :: (recv : ProcessId) @-}
  
> test01 :: Process ProcessId
> test01 = expect

test02 :: (recv : ProcessId) `bind` (lam $ \p -> send p {v:Int | v = 3})
  
> test02 :: Process ()  
> test02 = test01 >>= (\p -> test00 p)

Effect: forall m. m >> m >> m
  
> test03 :: Process () -> Process ()  
> test03 m = m >>= (\x -> m >>= (\x -> m))

Effect: forall A B, (A -> B) -> A -> B
  
> test04 = ($)

> test05 m = test01 >>= (\p -> test04 m p)

e ::= x
    | {v:b | φ}
    | let x = e in e
    | λx. e
    | rec x. e
    | e >>= e
  
> data Ping = Ping Int deriving (Generic, Typeable)
> test06 p x = send p (Ping x)
