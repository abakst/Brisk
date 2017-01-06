{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple03 where
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)

data PingMsg = Ping ProcessId | Pong ProcessId       
               deriving (Typeable, Generic)

instance Binary PingMsg


{-@ R(\X ..., xs) @-}
{-
b := b0
while true
{
  if xs == []:
    break
  else:
    x,xs := split(xs);
    b    := f b x;
}
fold(...)
-}
myFoldM :: (t1 -> t0 -> Process t1) -> t1 -> [t0] -> Process t1
myFoldM f b []     = return b
myFoldM f b (x:xs) = do b' <- f b x
                        myFoldM f b' xs

main :: Process () 
main = do me <- getSelfPid
          myFoldM (\a i -> send me i) () [1::Int,2,3]
