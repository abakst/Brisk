{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple03 where
import Control.Distributed.Process

myFoldM :: (t1 -> t0 -> Process t1) -> t1 -> [t0] -> Process t1
myFoldM f b []     = return b
myFoldM f b (x:xs) = do b' <- f b x
                        myFoldM f b' xs

spawnLoop :: Process () -> Process [ProcessId] 
spawnLoop gloob = myFoldM go [] [1::Int,2,3]
  where
    go ps _ = do p <- spawnLocal gloob
                 return (p : ps)

main :: Process ()
main = do me <- getSelfPid
          ps <- spawnLoop (return ())
          return ()
