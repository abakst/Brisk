{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple00 where
import Control.Distributed.Process

main :: Process () 
main = do me <- getSelfPid
          spawnLocal (send me ())
          who <- expect
          send who me
