{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple00 where
import Control.Distributed.Process

main :: Process () 
main = do who <- expect
          me  <- getSelfPid
          send who me
