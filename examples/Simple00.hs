{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple00 where
import Control.Distributed.Process
import ImportMe

main :: Process () 
main = do p <- getSelfPid
          m <- expect
          flip send p $ m
