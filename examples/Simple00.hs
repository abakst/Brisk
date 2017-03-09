{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:blain #-}
module Simple00 where
import Control.Distributed.Process

main :: Process () 
main = do p <- getSelfPid
          m <- expect :: Process Int
          return ()

someUndefinedFunc :: () -> ProcessId          
someUndefinedFunc () = undefined

blain :: Process ()
blain = do p <- getSelfPid
           let d = someUndefinedFunc ()
           r <- send d d
           let x = someUndefinedFunc r
           send x x
