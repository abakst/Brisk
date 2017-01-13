{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
{-# LANGUAGE TemplateHaskell #-}
module SpawnSym (main) where

import Control.Monad (forM)
import Control.Distributed.Process
import Control.Distributed.BriskStatic
import Control.Distributed.Process.Closure
import Control.Distributed.Process.SymmetricProcess

p :: () -> Process ()
p () = return ()

remotable ['p]

main :: [NodeId] -> Process ()
main nodes = do me     <- getSelfPid
                spawnSymmetric nodes $ $(mkBriskClosure 'p) me
                return ()
