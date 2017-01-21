{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:x #-}
module ImportMe where
import Control.Distributed.Process
import Brisk.Model.Types hiding (Process)

x :: Process ()
x = getSelfPid >> return ()

z :: Int
z = 3
