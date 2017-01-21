{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple00 where
import Control.Distributed.Process
import Brisk.Model.Types hiding (Process)
import ImportMe

main :: Process () 
main = do me <- getSelfPid
          send me me

z = EVar "e" ()
foo = x
