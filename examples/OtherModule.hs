{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module OtherModule where
import Control.Distributed.Process
import OtherModule

{-# ANN main [| do me <- getSelfPid; return me |] #-}
main :: Process () 
main = do me <- getSelfPid
          send me me
