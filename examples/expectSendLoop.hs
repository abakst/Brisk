{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:expectSend #-}
module Scratch where
import Control.Distributed.Process

expectSend :: Int -> Process ()
expectSend 0
  = return ()
expectSend n
  = do p <- expect
       send p n
       if n == 1 then
         expectSend $ n - 1
       else
         expectSend $ n + 2
