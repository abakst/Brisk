{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:expectSend #-}
module Scratch where
import Control.Distributed.Process

getPid :: Process (Maybe ProcessId)
getPid = expect

expectSend :: Process ()
expectSend = do p <- getPid
                case p of
                  Nothing -> return ()
                  Just p' -> send p' (0 :: Int) >> expectSend
