{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Scratch where
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)

data PingMessage = Ping ProcessId | Pong ProcessId
               deriving (Typeable, Generic)

instance Binary PingMessage                        

pingPong :: ProcessId -> PingMessage -> Process ()
pingPong x (Ping q) = send q (Pong x)
pingPong x _        = expect >>= pingPong x

main :: Process () 
main = do me  <- getSelfPid
          msg <- expect
          pingPong me msg
