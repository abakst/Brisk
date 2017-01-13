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

data PingMessage = Ping { unPid :: ProcessId }
                 | Pong { unPid :: ProcessId }
               deriving (Typeable, Generic)

instance Binary PingMessage

pingProcess :: ProcessId -> Process ()
pingProcess whom = do me <- getSelfPid
                      send whom $ Ping me
                      expect :: Process PingMessage
                      return ()

pongProcess :: Process ()
pongProcess = do msg  <- expect
                 me   <- getSelfPid
                 send (unPid msg) $ Pong me

main :: Process ()
main = do me  <- getSelfPid
          spawnLocal $ pingProcess me
          pongProcess
