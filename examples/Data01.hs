{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- OPTIONS_GHC -fplugin Brisk.Plugin #-}
{- OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Scratch where
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)

data PingMessage = Ping ProcessId | Pong ProcessId
               deriving (Typeable, Generic)

instance Binary PingMessage                        

pingProcess :: ProcessId -> Process ()         
pingProcess whom = do me <- getSelfPid
                      send whom $ Ping me
                      expect :: Process PingMessage
                      return ()

pongProcess :: Process ()
pongProcess = do msg       <- expect
                 case msg of
                   Ping whom -> do
                     me  <- getSelfPid
                     send whom $ Pong me
                   _         ->
                     return ()
main :: Process () 
main = do me  <- getSelfPid
          spawnLocal $ pingProcess me
          pongProcess
