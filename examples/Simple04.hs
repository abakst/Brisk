{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Simple03 where
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)

data PingMsg = Ping ProcessId | Pong ProcessId       
               deriving (Typeable, Generic)

instance Binary PingMsg

foo :: ProcessId -> Process ()         
foo me = do theRealMe <- getSelfPid
            forever $ send me (Ping theRealMe)

{-# ANN forever "let rec f p = p >> f p" #-}
forever :: Process () -> Process ()
forever p = go
  where
    go = p >> go

main :: Process () 
main = do me <- getSelfPid
          spawnLocal $ foo me
          who <- expect
          case who of
            Ping whom -> forever $ send whom me
            _         -> return ()
