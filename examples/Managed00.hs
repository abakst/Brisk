{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Managed where

import Data.Binary
import GHC.Generics (Generic)
import qualified Data.HashMap.Strict as M
import Control.Distributed.Process hiding (call)
import Control.Distributed.Process.Extras.Time
import Control.Distributed.Process.ManagedProcess
import Control.Distributed.Process.ManagedProcess.Client

data DataNodeState = DNS

data DataNodeAPI = Bloop
                   deriving (Eq, Ord, Show, Generic)

instance Binary DataNodeAPI

data DataNodeResponse = OK
                      deriving (Eq, Ord, Show, Generic)
instance Binary DataNodeResponse

initState = DNS

runDataNode :: Process ()
runDataNode =
  serve initState initializeDataNode dataNodeProcess

initializeDataNode :: DataNodeState -> Process (InitResult DataNodeState)
initializeDataNode s = return $ InitOk s NoDelay

dataNodeProcess :: ProcessDefinition DataNodeState
dataNodeProcess = defaultProcess {
  apiHandlers = [dataNodeAPIHandler]
  }

type DataNodeReply = Process (ProcessReply DataNodeResponse DataNodeState)

dataNodeAPIHandler :: Dispatcher DataNodeState
dataNodeAPIHandler = handleCall dataNodeAPIHandler'

dataNodeAPIHandler' :: DataNodeState -> DataNodeAPI -> DataNodeReply
dataNodeAPIHandler' st Bloop
  = reply OK st

foobert :: ProcessId -> Process DataNodeResponse
foobert p = call p Bloop

main :: Process DataNodeResponse
main = do server <- spawnLocal runDataNode
          foobert server
