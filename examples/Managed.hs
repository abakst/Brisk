{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{- OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Managed where

import Data.Binary
import GHC.Generics (Generic)
import qualified Data.HashMap.Strict as M
import Control.Distributed.Process hiding (call)
import Control.Distributed.Process.Extras.Time
import Control.Distributed.Process.ManagedProcess

{-
DataNode:
1. register datanode service
2. start "space reporter" ???
3. start RPC service
-}
dataNodeService :: String
dataNodeService = "theque:dataNode"

type BlobId      = String
type DataNodeMap = M.HashMap BlobId String

data DataNodeState = DNS {
    master :: ProcessId
  , blobs  :: !DataNodeMap
  }

data DataNodeAPI = AddBlob String String
                 deriving (Eq, Ord, Show, Generic)

pushBlob :: ProcessId -> String -> String -> Process DataNodeResponse
pushBlob p bn bdata
  = call p (AddBlob bn bdata)

instance Binary DataNodeAPI

data DataNodeResponse = OK
                      | BlobExists
                      deriving (Eq, Ord, Show, Generic)
instance Binary DataNodeResponse

initState m = DNS { blobs = M.empty, master = m }

runDataNode :: ProcessId -> Process ()
runDataNode m =
  serve (initState m) initializeDataNode dataNodeProcess

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
dataNodeAPIHandler' st (AddBlob bn blob)
  = case M.lookup bn (blobs st) of
      Nothing ->
        reply OK st'
        where
          st' = st { blobs = M.insert bn blob (blobs st) }
      Just bdata -> do
        say (bn ++ " := " ++ show bdata)
        reply BlobExists st
