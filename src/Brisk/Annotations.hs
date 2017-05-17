{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Brisk.Annotations
  ( BriskAnnotation(..)
  , top
  ) where
import Control.Distributed.Process hiding (send, receive)

import Language.Haskell.TH
import Data.Data
import Brisk.Model.Types as T

data BriskAnnotation = SpecModule
                     | Assume Name
                     | Forever
                     deriving (Data, Show)
top :: a
top = error "any"
