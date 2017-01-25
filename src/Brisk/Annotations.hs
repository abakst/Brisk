{-# LANGUAGE DeriveDataTypeable #-}
module Brisk.Annotations
  ( BriskAnnotation(..)
  , top
  ) where
import Language.Haskell.TH
import Data.Data

data BriskAnnotation = SpecModule
                     | Assume Name
                     deriving (Data, Show)
top :: a
top = error "any"
