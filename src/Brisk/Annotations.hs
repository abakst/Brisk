{-# LANGUAGE DeriveDataTypeable #-}
module Brisk.Annotations (BriskAnnotation(..)) where
import Language.Haskell.TH
import Data.Data

data BriskAnnotation = SpecModule
                     | Assume Name
                     deriving (Data, Show)
