{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
module LookAtAnnotations where

import AnnotateMe

foo :: Int
foo = AnnotateMe.x
