{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.BriskStatic where

import Control.Distributed.Static
import Control.Distributed.BriskStatic.Internal
import Control.Distributed.Process.Internal.Closure.TH (mkClosure, mkStaticClosure)
import Language.Haskell.TH

mkBriskClosure :: Name -> ExpQ
mkBriskClosure n = appE c1 (varE n)
  where c1 = appE (varE castName) (mkClosure n)

mkBriskStaticClosure :: Name -> ExpQ
mkBriskStaticClosure n = appE c1 (varE n)
  where c1 = appE (varE castName) (mkStaticClosure n)
