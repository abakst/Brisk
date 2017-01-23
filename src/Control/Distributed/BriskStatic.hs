{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.BriskStatic where

import Control.Distributed.Static
import Control.Distributed.BriskStatic.Internal
import Control.Distributed.Process.Internal.Closure.TH (mkClosure)
import Language.Haskell.TH

mkBriskClosure :: Name -> Q Exp
mkBriskClosure n = appE c1 (varE n)
  where c1 = appE (varE castName) (mkClosure n)
