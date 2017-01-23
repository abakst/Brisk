{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.BriskStatic where

import Control.Distributed.Static
import Control.Distributed.BriskStatic.Internal
import Control.Distributed.Process.Internal.Closure.TH (mkStatic)
import Language.Haskell.TH

mkBriskStatic :: Name -> Q Exp
mkBriskStatic n = appE c1 (varE castName)
  where c1 = appE (varE castName) (mkStatic n)
