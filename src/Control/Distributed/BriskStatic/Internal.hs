{-# LANGUAGE TemplateHaskell #-}
module Control.Distributed.BriskStatic.Internal where

import Language.Haskell.TH

castEffect :: a -> b -> a
castEffect x y = x

castName :: Name
castName = 'castEffect
