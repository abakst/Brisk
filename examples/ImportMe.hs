{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
module ImportMe where
import Brisk.Annotations
{-# ANN module SpecModule #-}

{-# ANN ap_spec (Assume '($)) #-}
ap_spec :: (a -> b) -> a -> b
ap_spec f x = f x

{-# ANN flip_spec (Assume 'flip) #-}
flip_spec :: (a -> b -> c) -> b -> a -> c
flip_spec f x y = f y x
