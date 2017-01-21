{-# LANGUAGE TemplateHaskell #-}
module AnnotateMe (foldl') where
import qualified Data.List as L

{-# ANN foldl' foldl_Annot #-}
foldl' :: Foldable f => (a -> b -> a) -> a -> f b -> a
foldl' = L.foldl'

{-# ANN x (3 :: Int) #-}
x :: Int
x = 3

foldl_Annot :: Int
foldl_Annot = 3
