{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
module Brisk.Pretty (
    render
  , text
  , parensIf
  , Pretty(..)
  ) where

import Text.PrettyPrint.HughesPJ

class Pretty a where
  pp :: a -> Doc
  pp = ppPrec 0

  ppPrec :: Int -> a -> Doc

instance Pretty String where
  ppPrec _ = text

instance Pretty a => Pretty [a] where
  ppPrec z l = brackets (vcat (ppPrec z <$> l))

parensIf :: Bool -> Doc -> Doc
parensIf b d | b = parens d
parensIf _ d     = d
