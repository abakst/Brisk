module Brisk.Pretty (render, text, Pretty(..)) where

import Text.PrettyPrint.HughesPJ

class Pretty a where
  pp :: a -> Doc
