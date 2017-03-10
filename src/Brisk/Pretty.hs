{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Brisk.Pretty (
    render
  , text
  , parensIf
  , Pretty(..)
  , textNoDots
  , modulePrefix
  ) where

import Text.PrettyPrint.HughesPJ
import Data.List (intercalate)

class Pretty a where
  pp :: a -> Doc
  pp = ppPrec 0

  ppPrec :: Int -> a -> Doc
  ppPrec _ a = pp a

instance Pretty String where
  ppPrec _ = text . last . textNoDots

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
  ppPrec z l = brackets (vcat (ppPrec z <$> l))

parensIf :: Bool -> Doc -> Doc
parensIf b d | b = parens d
parensIf _ d     = d

textNoDots :: String -> [String]
textNoDots s
  = case dropWhile isDot s of
      "" -> []
      s' -> w : textNoDots s''
        where
          (w, s'') = break isDot s'
  where
    isDot c = c == '.'

modulePrefix :: String -> (String, String)
modulePrefix s = modulePrefix' [] s
  where
    modulePrefix' acc s
      = case break isDot s of
          (m,"") -> (intercalate "." $ reverse acc, m)
          (m,s') -> modulePrefix' (m:acc) (dropWhile isDot s')
      where
        isDot c = c == '.'
