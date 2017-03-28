{-# LANGUAGE ImplicitParams #-}
module Brisk.UX where
import GHC.Stack
import Text.Show.Pretty (ppShow)

abort :: (?callStack :: CallStack, Show a) => String -> a -> b
abort msg x
  = error $  unlines [ "\n********** BRISK ERROR **********"
                     , msg ++ ":\n" ++ ppShow x
                     , "*********************************"
                     ]
