module Brisk.UX where
import Text.Show.Pretty (ppShow)

abort :: Show a => String -> a -> b
abort msg x
  = error $  unlines [ "********** BRISK ERROR **********"
                     , msg ++ ": " ++ ppShow x
                     , "*********************************"
                     ]
