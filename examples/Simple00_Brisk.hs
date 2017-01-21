{-# LANGUAGE TemplateHaskell #-}
module Simple00_Brisk where
import Control.Distributed.Process
{-# ANN module () #-}


data Annotated = Foo | Bar

{-# ANN main 'send #-}
main :: Annotated
main = Foo
