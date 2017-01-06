{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Brisk.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Brisk.Plugin:main #-}
module Scratch where
import Control.Distributed.Process

main :: Process ProcessId 
main = do p <- spawnLocal $ do p <- expect
                               send p (0 :: Int)

          send p ()
          expect :: Process ProcessId
          main
