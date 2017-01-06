module Match00 where

import Control.Distributed.Process

main :: Process ()
main = receiveWait [
    match f -- receive([match x:t1 -> f
            --         ,match x:t2 -> g
            --         ,match x:t3 -> h])  >>= \x -> ...
  , match g
  ]
  where
    f :: Int -> Process ()
    f x = return ()

    g :: String -> Process ()
    g x = return ()
