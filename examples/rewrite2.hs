module Rewrite2 where

{-


G[x <- m],Σ,D,x := recv() ==> G,Σ,D;x:=m,skip

p*:Fresh,G,Σ(P) |- D;havoc(A) ~~> A(p*)
---------------------------------------
G,Σ             |- for (p:P) do A(p) end

---------------------------------------
G,Π(p:P\p*).s(p) |- A || s(p*) ~~> D
-}
