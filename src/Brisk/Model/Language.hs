{-# Language GADTs #-}
module Brisk.Model.Language where

import Control.Monad.State
import Type
import SrcLoc

type Id       = String
data Binder a = Bind Id a
data AbsExpr a = Pure (AbsVal a)
               | Lam (Binder a) (AbsExpr a) a
               | Return (AbsVal a)

data AbsVal a = Top a                 
type LocExpr = AbsExpr SrcSpan

class Subst a where               
  sub :: Var -> Var -> a

pure :: AbsVal SrcSpan -> LocExpr
pure = Pure

top :: SrcSpan -> AbsVal SrcSpan
top l = Top l

app :: LocExpr -> LocExpr -> LocExpr
app (Lam x m l) e
  = undefined

-- prim :: s -> AbsVal p s a (p c)  
-- prim = Prim

-- return :: AbsVal p s a (a c) -> AbsVal p s a (p c)
-- return = Return

-- bind :: Binder
--      -> AbsVal p s a (p c)
--      -> AbsVal p s a (c -> p d)
--      -> AbsVal p s a (p d)
-- bind = Bind
