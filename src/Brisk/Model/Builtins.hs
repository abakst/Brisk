module Brisk.Model.Builtins where
import PrelNames
import Name

import Data.Maybe
import Brisk.Model.Types
import Brisk.Model.GhcInterface

thenWiredIn :: EffExpr Name ()       
thenWiredIn = a $->$ b $->$ m $->$ n $->$ EBind (EVar m ()) (EVar n ()) ()
  where
    m = builtinName (-1)
    n = builtinName (-2)
    a = builtinName (-3)
    b = builtinName (-4)

bindWiredIn :: EffExpr Name ()
bindWiredIn
  = a $->$ b $->$ m $->$ n $->$ EBind (EVar m ()) (EVar n ()) ()
  where
    m = builtinName (-1)
    n = builtinName (-2)
    a = builtinName (-3)
    b = builtinName (-4)

returnWiredIn :: EffExpr Name ()
returnWiredIn
  = a $->$ e $->$ EReturn (var e) ()
  where
    a = builtinName (-3)
    e = builtinName (-4)

monadBuiltin =  [ (bindMName, bindWiredIn)
                , (thenMName, thenWiredIn)
                , (returnMName, returnWiredIn)
                ]   

builtin :: [(String, String, EffExpr Name ())]
builtin = [ ("GHC.Num", "-", x $->$ y $->$ EVal (v, PTrue) ())
          , ("GHC.Num", "+", x $->$ y $->$ EVal (v, PTrue) ())
          , ("GHC.Types", "I#", x $->$ EVal (v, PTrue) ())
          , ("GHC.Classes", "==", x $->$ y $->$ EVal (v, PTrue) ())
          , ("GHC.Prim", "void#", EVal (v, PTrue) ())
          , ("GHC.Tuple", "()", EVal (v, PTrue) ())
          , ("Control.Exception.Base", "patError", x $->$ EVal (v, PTrue) ())

          , ("Control.Distributed.Process.Internal.Primitives", "send",
             t $->$ x $->$ y $->$ EProcess (Send (var x) (var y)) (EVal (v, PTrue) ()) ())

          , ("Control.Distributed.Process.Internal.Primitives", "expect",
             t $->$ EProcess (Recv (var t)) (EVal (v, PTrue) ()) ())
          -- , ("Control.Distributed", "spawn",  undefined)
          ]
  where
    v = builtinName (0) 
    x = builtinName (-2)
    y = builtinName (-3)
    t = builtinName (-1)

isMonadOp :: NamedThing a => a -> Bool
isMonadOp 
  = isJust . monadOp

monadOp :: NamedThing a => a -> Maybe (EffExpr Name ())  
monadOp f
  = lookup (getName f) monadBuiltin
