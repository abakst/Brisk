module Brisk.Model.Builtins where
import PrelNames
import Name

import Data.Maybe
import Brisk.Model.Types
import Brisk.Model.GhcInterface

thenWiredIn :: EffExpr Id ()       
thenWiredIn = a $->$ b $->$ m $->$ n $->$ EBind (EVar m ()) (ELam "_" (EVar n ()) ()) ()
  where
    m = "m"
    n = "n"
    a = "a"
    b = "b"

bindWiredIn :: EffExpr Id ()
bindWiredIn
  = a $->$ b $->$ m $->$ n $->$ EBind (EVar m ()) (EVar n ()) ()
  where
    m = "$m"
    n = "$n"
    a = "$a"
    b = "$b"

returnWiredIn :: EffExpr Id ()
returnWiredIn
  = a $->$ e $->$ EReturn (var e ()) ()
  where
    a = "a"
    e = "e"

monadBuiltin =  [ (bindMName, bindWiredIn)
                , (thenMName, thenWiredIn)
                , (returnMName, returnWiredIn)
                ]   
pidType :: Type Id
pidType = TyConApp "Control.Distributed.Process.Internal.Types.ProcessId" []

procType :: Type Id -> Type Id
procType t = TyConApp "Control.Distribted.Process.Internal.Types.Process" [t]

unitType = TyConApp "GHC.Base.()" []  

builtin :: SpecTableIn
builtin = SpecTable [
    "Control.Distributed.Process.Internal.Primitives.send"
    :<=:
    ELam "t" (
        ELam "p" (
            ELam "m" (
                Send (EType (TyVar "t") Nothing)
                (EVar "p" (Just pidType))
                (EVar "m" (Just (TyVar "t")))
                (Just (procType unitType))
                ) (Just $ TyFun (TyVar "t") (procType unitType))
            ) (Just $ TyFun pidType (TyFun (TyVar "t") (procType unitType)))
        ) Nothing

  , "Control.Distributed.Process.Internal.Primitives.getSelfPid"
    :<=:
    Self (Just (procType pidType))
    
  , "Control.Distributed.Process.Internal.Primitives.expect"
    :<=:
    ELam "t" (Recv (EType (procType (TyVar "t")) Nothing)
                   (Just  (procType (TyVar "t"))))
             Nothing
  ]
{-
builtin :: [(String, String, EffExpr Id ())]
builtin = [ ("GHC.Num", "-", t $->$ x $->$ y $->$ EVal (pExpr v Eq (eMinus (pVar x ()) (pVar y ())) ()) ())
          , ("GHC.Num", "+", t $->$ x $->$ y $->$ EVal (pExpr v Eq (ePlus (pVar x ()) (pVar y ())) ()) ())
          , ("GHC.Types", "I#", x $->$ (EVar x ()))
          , ("GHC.Base", "$", t $->$ t $->$ x $->$ y $->$ EApp (EVar x ()) (EVar y ()) ())
          , ("GHC.Base", "fail", t $->$ x $->$ y $->$ (EVal (v, PTrue) ()))
          , ("GHC.Classes", "==", x $->$ y $->$ EVal (v, PTrue) ())
          , ("GHC.Prim", "void#", EVal (v, PTrue) ())
          , ("GHC.Tuple", "()", EVal (v, PTrue) ())
          , ("Control.Exception.Base", "patError", x $->$ EVal (v, PTrue) ())
          , ("GHC.CString", "unpackCString#", x $->$ EVal (v, PTrue) ())

          , ("Control.Distributed.Process.Internal.Primitives", "send",
             t $->$ x $->$ y $->$ EProcess (Send (var t ()) (var x ()) (var y ()) ()) (EVal (v, PTrue) ()) ())

          , ("Control.Distributed.Process.Internal.Primitives", "getSelfPid",
             EProcess (Self ()) (EVal (v, PTrue) ()) ())

          , ("Control.Distributed.Process", "spawnLocal",
             t $->$ EProcess (Spawn (var t ()) ()) (EVal (v, PTrue) ()) ())

          , ("Control.Distributed.Process.Internal.Primitives", "expect",
             t $->$ EProcess (Recv (var t ()) ()) (EVal (v, PTrue) ()) ())
          ]
  where
    v = vv
    x = "x"
    y = "y"
    t = "t"
-}
isMonadOp :: NamedThing a => a -> Bool
isMonadOp 
  = isJust . monadOp

monadOp :: NamedThing a => a -> Maybe (EffExpr Id ())  
monadOp f
  = lookup (getName f) monadBuiltin
