module Brisk.Model.Builtins where
import PrelNames
import Name

import Data.Maybe
import Brisk.Model.Types
import Brisk.Model.GhcInterface

($->$) b e = ELam b e ()
infixr $->$

($>>=$) e1 e2 = EPrimOp Bind [e1,e2] ()
ret e = EPrimOp Return [e] ()
v x = EVar x ()

thenWiredIn :: EffExpr Id ()       
thenWiredIn
  = "a" $->$ "b" $->$ "m" $->$ "n" $->$ (v "m" $>>=$ ("_" $->$ v "n"))

bindWiredIn :: EffExpr Id ()
bindWiredIn
  = "a" $->$ "b" $->$ "m" $->$ "n" $->$ (v "m" $>>=$ v "n")

returnWiredIn :: EffExpr Id ()
returnWiredIn
  = "a" $->$ "e" $->$ ret (v "e")

failWiredIn :: EffExpr Id ()
failWiredIn
  = "a" $->$ "e" $->$ (EPrimOp Fail [] ())

monadBuiltin =  [ (bindMName, bindWiredIn)
                , (thenMName, thenWiredIn)
                , (failMName, failWiredIn)
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
                EPrimOp Send [ EType (TyVar "t") Nothing
                             , EVar "p" (Just pidType)
                             , EVar "m" (Just (TyVar "t"))
                             ]
                (Just (procType unitType))
                ) (Just $ TyFun (TyVar "t") (procType unitType))
            ) (Just $ TyFun pidType (TyFun (TyVar "t") (procType unitType)))
        ) Nothing

  , "Control.Distributed.Process.Internal.Primitives.getSelfPid"
    :<=:
    EPrimOp Self [] (Just (procType pidType))
    
  , "Control.Distributed.Process.Internal.Primitives.expect"
    :<=:
    ELam "t" (EPrimOp Recv [EType (procType (TyVar "t")) Nothing]
              (Just  (procType (TyVar "t"))))
             Nothing

  , "Control.Distributed.Process.SymmetricProcess.spawnSymmetric"
    :<=:
    ELam "nodes" (
      ELam "p" (
          (EPrimOp SymSpawn [EVar "p" Nothing] (Just (procType (TyConApp "Control.Distributed.Process.SymmetricProcess.SymProcessSet" [] ))))
          ) Nothing
       ) Nothing

  , "Control.Distributed.BriskStatic.Internal.castEffect"
    :<=:
    ELam "a" (ELam "b"
      (ELam "x" (ELam "y" (EVar "y" Nothing) Nothing) Nothing)
      Nothing) Nothing

  , "GHC.Err.error"
    :<=:
    ELam "a" (ELam "s" (EPrimOp Fail [] (Just (TyVar "a"))) Nothing) Nothing

  , "Control.Monad.foldM"
    :<=:
    ELam "t" (
      ELam "m" (
          ELam "b" (
              ELam "a" (
                  ELam "f" (
                      ELam "base" (
                          ELam "xs" (
                              EPrimOp FoldM [ EVar "f" Nothing
                                            , EVar "base" Nothing
                                            , EVar "xs" Nothing
                                            ] (Just (TyVar "b"))
                              ) Nothing
                          ) Nothing
                      ) Nothing
                  ) Nothing
              ) Nothing
          ) Nothing
      ) Nothing
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
