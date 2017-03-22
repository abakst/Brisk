module Brisk.Model.Builtins where
import PrelNames
import Name

import Data.Maybe
import Brisk.Model.Types
import Brisk.Model.GhcInterface

($->$) b e = ELam b e ()
infixr $->$

($-->$) b e = ELam b e Nothing
infixr $-->$

($>>=$) e1 e2 = EPrimOp Bind [e1,e2] ()
ret e = EPrimOp Return [e] ()
v x = EVar x ()

thenWiredIn :: EffExpr Id ()       
thenWiredIn
  = "A" $->$ "B" $->$ "m" $->$ "n" $->$ (v "m" $>>=$ ("_" $->$ v "n"))

bindWiredIn :: EffExpr Id ()
bindWiredIn
  = "A" $->$ "B" $->$ "m" $->$ "n" $->$ (v "m" $>>=$ v "n")

returnWiredIn :: EffExpr Id ()
returnWiredIn
  = "A" $->$ "e" $->$ ret (v "e")

failWiredIn :: EffExpr Id ()
failWiredIn
  = "A" $->$ "e" $->$ (EPrimOp Fail [] ())

monadBuiltin =  [ (nameId bindMName, bindWiredIn)
                , (nameId thenMName, thenWiredIn)
                , (nameId failMName, failWiredIn)
                , (nameId returnMName, returnWiredIn)
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
    ELam "T" (
        ELam "p" (
            ELam "m" (
                EPrimOp Send [ EType (TyVar "T") Nothing
                             , EVar "p" (Just pidType)
                             , EVar "m" (Just (TyVar "T"))
                             ]
                (Just (procType unitType))
                ) (Just $ TyFun (TyVar "T") (procType unitType))
            ) (Just $ TyFun pidType (TyFun (TyVar "T") (procType unitType)))
        ) Nothing

  , "Control.Distributed.Process.Internal.Primitives.getSelfPid"
    :<=:
    EPrimOp Self [] (Just (procType pidType))
    
  , "Control.Distributed.Process.Internal.Primitives.expect"
    :<=:
    ELam "T" (EPrimOp Recv [EType (TyVar "T") Nothing]
              (Just  (procType (TyVar "T"))))
             Nothing

  , "Control.Distributed.Process.Internal.Spawn.spawn"
    :<=:
    ELam "node" (
      ELam "p" (
         (EPrimOp Spawn [EVar "p" Nothing] (Just (procType pidType)))
         ) Nothing
      ) Nothing
   
  , "Control.Distributed.Process.SymmetricProcess.spawnSymmetric"
    :<=:
    ELam "nodes" (
      ELam "p" (
          (EPrimOp SymSpawn [EVar "nodes" Nothing, EVar "p" Nothing] (Just (procType (TyConApp "Control.Distributed.Process.SymmetricProcess.SymProcessSet" [] ))))
          ) Nothing
       ) Nothing

  , "Control.Distributed.Process.SymmetricProcess.chooseSymmetric"
    :<=:
    ELam "A" (ELam "set" (ELam "_" (ESymElt (EVar "set" Nothing) (Just (TyVar "A"))) Nothing) Nothing) Nothing

  , "Control.Distributed.BriskStatic.Internal.castEffect"
    :<=:
    ELam "A" (ELam "B"
      (ELam "x" (ELam "y" (EVar "y" Nothing) Nothing) Nothing)
      Nothing) Nothing

  , "GHC.Err.error"
    :<=:
    ELam "R" (
      ELam "A" (ELam "s" (EPrimOp Fail [] (Just (TyVar "A"))) Nothing) Nothing
      ) Nothing

  , "Control.Distributed.Process.SymmetricProcess.expectFrom"
    :<=:
    ELam "A" (
      ELam "p" (
          EPrimOp Bind
             [ EPrimOp Recv [ EType (TyConApp "Control.Distributed.Process.SymmetricProcess.SelfSigned" [TyVar "A"]) Nothing
                            , EVar "p" (Just pidType)
                            ] (Just (procType (TyVar "A")))
             , ELam "msg" (ECase
                           (TyVar "A")
                           (EVar "msg" Nothing)
                           [ ( "Control.DistributedProcess.SymmetricProcess.SelfSigned"
                             , ["X", "pay"]
                             , EPrimOp Return [EVar "pay" (Just (TyVar "A"))] Nothing
                             )
                           ]
                           Nothing
                           Nothing) Nothing
             ] Nothing
          ) Nothing
      ) Nothing

  , "Control.Distributed.Process.SymmetricProcess.selfSign"
    :<=:
    let ret = ECon ty
                   [ EVar "me" Nothing, EVar "m" (Just (TyVar "A")) ]
                   (Just (TyConApp ty [TyVar "A"]))
        ty = "Control.DistributedProcess.SymmetricProcess.SelfSigned"
    in
    ELam "A" (
      ELam "m" (
          EPrimOp Bind [ EPrimOp Self [] Nothing
                       , ELam "me" (EPrimOp Return [ret] Nothing) Nothing
                       ] Nothing
          ) Nothing
      ) Nothing

  , "Control.Monad.foldM"
    :<=:
    ELam "T" (
      ELam "M" (
          ELam "B" (
              ELam "A" (
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

    , "Data.Traversable.forM"
      :<=:
      ("T" $-->$ "M"
           $-->$ "B"
           $-->$ "A"
           $-->$ "xs"
           $-->$ "f"
           $-->$ EPrimOp FoldM [ "a" $-->$ "x" $-->$ 
                                 EPrimOp Bind [
                                   EApp (EVar "f" Nothing)
                                   (EVar "x" Nothing)
                                   Nothing
                                 , "_" $-->$ EVal Nothing Nothing
                                 ] Nothing
                               , EAny (EType (TyVar "B") Nothing) Nothing
                               , EVar "xs" Nothing
                               ] Nothing
      )
                    

    , "Brisk.Annotations.top"
      :<=:
      ELam "A" (EAny (EType (TyVar "A") Nothing) Nothing) Nothing

    , "GHC.Base.fail"
      :<=:
      ELam "M" (ELam "A" (ELam "e" (EPrimOp Fail [] Nothing) Nothing) Nothing) Nothing
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
  = lookup (nameId $ getName f) monadBuiltin
