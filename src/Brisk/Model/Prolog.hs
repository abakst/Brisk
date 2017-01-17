{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Brisk.Model.Prolog where

import           Name
import           OccName
import           Text.PrettyPrint.HughesPJ
import           Control.Exception
import           Data.Char
import qualified Brisk.Model.Types as T
import           Brisk.Model.Types (Id)
import           Brisk.Model.IceT
import           Brisk.Model.GhcInterface
import           Brisk.Pretty
import           Brisk.UX
import qualified GhcPlugins as GT

---------------------------------------------------
toBriskString :: (Show a, HasType a) => T.EffExpr T.Id a -> String
---------------------------------------------------
toBriskString = render . toBrisk                 

---------------------------------------------------
toBrisk :: (Show a, HasType a) => T.EffExpr T.Id a -> Doc
---------------------------------------------------
toBrisk e = fromIceT (runIceT e)

---------------------------------------------------
fromIceT :: (Show a, HasType a) => [IceTProcess a] -> Doc
---------------------------------------------------
fromIceT ps
  = mkPar (fromIceTProcess <$> ps)

---------------------------------------------------
fromIceTProcess :: (Show a, HasType a) => IceTProcess a -> Doc
---------------------------------------------------
fromIceTProcess (Single pid stmt)
  = fromIceTStmt pid stmt
fromIceTProcess (ParIter pid pidset stmt)
  = mkSym (prolog pid) (mkPidSet pidset) (fromIceTStmt pid stmt)

---------------------------------------------------
fromIceTStmt :: (Show a, HasType a) => ProcessId -> IceTStmt a -> Doc
---------------------------------------------------
fromIceTStmt pid s@(Seq _)
  = mkSeq (fromIceTStmt pid <$> ss)
  where
    (Seq ss) = flattenSeq s

fromIceTStmt pid (Send _ p m)
  = mkSend (prolog pid) [ prolog (getType m)
                        , fromIceTPid  p
                        , fromIceTExpr pid m
                        ]
fromIceTStmt pid Skip
  = mkSkip

fromIceTStmt pid (Recv ty my)
  = mkRecv (prolog pid) [ mkType [prolog ty]
                        , y
                        ]
  where
    y = case my of
          Nothing -> prolog "nil"
          Just y  -> prolog y

fromIceTStmt pid (Assgn x _ e)
  = mkAssign (prolog pid) [prolog x, fromIceTExpr pid e]

fromIceTStmt pid (Case e cases d)
  = mkCases (prolog pid) (fromIceTExpr pid e) pCases 
  where
    pCases
      = (goCase <$> cases) ++ defaultCase
    goCase (e, s)
      = mkCase ppid (fromIceTExpr pid e) (fromIceTStmt pid s)
    defaultCase
      = maybe [] (return . mkDefaultCase ppid . fromIceTStmt pid) d
    ppid = prolog pid

fromIceTStmt pid (While s)    
  = mkWhile (prolog pid) [fromIceTStmt pid s]

fromIceTStmt pid Continue
  = mkContinue

fromIceTStmt pid (ForEach x xs s)
  = mkForEach (prolog pid) [ prolog x
                           , fromIceTPidSet xs
                           , fromIceTStmt pid s
                           ]

fromIceTPid (T.EVar v l)
  = prologPid v

fromIceTPidSet (T.EVar v _)
  = mkPidSet v

---------------------------------------------------
fromIceTExpr :: (Show a, HasType a) => ProcessId -> IceTExpr a -> Doc
---------------------------------------------------
fromIceTExpr _ (T.EVar v l)
  = prolog v
fromIceTExpr _ (T.EType t _)
  = prolog t
fromIceTExpr pid (T.ECon c es _)
  = compoundTerm c (fromIceTExpr pid <$> es)
fromIceTExpr pid (T.ECase t e alts d l)
  = mkCases (prolog pid) (fromIceTExpr pid e) cases
  where
    cases
      = (goCase <$> alts) ++
        maybe [] (return . mkDefaultCase ppid . fromIceTExpr pid) d
    goCase (c,xs,e)
      = mkCase ppid (fromIceTExpr pid (T.ECon c (flip T.EVar l <$> xs) l))
                    (fromIceTExpr pid e)
    ppid = prolog pid
fromIceTExpr pid (T.EField e i _)
  = mkField (prolog pid) [fromIceTExpr pid e, prolog i]
fromIceTExpr pid e
  = abort "fromIceTExpr" e

mkPidSet (s0:s)  
  = compoundTerm "set" [prolog (toLower s0 : s)]

mkField :: Doc -> [Doc] -> Doc
mkField = mkAction "field" 2

mkSym :: Doc -> Doc -> Doc -> Doc
mkSym p set act = compoundTerm "sym" [p,set,act]

mkSeq :: [Doc] -> Doc
mkSeq ds = compoundTerm "seq" [listTerms ds]

mkAssign :: Doc -> [Doc] -> Doc
mkAssign = mkAction "assign" 2

mkPar :: [Doc] -> Doc
mkPar ds = compoundTerm "par" [listTerms ds]

mkType :: [Doc] -> Doc
mkType = compoundTerm "type" . checkLen 1

mkSend :: Doc -> [Doc] -> Doc  
mkSend = mkAction "send" 3

mkRecv :: Doc -> [Doc] -> Doc
mkRecv = mkAction "recv" 2

mkSkip :: Doc
mkSkip = prolog "skip"

mkContinue :: Doc
mkContinue = prolog "continue"

mkWhile :: Doc -> [Doc] -> Doc  
mkWhile = mkAction "while" 1

mkForEach :: Doc -> [Doc] -> Doc
mkForEach = mkAction "for" 3

mkCases :: Doc -> Doc -> [Doc] -> Doc
mkCases pid x cases = compoundTerm "cases" [pid, x, listTerms cases]

mkCase :: Doc -> Doc -> Doc -> Doc
mkCase pid e s = compoundTerm "case" [pid, e, s]

mkDefaultCase :: Doc -> Doc -> Doc
mkDefaultCase pid s = compoundTerm "case" [ pid
                                          , compoundTerm "default" []
                                          , s
                                          ]

mkAction f n pid args
  = compoundTerm f (pid : checkLen n args)

checkLen n ds
  = assert (length ds == n) ds

atom :: String -> Doc
atom = prolog  

---------
--
---------

listTerms :: [Doc] -> Doc
listTerms = brackets
          . (space <>)
          . vcat
          . punctuate (comma<>space)

tupleTerms :: [Doc] -> Doc
tupleTerms = parens . hcat . punctuate (comma<>space)

compoundTerm :: String -> [Doc] -> Doc
compoundTerm n ds
  = text n <> tupleTerms ds

class Prolog a where
  prolog    :: a -> Doc
  prologPid :: a -> Doc

instance Prolog String where
  prolog = text

  prologPid pid@(s:_)
    | isUpper s = compoundTerm "e_pid" [text pid]
    | otherwise = compoundTerm "e_var" [text pid]

instance Prolog Int where
  prolog    = int
  prologPid = abort "prologPid" "prologPid of Int"

instance Prolog GT.Type where
  prolog t = text $ GT.showSDoc GT.unsafeGlobalDynFlags (GT.ppr t)
  prologPid = error "prologPid of Type"
