{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Brisk.Model.Prolog where

import           Name
import           OccName
import           Text.PrettyPrint.HughesPJ
import           Control.Exception
import           Data.Char
import           Data.List
import           Data.Maybe
import qualified Brisk.Model.Types as T
import           Brisk.Model.Types (Id)
import           Brisk.Model.IceT
import           Brisk.Model.GhcInterface
import           Brisk.Pretty
import           Brisk.UX
import qualified GhcPlugins as GT

---------------------------------------------------
toBriskString :: (Show a, HasType a, T.Annot a) => T.EffExpr T.Id a -> String
---------------------------------------------------
toBriskString = render . toBrisk                 

---------------------------------------------------
toBrisk :: (Show a, HasType a, T.Annot a) => T.EffExpr T.Id a -> Doc
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

fromIceTStmt pid (Send t p m)
  = mkSend (prolog pid) [ prolog t
                        , fromIceTPid pid p
                        , fromIceTExpr pid m
                        ]
fromIceTStmt pid Skip
  = mkSkip

fromIceTStmt pid (Recv ty w my)
  = mkRecv (prolog pid) (wc ++ [ mkType [prolog ty], y])
  where
    wc = maybe [] (return . fromIceTExpr pid) w
    y = case my of
          Nothing -> prolog "_"
          Just y  -> prolog y

fromIceTStmt pid (Assgn x _ e)
  = mkAssign (prolog pid) [prolog x, fromIceTExpr pid e]

fromIceTStmt pid (Case e cases d)
  = mkCases (prolog pid) (fromIceTExpr pid e) pCases defaultCase
  where
    pCases
      = goCase <$> cases
    goCase (e, s)
      = mkCase ppid (fromIceTExpr pid e) (fromIceTStmt pid s)
    defaultCase
      = (mkDefault ppid . fromIceTStmt pid) <$> d
    ppid = prolog pid

fromIceTStmt pid (While s)    
  = mkWhile (prolog pid) [fromIceTStmt pid s]

fromIceTStmt pid Continue
  = mkContinue

fromIceTStmt pid (ForEach x xs s)
  = mkForEach (prolog pid) [ prolog x
                           , fromIceTPidSet pid xs
                           , fromIceTStmt pid s
                           ]

fromIceTStmt pid Fail
  = mkFail (prolog pid)

fromIceTPid pid (T.EVar v l)
  = prologPid v
fromIceTPid pid (T.ESymElt e l)
  = fromIceTPidSet pid e
fromIceTPid pid e
  = prologPid (fromIceTExpr pid e)

fromIceTPidSet pid (T.EVar v _)
  = mkPidSet v
fromIceTPidSet pid e
  = mkPidSet (fromIceTExpr pid e)

---------------------------------------------------
fromIceTExpr :: (Show a, HasType a)
             => ProcessId -> IceTExpr a -> Doc
---------------------------------------------------
fromIceTExpr _ (T.EVal (Just (T.CInt i)) _)
  = prolog i
fromIceTExpr _ (T.EAny t l)
  = prolog "_"
fromIceTExpr _ (T.EVar v l)
  = prolog v
fromIceTExpr _ (T.EType t _)
  = prolog t
fromIceTExpr pid (T.ECon c [] _)
  = prolog (cstrId c)
fromIceTExpr pid (T.ECon c es _)
  = compoundTerm (cstrId c) (fromIceTExpr pid <$> es)
fromIceTExpr pid (T.ECase t e alts d l)
  = mkCases (prolog pid) (fromIceTExpr pid e) cases dflt
  where
    cases
      = goCase <$> alts
    dflt
      = (mkDefault ppid . fromIceTExpr pid) <$> d
    goCase (c,xs,e)
      = mkCase ppid (fromIceTExpr pid (T.ECon c (flip T.EVar l <$> xs) l))
                    (fromIceTExpr pid e)
    ppid = prolog pid
fromIceTExpr pid (T.EField e i _)
  = mkField (prolog pid) [fromIceTExpr pid e, prolog i]
fromIceTExpr pid (T.ESymElt e _)
  = compoundTerm "nonDet" [prolog pid, fromIceTExpr pid e]
fromIceTExpr pid (T.EApp e1 e2 l)
  | Just t <- getType l
  = fromIceTExpr pid (T.EAny (T.EType t l) l)
fromIceTExpr pid e
  = abort "fromIceTExpr" e

mkPidSet s  
  = compoundTerm "set" [prolog s]

mkFail :: Doc -> Doc
mkFail p = compoundTerm "die" [p]

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

mkCases :: Doc -> Doc -> [Doc] -> Maybe Doc -> Doc
mkCases pid x cases d
  = compoundTerm "cases" ([pid, x, listTerms cases] ++ d')
  where
    d' = maybe [] return d

mkCase :: Doc -> Doc -> Doc -> Doc
mkCase pid e s = compoundTerm "case" [pid, e, s]

mkDefault :: Doc -> Doc -> Doc
mkDefault pid s = compoundTerm "default" [pid, s]

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
  = prolog n <> tupleTerms ds

class Prolog a where
  prolog     :: a -> Doc
  prologPid  :: a -> Doc

instance Prolog Doc where
  prolog    = id
  prologPid = id

instance Prolog String where
  prolog = text
         . (concatMap repl)
         . last
         . textNoDots
    where
      repl '\'' = "_"
      repl '.'  = "__"
      repl c    = [c]

  prologPid pid@(s:_)
    | isUpper s = compoundTerm "e_pid" [text pid]
    | otherwise = compoundTerm "e_var" [text pid]

cstrId = makeLower "cstr__"
typeId = makeLower "ty__"

makeLower :: String -> String -> String
makeLower pre  s
  = intercalate "." (hd ++ [pre ++ lst])
  where
    lst :: String
    lst = last ss
    hd = init ss
    ss :: [String]
    ss = textNoDots s

instance Prolog Int where
  prolog    = int
  prologPid = abort "prologPid" "prologPid of Int"

instance Prolog GT.Type where
  prolog t = text $ GT.showSDoc GT.unsafeGlobalDynFlags (GT.ppr t)
  prologPid = error "prologPid of Type"

instance Prolog b => Prolog (T.Type b) where
  prologPid = abort "prologPid" "prologPid of Type"
  prolog (T.TyVar v)
    = compoundTerm "tyVar" [prolog v]
  prolog (T.TyApp t1 t2)
    = compoundTerm "tyApp" [prolog t1, prolog t2]
  prolog (T.TyFun t1 t2)
    = compoundTerm "tyFun" [prolog t1, prolog t2]
  prolog (T.TyConApp t [])
    = compoundTerm "tyCon" [text "ty__" <> prolog t]
  prolog (T.TyConApp t ts)
    = compoundTerm "tyCon" ((text "ty__" <> prolog t) : fmap prolog ts)
