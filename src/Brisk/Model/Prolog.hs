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
import qualified GhcPlugins as GT

toBriskString :: (Show a, HasType a) => T.EffExpr T.Id a -> String
toBriskString = render . toBrisk                 

toBrisk :: (Show a, HasType a) => T.EffExpr T.Id a -> Doc
toBrisk e = fromIceT (runIceT e)

fromIceT :: [IceTProcess a] -> Doc
fromIceT ps
  = mkPar (fromIceTProcess <$> ps)

fromIceTProcess (Single pid stmt)
  = fromIceTStmt pid stmt
fromIceTProcess (ParIter pidset pid stmt)
  = undefined

fromIceTStmt :: ProcessId -> IceTStmt a -> Doc
fromIceTStmt pid s@(Seq _)
  = mkSeq (fromIceTStmt pid <$> ss)
  where
    (Seq ss) = flattenSeq s
fromIceTStmt pid (Send ty p m)
  = mkSend (prolog pid) [ prolog ty
                        , fromIceTPid  pid p
                        , fromIceTExpr pid m
                        ]
  where
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

fromIceTStmt pid (Case e cases _)
  = mkCases (prolog pid) (fromIceTExpr pid e) (goCase <$> cases)
  where
    goCase (e, s)
      = mkCase (prolog pid) (fromIceTExpr pid e) (fromIceTStmt pid s)

fromIceTPid _ (T.EVar v l)
  = prologPid v

fromIceTExpr _ (T.EVar v l)
  = prolog v
fromIceTExpr _ (T.EType t _)
  = prolog t
fromIceTExpr pid (T.ECon c es _)
  = compoundTerm c (fromIceTExpr pid <$> es)

mkSeq :: [Doc] -> Doc
mkSeq ds = compoundTerm "seq" [listTerms ds]

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

mkCases :: Doc -> Doc -> [Doc] -> Doc
mkCases pid x cases = compoundTerm "cases" ([pid, x, listTerms cases])

mkCase :: Doc -> Doc -> Doc -> Doc
mkCase pid e s = compoundTerm "case" [pid, e, s]

mkAction f n pid args
  = compoundTerm f (pid:(checkLen n args))

checkLen n ds
  = assert (length ds == n) ds

atom :: String -> Doc
atom = prolog  

---------
--
---------


listTerms :: [Doc] -> Doc
listTerms ds
  = brackets . hcat . punctuate comma $ ds

tupleTerms :: [Doc] -> Doc
tupleTerms ds
  = parens . hcat . punctuate comma $ ds

compoundTerm :: String -> [Doc] -> Doc
compoundTerm n ds
  = text n <> tupleTerms ds

class Prolog a where
  prolog    :: a -> Doc
  prologPid :: a -> Doc

instance Prolog String where
  prolog = text

  prologPid (s:ss)
    | isUpper s = compoundTerm "e_pid" [text (toLower s : ss)]
    | otherwise = compoundTerm "e_var" [text (s:ss)]

instance Prolog GT.Type where
  prolog t = text $ GT.showSDoc GT.unsafeGlobalDynFlags (GT.ppr t)
  prologPid = error "prologPid of Type"
