{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
module Brisk.Model.Prolog where

import           Name
import           GHC.Stack
import           OccName
import           Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as Doc
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
import           Text.Show.Pretty
import           Paths_brisk 
import           Text.Printf
import           Turtle hiding (printf, text, (<>), space)
import           Turtle.Format hiding (printf)

import Debug.Trace       

--------------------------------------------------
runRewriter :: (HasType l, T.Annot l, Show l)
            => T.EffExpr Id l -> Maybe String -> IO ()
--------------------------------------------------
runRewriter e mdest
  = do rw <- getDataFileName "rewrite.pl"
       sh $ do
         tmp  <- using (mktempfile "." "brisk_query")
         let query   = template tmp
             (inp,rem) = toBrisk e
             rwquery   = queryTemplate (fromString (render inp)) (fromString (render rem))
             cmd     = format ( "sicstus -l " % s
                              % " --goal "    % w
                              % " --noinfo --nologo "
                              % "2>/dev/null "
                              % "1>/dev/null "
                              ) (fromString rw) query
         output tmp (select $ textToLines rwquery)
         l <- select $ textToLines cmd
         echo l
         maybe (return ()) (saveTemp tmp) mdest
         status <- shell cmd empty
         reportStatus status
         case status of
           ExitSuccess   -> return ()
           ExitFailure _ -> cp tmp "./query_failed"
         exit status
  where
    saveTemp f g = cp f (fromString g)

reportStatus = echo . statusMsg

notSND = 3               
notDLFree = 4

statusMsg :: ExitCode -> Line
statusMsg ExitSuccess
  = "\x1b[1;32mOK\x1b[0m"
statusMsg (ExitFailure c)
  | c == notSND
  = "\x1b[1;31mUNSAFE: Not SND\x1b[0m"
  | c == notDLFree
  = "\x1b[1;31mUNSAFE: Possible Deadlock\x1b[0m"
  | otherwise
  = "\x1b[1;31mERROR: Unexpected Status!\x1b[0m"

queryTemplate t r
  = format("rewrite_query(T,Rem) :- \nRem="%s%",\nT="%s%".") r t

-- template :: String -> String -> String -> String
template tmp
  = format ( "consult('"%fp%"'),"
           % "rewrite_query(T,R),"
           % s
           % "halt(0)."
           ) tmp check
  where
    check = format ("("%s%", ("%s%"; halt("%d%")) ; halt("%d%")),") rf rw notDLFree notSND
    rf = format ("catch(check_race_freedom(T,T1),_,halt("%d%")),!") notSND
    rw = format ("catch(rewrite(T1,R,_,_),_,halt("%d%"))") notDLFree
    
data BriskAnnot a = BriskAnnot { isPatternVar :: Bool
                               , annot        :: a
                               }
                  deriving Show

instance (Show a, T.Annot a) => T.Annot (BriskAnnot a) where
  dummyAnnot = BriskAnnot False T.dummyAnnot
instance (Show a, HasType a) => HasType (BriskAnnot a) where
  getType     = getType . annot
  setType t a = a { annot = setType t (annot a) }
         
---------------------------------------------------
findForever :: (Show a, HasType a, T.Annot a)
            => ProcessId -> IceTStmt (BriskAnnot a) -> Maybe Doc
---------------------------------------------------
findForever pid st@(While l s)
  | alwaysContinues l s
  = Just $ mkWhile (prolog pid) [ prolog l <> equals <> int 1
                                , fromIceTStmt pid body
                                ]
  | otherwise
  = Nothing
  where
    assgn = Assgn l Nothing (T.EVal (Just (T.CInt 0)) T.dummyAnnot)
    body = seqStmts [ assgn, s ]
findForever pid (Seq ss)
  = findForever pid (last ss)
findForever _ _
  = Nothing

alwaysContinues l (Continue l')
  = l == l'
alwaysContinues l (Seq ss)
  = let s' = last ss in alwaysContinues l s'
alwaysContinues l (Case _ alts d)
  = all (alwaysContinues l) ((snd <$> alts) ++ maybe [] return d)
alwaysContinues l _
  = False

---------------------------------------------------
toBriskString :: (Show a, HasType a, T.Annot a) => T.EffExpr T.Id a -> String
---------------------------------------------------
toBriskString = render . fst . toBrisk

---------------------------------------------------
toBrisk :: (Show a, HasType a, T.Annot a) => T.EffExpr T.Id a -> (Doc, Doc)
---------------------------------------------------
toBrisk e = fromIceT procs
  where
    (_, procs)    = runIceT (toBriskAnnot <$> e)
    toBriskAnnot a = BriskAnnot False a

---------------------------------------------------
fromIceT :: (Show a, HasType a, T.Annot a) => [IceTProcess (BriskAnnot a)] -> (Doc, Doc)
---------------------------------------------------
fromIceT ps
  = (par, rem)
  where
    par           = mkPar docs
    rem           = case rems of
                      []  -> mkSkip
                      [r] -> r
                      _   -> mkPar rems
    rems          = catMaybes mrems
    (docs, mrems) = unzip (fromIceTProcess <$> ps)

---------------------------------------------------
fromIceTProcess :: (Show a, HasType a, T.Annot a) => IceTProcess (BriskAnnot a) -> (Doc, Maybe Doc)
---------------------------------------------------
fromIceTProcess (Single pid stmt)
  = (st, rem)
  where
    st  = fromIceTStmt pid s
    rem = findForever pid s 
    s   = pullCaseAssignStmt stmt
fromIceTProcess (ParIter pid pidset stmt)
  = (st, rem)
  where
    mkSet = mkSym (prolog pid) (mkPidSet pidset)
    st    = mkSet (fromIceTStmt pid s)
    rem   = mkSet <$> findForever pid s
    s     = pullCaseAssignStmt stmt

pullCaseAssignStmt :: (Show a, HasType a) => IceTStmt a -> IceTStmt a  
pullCaseAssignStmt (Case e alts d)
  = Case e (goAlt <$> alts) (pullCaseAssignStmt <$> d)
  where
    goAlt (e,s) = (e, pullCaseAssignStmt s)
pullCaseAssignStmt (Seq ss)
  = Seq (pullCaseAssignStmt <$> ss)
pullCaseAssignStmt (ForEach x xs s)
  = ForEach x xs (pullCaseAssignStmt s)
pullCaseAssignStmt (While l s)
  = While l (pullCaseAssignStmt s)
pullCaseAssignStmt (Assgn x t (T.ECase ty e alts d l))
  = Case e stmtAlts stmtDflt
  where
    mkCon c xs = T.ECon c (flip T.EVar l <$> xs) l
    stmtAlts   = [ (mkCon c xs, Assgn x t e) | (c,xs,e) <- alts ]
    stmtDflt   = Assgn x t <$> d
pullCaseAssignStmt s
  = s

---------------------------------------------------
fromIceTStmt :: (?callStack :: CallStack, Show a, HasType a, T.Annot a)
             => ProcessId -> IceTStmt (BriskAnnot a) -> Doc
---------------------------------------------------
fromIceTStmt pid s@(Seq _)
  = mkSeq (fromIceTStmt pid <$> ss)
  where
    (Seq ss) = flattenSeq s

fromIceTStmt pid (Send t p m)
  = mkSend (prolog pid) [ fromIceTPid pid p
                        , prolog t
                        , fromIceTExpr pid m
                        ]
fromIceTStmt pid Skip
  = mkSkip

fromIceTStmt pid (Recv ty w my)
  = mkRecv (prolog pid) (wc ++ [t, y])
  where
    wc = maybe [] (return . fromIceTPid pid) w
    t  = maybe (mkType [prolog ty]) (const (prolog ty)) w
    y = case my of
          Nothing  -> prolog ("dev_null__" :: String)
          Just "_" -> prolog ("dev_null__" :: String)
          Just y   -> prolog y

fromIceTStmt pid (Assgn x _ (T.ESymElt e _))
  = compoundTerm "nondet" [
         prolog (liftCase x)
       , fromIceTPidSet pid e
       , mkAssign (prolog pid) [prolog x, prolog (liftCase x) ]
    ]

fromIceTStmt pid (Assgn x _ (T.EVal Nothing _))
  = Doc.empty
fromIceTStmt pid (Assgn x _ (T.EAny _ _))
  = Doc.empty
fromIceTStmt pid (Assgn x _ e)
  = mkAssign (prolog pid) [prolog var, fromIceTExpr pid e]
  where
    var | x == "_"  = "null"
        | otherwise = x

fromIceTStmt pid (Case e cases d)
  = mkCases (prolog pid) (fromIceTExpr pid e) pCases defaultCase
  where
    pCases
      = goCase <$> cases
    goCase (pat@(T.ECon c xs l), s)
      = mkCase ppid (fromIceTExpr pid pat) (fromIceTStmt pid s)
      -- where
        -- s'  = foldl' (\s (x,x') -> substStmt x x' s) s (zip bs xs')
        -- e'  = T.ECon c xs' l
        -- bs  = T.varId <$> xs
        -- xs' = [ T.EVar v l { isPatternVar = True } | v <- bs ]
    defaultCase
      = (mkDefault ppid . fromIceTStmt pid) <$> d
    ppid = prolog pid

fromIceTStmt pid (While l s)    
  = mkSeq [ fromIceTStmt pid (assgn 1)
          , mkWhile (prolog pid) [ prolog l <> equals <> int 1
                                 , fromIceTStmt pid body
                                 ]
          ]
  where
    a       = T.dummyAnnot
    assgn b = Assgn l Nothing (T.EVal (Just (T.CInt b)) a)
    body    = seqStmts [ assgn 0, s ]

fromIceTStmt pid (Continue l)
  = mkAssign (prolog pid) [prolog l, mkTrue]

fromIceTStmt pid (ForEach x (True, xs) s)
  = mkForEach (prolog pid) [ prolog (liftCase x)
                           , fromIceTPidSet pid xs
                           , fromIceTStmt pid s'
                           ]
    where
      s' = seqStmts [ Assgn x Nothing (T.EVar (liftCase x) T.dummyAnnot { isPatternVar = True })
                    , s
                    ]
fromIceTStmt pid (ForEach x (False, xs) s)
  = mkIter (prolog pid) [ fromIceTExpr pid xs, fromIceTStmt pid s ]

fromIceTStmt pid Fail
  = mkFail (prolog pid)

fromIceTStmt pid s
  = abort "fromIceTStmt" s

fromIceTPid pid (T.EVal (Just (T.CPid p)) _)
  = compoundTerm "e_pid" [prolog p]
fromIceTPid pid (T.EVar v l)
  | isPatternVar l
  = compoundTerm "e_pid" [prolog (liftCase v)]
  | otherwise
  = compoundTerm "e_var" [prolog v]
fromIceTPid pid (T.ESymElt e l)
  = fromIceTPidSet pid e
fromIceTPid pid e
  = prologPid (fromIceTExpr pid e)

fromIceTPidSet pid (T.EVar v _)
  = mkPidSet v
fromIceTPidSet pid e
  = mkPidSet (fromIceTExpr pid e)

---------------------------------------------------
fromIceTExpr :: (?callStack :: CallStack, Show a, HasType a)
             => ProcessId -> IceTExpr (BriskAnnot a) -> Doc
---------------------------------------------------
fromIceTExpr _ (T.EVal (Just (T.CInt i)) _)
  = prolog i
fromIceTExpr _ (T.EVal (Just (T.CPid p)) _)
  = prolog p
fromIceTExpr _ (T.EVal (Just (T.CPidSet ps)) _)
  = prolog ps
fromIceTExpr _ (T.EVal Nothing _)
  = prolog ("ndet" :: String)
fromIceTExpr _ (T.EAny t l)
  = prolog ("ndet" :: String)
fromIceTExpr _ (T.EVar v l)
  = prolog v
fromIceTExpr _ (T.EType t _)
  = prolog t
fromIceTExpr pid (T.ECon c [] _)
  = compoundTerm (cstrId c) [prolog ("null___" :: String)]
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
fromIceTExpr pid (T.ESymElt e _)
  = compoundTerm "nondet" [prolog pid, fromIceTExpr pid e]
fromIceTExpr pid e@(T.EApp e1 e2 l)
  | Just t <- getType l
  = fromIceTExpr pid $ T.EAny (T.EType t l) l
fromIceTExpr pid e
  = abort "fromIceTExpr" e

mkPidSet s  
  = prolog s -- compoundTerm "set" [prolog s]

mkFail :: Doc -> Doc
mkFail p = compoundTerm "die" [p]

mkField :: Doc -> [Doc] -> Doc
mkField = mkAction "field" 2

mkSym :: Doc -> Doc -> Doc -> Doc
mkSym p set act = compoundTerm "sym" [p,set,act]

mkSeq :: [Doc] -> Doc
mkSeq ds  = mkSeq' [ d | d <- ds, d /= Doc.empty ]
  where
    mkSeq' []  = mkSkip
    mkSeq' [d] = d
    mkSeq' ds  = compoundTerm "seq" [listTerms ds]

mkTrue  = text "1"
mkFalse = text "0"
         
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
mkSkip = prolog ("skip" :: String)

mkContinue :: Doc
mkContinue = prolog ("continue" :: String)

mkWhile :: Doc -> [Doc] -> Doc  
mkWhile = mkAction "while" 2

mkForEach :: Doc -> [Doc] -> Doc
mkForEach = mkAction "for" 3

mkIter :: Doc -> [Doc] -> Doc
mkIter = mkAction "iter" 2

mkCases :: Doc -> Doc -> [Doc] -> Maybe Doc -> Doc
mkCases pid x cases d
  = compoundTerm "cases" ([pid, x, listTerms cases, d'])
  where
    d' = fromMaybe mkSkip d

mkCase :: Doc -> Doc -> Doc -> Doc
mkCase pid e s = compoundTerm "case" [pid, e', s']
  where
    e' = if e == Doc.empty then mkSkip else e
    s' = if s == Doc.empty then mkSkip else s

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
         . fixupFirst
    where
      fixupFirst ('_':str) = ("v_" ++ str)
      fixupFirst s         = s

      repl '$'  = "dll__"
      repl '#'  = "mh__"
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

liftCase :: String -> String
liftCase []     = []
liftCase (x:xs) = toUpper x : xs
