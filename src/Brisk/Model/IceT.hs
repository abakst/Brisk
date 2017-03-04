{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Brisk.Model.IceT where

import           Name
import           Type
import           Control.Monad.Trans.State
import           Data.List
import           Data.Char (toUpper)
import           Data.Maybe
import           Brisk.Pretty
import           Brisk.Model.GhcInterface
import qualified Brisk.Model.Types as E
import           Brisk.UX
import           Text.PrettyPrint.HughesPJ

type ProcessId = String

type IceTExpr a = E.EffExpr E.Id a
type IceTType   = E.Type E.Id

data IceTStmt_ b a = Send IceTType (E.EffExpr b a) (E.EffExpr b a)
                   | Recv IceTType (Maybe (E.EffExpr b a)) (Maybe E.Id)
                   | Assgn b (Maybe IceTType) (E.EffExpr b a)
                   | Seq [IceTStmt_ b a]
                   | Case (E.EffExpr b a) [(E.EffExpr b a, IceTStmt_ b a)] (Maybe (IceTStmt_ b a))
                   | ForEach E.Id (Bool, E.EffExpr b a) (IceTStmt_ b a) 
                   | NonDet IceTType
                   | While (IceTStmt_ b a)
                   | Fail
                   | Skip
                   | Continue
                   | Exec (E.EffExpr b a)
                   -- Only occurs in rw traces, XAssgn p x p e ==> (x_p := eval(p,e))
                   | XAssgn b b b (E.EffExpr b a)
                  deriving (Show, Eq)
type IceTStmt = IceTStmt_ E.Id

data IceTProcess_ b a = Single  ProcessId (IceTStmt a)
                   | Unfold  ProcessId ProcessId ProcessId (IceTStmt a) (IceTStmt a)
                   | ParIter ProcessId ProcessId (IceTStmt a)
                     deriving (Show, Eq)
type IceTProcess = IceTProcess_ E.Id

data IceTState a = IS { current   :: Char
                      , next      :: Char
                      , recFns    :: [(E.Id, [E.Id])]
                      , par       :: [IceTProcess a]
                      , params    :: [E.Id]
                      , paramSets :: [(E.Id, IceTExpr a)]
                      }
queryMsgTys :: (a -> IceTType -> a)
            -> (a -> IceTType -> a)
            -> a
            -> IceTStmt l
            -> a
queryMsgTys f g
  = go
  where
    go b (Send t _ _)    = f b t
    go b (Recv t _ _)    = g b t
    go b (Seq ts)        = foldl' go b ts
    go b (Case _ as d)   = let z = foldl' go b (snd <$> as) in
                           maybe z (go z) d
    go b (ForEach _ _ s) = go b s
    go b (While s)       = go b s
    go b _               = b

substStmt :: (E.Annot a) => E.Id -> IceTExpr a -> IceTStmt a -> IceTStmt a
substStmt x e = go
  where
    sub                = E.subst x e 
    go (Send t p m)    = Send t (sub p) (sub m) 
    go (Assgn x t e)   = Assgn x t (sub e)
    go (Seq ss)        = Seq (go <$> ss)
    go (Case e alts d) = Case (sub e) (fmap go <$> alts) (go <$> d)
    go (ForEach x (b, e) s) = ForEach x (b, sub e) (go s)
    go (While s)       = While (go s)
    go (Recv t w mx)   = Recv t (sub <$> w) mx
    go s               = s

unSubstPid = undefined    

class HasType a where
  getType :: a -> Maybe IceTType
  setType :: Maybe IceTType -> a -> a

instance HasType a => HasType (IceTExpr a) where
  getType     = getType . E.annot
  setType t e = e { E.annot = setType t (E.annot e) }

instance HasType E.AnnIn where
  getType = id
  setType = const

recCall :: E.Id -> ITM a (Maybe [E.Id])
recCall f
  = do fs <- gets recFns
       case fs of
         []         -> return Nothing
         (f', xs):_ -> return (Just xs)

type ITM a r = State (IceTState a) r

type Store a = [(E.Id, IceTExpr a)]

lookupStoreDef :: Store a
               -> E.Id
               -> IceTExpr a
               -> IceTExpr a
lookupStoreDef s v d
  = case lookup v s of
      Nothing -> d
      Just e  -> e

lookupStore :: Store a -> E.Id -> IceTExpr a
lookupStore s v
  = case lookup v s of
      Nothing -> error ("Store lookup! " ++ show v)
      Just e  -> e

extendStore :: Store a -> E.Id -> IceTExpr a -> Store a
extendStore s x e = (x,e) : s

addsStore :: a -> Store a -> [E.Id] -> Store a
addsStore l = foldl go
  where
    go s x = extendStore s x (E.EVar x l)

seqStmts :: [IceTStmt_ b a] -> IceTStmt_ b a    
seqStmts = flattenSeq . Seq

flattenSeq :: IceTStmt_ b a -> IceTStmt_ b a
flattenSeq (Seq ss)
  = dropSingleton
  . simplifySkips
  $ Seq (foldl go [] ss')
  where
    go ss (Seq ss') = ss ++ (foldl go [] ss')
    go ss Skip      = ss
    go ss s         = ss ++ [s]
    ss'             = flattenSeq <$> ss
    dropSingleton (Seq [])  = Skip
    dropSingleton (Seq [s]) = s
    dropSingleton s         = s
flattenSeq (ForEach x y s)
  = ForEach x y (flattenSeq s)
flattenSeq s
  = s

simplifySkips :: IceTStmt_ b a -> IceTStmt_ b a
simplifySkips (Seq ss) = Seq ss'
  where ss'    = filter (not . isSkip) ss
        isSkip Skip = True
        isSkip _    = False

runIceT :: (Show a, HasType a, E.Annot a) => IceTExpr a -> [IceTProcess a]
runIceT e
  =   anormalizeProc
   .  mapProcStmt (substStmt "a" aPid)
  <$> (Single "a" stmt : par st)
  where
    aPid            = E.EVal (Just (E.CPid "a")) E.dummyAnnot
    ((stmt, _), st) = runState (fromTopEffExp e) (IS 'a' 'b' [] [] [] [])

mapProcStmt :: (IceTStmt a -> IceTStmt a) -> IceTProcess a -> IceTProcess a
mapProcStmt f (Single p s)      = Single p (f s)
mapProcStmt f (ParIter p ps s)  = ParIter p ps (f s)
mapProcStmt f (Unfold p0 p ps s t) = Unfold p0 p ps (f s) (f t)

---------------------------------------------------
anormalizeProc :: (Show a, HasType a)
               => IceTProcess a
               -> IceTProcess a
---------------------------------------------------
anormalizeProc = mapProcStmt anormalize

---------------------------------------------------
fromTopEffExp :: (Show a, HasType a, E.Annot a)
              => IceTExpr a
              -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromTopEffExp eff@(E.ELam b e l)
  = do modify $ \s -> s { params = xs }
       fromTopEffExp body
  where
    (xs, body) = E.collectArgs eff
fromTopEffExp eff
  = fromEffExp [] eff Nothing

---------------------------------------------------
fromEffExp :: (Show a, HasType a, E.Annot a)
           => Store a
           -> IceTExpr a
           -> Maybe E.Id
           -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromEffExp s (E.EPrimOp E.Recv [E.EType t _] l) x
  = return (Recv t Nothing x, flip E.EVar l <$> x)

fromEffExp s (E.EPrimOp E.Recv [E.EType t _, e] l) x
  = do e' <- fromPure s e
       return (Recv t (Just e') x, flip E.EVar l <$> x)

fromEffExp s (E.EPrimOp E.Send [E.EType t _, p, m] l) x
  = do to  <- fromPure s p
       msg <- fromPure s m
       return (Send t to msg, flip E.EVar l <$> x)

fromEffExp s (E.EPrimOp E.Spawn [p] l) x
  = fromSpawn l s p x

fromEffExp s (E.EPrimOp E.SymSpawn [xs, p] l) x
  = fromSymSpawn l s xs p x

fromEffExp s (E.EPrimOp E.Bind [e1, E.ELam x e2 l2] l1) y
  = fromBind s l1 l2 e1 x e2 y

fromEffExp s (E.EPrimOp E.Return [e] l) y
  = do e' <- fromPure s e
       return (Skip, Just e')

fromEffExp s (E.EPrimOp E.FoldM [E.ELam a (E.ELam x body _) _, base, xs] l) y       
  = fromEffExp s  E.EPrRec { E.precAcc = a
                           , E.precNext = x
                           , E.precBody = body
                           , E.precBase = base
                           , E.precArg = xs
                           , E.annot = l
                           } y

fromEffExp s (E.EPrRec acc x body acc0 xs l) mx
  = do (stmt, _) <- fromEffExp s' body (Just acc)
       exs       <- fromPure s xs
       a0        <- fromPure s acc0
       return (foreach stmt (isPidSet exs, exs) a0, Nothing)
  where
    s'               = addsStore l s [acc, x]
    foreach s exs a0 = seqStmts [ Assgn acc (getType a0) a0
                                , ForEach x exs s
                                ]
    isPidSet e = getType e
              == Just (E.TyConApp "Control.Distributed.Process.SymmetricProcess.SymProcessSet" []) -- Ugh

fromEffExp s (E.EPrimOp E.Self [] l) _
  = do me <- gets current
       return (Skip, Just (E.EVar [me] (setType ty l)))
         where
           go (E.TyConApp _ [t]) = t
           ty                    = go <$> getType l
            
           -- go = head . snd . E.splitAppTys

fromEffExp s app@(E.EApp _ _ l) _
  = fromApp l s f as
  where
    (f, as) = E.collectAppArgs app

fromEffExp s r@(E.ERec f e l) _
  = fromApp l s r []

fromEffExp s (E.ECase t e alts mdefault l) x
  = do a     <- fromPure s e
       alts' <- mapM (fromAlt l s t x) alts
       d'    <- fromDefault mdefault
       return (simplifyCase $ Case a alts' d', (flip E.EVar l <$> x))
         where
           fromDefault Nothing  = return Nothing
           fromDefault (Just d) = do
             (st,e) <- fromEffExp s d Nothing
             return (Just $ seqStmts [st, mkAssignMb x e])
           mkAssignMb (Just x) (Just e)
             = mkAssigns [(x,e)]
           mkAssignMb _ _
             = Skip
           

fromEffExp s v@(E.EVar x l) _
  = recCall x >>= go
  where
    go (Just []) = return (Continue, Nothing)
    go _         = return (Exec v, Nothing)

fromEffExp s e@(E.EVal x _) _    
  = return (Skip, Just e)

fromEffExp s a@(E.EAny x _) _  
  = return (Skip, Just a)

fromEffExp s e@(E.EPrimOp E.Fail _ _) _
  = return (Fail, Nothing)

fromEffExp s e@E.ECon {} _
  = return (Skip, Just e)

fromEffExp s e _
  = error ("fromEffExpr:\n" ++ E.exprString e)

fromPure :: (Show a, HasType a)
         => Store a
         -> IceTExpr a
         -> ITM a (IceTExpr a)
fromPure s (E.ECase t e alts d l)
  = do e'    <- fromPure s e
       alts' <- mapM goAlt alts
       d'    <- mapM (fromPure s) d
       return $ E.ECase t e' alts' d l
         where
           goAlt (c,xs,e) = (c,xs,) <$> fromPure (addsStore l s xs) e
fromPure s (E.EField e i l)
  = do e' <- fromPure s e
       return (E.EField e' i l)
fromPure s e@(E.ECon c as l)
  = do as' <- mapM (fromPure s) as
       return (E.ECon c as' l)
fromPure s e@(E.EVal _ l)
  = return e
fromPure s v@(E.EVar b l)
  = do ps <- gets params
       return $ if b `elem` ps
                  then v
                  else case getType l of
                         Just t -> 
                           let d = E.EAny (E.EType t l) l in
                           lookupStoreDef s b d
                         Nothing ->
                           let d = E.EVal Nothing l in
                           lookupStoreDef s b d
fromPure s a@E.EAny{}
  = return a
fromPure s (E.ESymElt set l)
  = E.ESymElt <$> fromPure s set <*> pure l
fromPure s (E.EApp e1 e2 l)
  = do v1 <- fromPure s e1
       v2 <- fromPure s e2
       return $ reduceApp v1 v2 l
fromPure s (E.ELam x e l)
  = let s' = extendStore s x (E.EVar x l)
    in E.ELam x <$> fromPure s' e <*> pure l
fromPure s (E.ERec x e l)
  = let s' = extendStore s x (E.EVar x l)
    in E.ERec x <$> fromPure s' e <*> pure l
fromPure _ t@(E.EType {})
  = return t
fromPure s e
  = abort "fromPure" e

reduceApp v1 v2 l
  = E.EApp v1 v2 l

---------------------------------------------------
fromApp :: (Show a, HasType a, E.Annot a)
        => a
        -> Store a
        -> IceTExpr a
        -> [IceTExpr a]
        -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
-- WARNING I am assuming this is tail recursive, but
-- that is not currently checked!!!
fromApp l s erec@(E.ERec f e l') as
  | length xs == length as
  = do modify $ \s -> s { recFns = (f,xs) : recFns s }
       (stmt, ebody) <- fromEffExp s' body Nothing
       modify $ \s -> s { recFns = tail (recFns s) }
       let (rX, while) = mkWhileLoop l f stmt ebody
           initArgs    = mkAssigns (zip xs as)
           app         = seqStmts [initArgs, while]
       return (app, Nothing)
  | otherwise
  = abort "fromApp" (erec, as)
  where
    (xs,body) = E.collectArgs e -- e should be a function in general
    s'        = addsStore l s xs
fromApp l s exp@(E.EVar f _) as
  = do ps <- gets params
       recCall f >>= go ps
  where
    go _ (Just xs)
      = return (seqStmts [mkAssigns (zip xs as), Continue], Nothing)
    go ps _
      | f `notElem` ps
      = abort "fromApp" ("Unknown Function: " ++ render (pp f))
      | otherwise
      = return (Skip, Just exp)
fromApp l s e as
  = abort "fromApp" e

mkAssigns xas
  = seqStmts [ Assgn x (getType a) a | (x,a) <- xas, nonTrivialAssign x a ]
  where
    nonTrivialAssign x (E.EVar y _) = x /= y
    nonTrivialAssign _ _            = True

mkWhileLoop l f stmt e
  = (retx, While (seqStmts ([stmt] ++ mret)))
  where
    mret = maybe [] (return . mkAssgn) e
    retx = "ret_" ++ f
    mkAssgn e = Assgn retx (getType e) e

---------------------------------------------------
fromAlt :: (Show a, HasType a, E.Annot a)
        => a
        -> Store a
        -> IceTType
        -> Maybe E.Id
        -> (E.Id, [E.Id], IceTExpr a)
        -> ITM a (IceTExpr a, IceTStmt a)
---------------------------------------------------
fromAlt l s t x (c, xs, e)
  = do (stmt, e') <- fromEffExp s' e x
       return (a, seqStmts [stmt, mkAssign x e'])
  where
    mkAssign (Just x) (Just e) = mkAssigns [(x,e)]
    mkAssign _ _               = Skip
    es           = flip E.EVar l <$> xs
    a            = E.ECon c es l
    s'           = foldl go s (zip xs es)
    go s (x,e)   = extendStore s x e

---------------------------------------------------
fromSpawn :: (Show a, HasType a, E.Annot a)
          => a
          -> Store a
          -> IceTExpr a
          -> Maybe E.Id
          -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromSpawn l s p x
  = do them <- newPidM
       withCurrentM them $ do
         (pSpawn, _) <- fromEffExp s p x
         let pSpawn' = substStmt [them] pid pSpawn
             pid     = E.EVal (Just (E.CPid [them])) l
         addProcessM (Single [them] pSpawn')
         return $ (Skip, Just pid)

---------------------------------------------------
fromSymSpawn :: (Show a, HasType a, E.Annot a)
             => a
             -> Store a
             -> IceTExpr a
             -> IceTExpr a
             -> Maybe E.Id
             -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromSymSpawn l s xs p x
  = do me     <- gets current
       them   <- newPidM
       let themSet = them : "_Set"
       withCurrentM (toUpper them) $ do
         (pSpawn, _) <- fromEffExp s p Nothing
         addProcessM (ParIter [toUpper them] themSet pSpawn)
         return (Skip, Just (E.EVal (Just (E.CPidSet themSet)) l))

newPidM = do who <- gets next
             modify $ \s -> s { next = succ who }
             return who

addProcessM :: IceTProcess a -> ITM a ()
addProcessM p
  = modify $ \s -> s { par = p : par s }

withCurrentM :: Char -> ITM a b -> ITM a b
withCurrentM p act = do q <- gets current
                        modify $ \s -> s { current = p }                   
                        r <- act
                        modify $ \s -> s { current = q }
                        return r

---------------------------------------------------
fromBind :: (Show a, HasType a, E.Annot a)
         => Store a
         -> a
         -> a
         -> IceTExpr a
         -> E.Id
         -> IceTExpr a
         -> Maybe E.Id
         -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromBind s l1 l2 e1 x e2 y
  = do (p1, mv1) <- fromEffExp s e1 (Just x)
       let s' = maybe (extendStore s x (E.EVar x l1)) (extendStore s x) mv1
       (p2, v2) <- fromEffExp s' e2 y
       return (seqStmts [p1, p2], v2)

---------------------------------------------------
fromProcess :: (Show a, HasType a, E.Annot a)
            => a
            -> Store a
            -> IceTExpr a
            -> Maybe E.Id
            -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromProcess l = fromEffExp

simplifyCase :: E.Annot a => IceTStmt a -> IceTStmt a
simplifyCase st@(Case (E.ECon c xs _) alts _)
  = fromMaybe st $ go alts
  where
    go []
      = Nothing
    go ((E.ECon c' xs' _, s):as)
      | c == c' && length xs == length xs'
      = foldl' app (Just s) (zip xs' xs)
      | otherwise
      = go as
    app s (E.EVar x _,e) = substStmt x e <$> s
    app s _              = Nothing
simplifyCase s = s

type ANFM a = State Int a

---------------------------------------------------
anormalize :: (Show a, HasType a) => IceTStmt a -> IceTStmt a
---------------------------------------------------
anormalize s = evalState (anf s) 0

-- This anormalization just makes sure that sends have
-- immediate arguments, that's all
---------------------------------------------------
anf :: (Show a, HasType a) => IceTStmt a -> ANFM (IceTStmt a)
---------------------------------------------------
anf Skip
  = return Skip
anf Fail
  = return Fail
anf Continue
  = return Continue
anf s@Recv {}
  = return s
anf (Send t e1 e2)
  = do (x, bs1) <- imm e1
       (y, bs2) <- imm e2
       return (stitch (bs1 ++ bs2) (Send t x y))
anf s@(Assgn x t e)
  = do (y, bs) <- imm e
       return $ stitch bs (Assgn x t y)
anf (Seq ss)
  = seqStmts <$> mapM anf ss
anf (While s)
  = While <$> anf s
anf (Case e es d)
  = do es'      <- mapM anfAlt es
       d'       <- mapM anf d
       return (Case e es' d')
         where
           anfAlt (pat, s) = do s' <- anf s
                                return (pat, s')
anf (ForEach x xs s)
  = do s'        <- anf s
       return (ForEach x xs s')
anf (Exec e)
  = do (e', bs) <- imm e
       return (stitch bs $ Exec e')
anf s
  = abort "anf" s

imm :: (Show a, HasType a)
    => IceTExpr a -> ANFM (IceTExpr a, [(E.Id, IceTExpr a)])
imm e@E.EAny{}
  = return (e, [])
imm (E.ESymElt s l)
  = do (s', bs) <- imm s
       x        <- fresh l
       let e = E.ESymElt s' l
       return (x, bs ++ [(E.varId x, e)])
imm e@E.EVar{}
  = return (e, [])
imm e@(E.EVal _ _)
  = return (e, [])
imm e@(E.ECon c [] l)
  = return (e, [])
imm (E.ECon c args l)
  = do x <- fresh l
       (immArgs, bs) <- unzip <$> mapM imm args
       let e = E.ECon c immArgs l
       return (x, concat bs ++ [(E.varId x, e)])
imm e@E.ECase {}
  = do x            <- fresh (E.annot e)
       return (x, [(E.varId x, e)])
imm e@E.EField {}
  = do x <- fresh (E.annot e)
       return (x, [(E.varId x, e)])
-- imm e@(E.ELam b bdy a)
--   = return (e, [])
imm e@(E.EApp e1 e2 l)
  = return (e, [])
imm e
  = abort "imm" e

fresh :: a -> ANFM (IceTExpr a)
fresh l = do i <- get
             put (i + 1)
             return (E.EVar ("anf" ++ show i) l)

stitch :: HasType a => [(E.Id, IceTExpr a)] -> IceTStmt a -> IceTStmt a
stitch bs s = seqStmts (assigns ++ [s])
  where
    assigns   = go <$> bs
    go (x, e) = Assgn x (getType e) e

instance Pretty (IceTStmt a) where
  ppPrec _ (Exec e)
    = text "exec" <> (E.tuple [pp e])
  ppPrec _ (Send t p m)
    = text "send" <> brackets (pp t)
                  <> E.tuple [pp p, pp m]

  ppPrec _ (Recv t w Nothing)
    = ppRecv t w

  ppPrec _ (Recv t w (Just x))
    = pp x <+> text ":=" <+> ppRecv t w

  ppPrec _ (Assgn x _ e)
    = pp x <+> text ":=" <+> pp e
  ppPrec _ (XAssgn p x q e)
    = pp x <> brackets (pp p) <+> text ":=" <+> pp e <+> text "@" <> pp q

  ppPrec _ (Seq ss)
    = vcat (ppPrec 0 <$> ss)

  ppPrec _ (Case e alts mdf)
    = text "match" <+> pp e <> colon $$
      nest 2 (vcat (ppAlt <$> alts)) $$
      nest 2 (ppDflt mdf)
    where
      ppAlt (e,s) = text "case" <+> pp e <> colon $$
                    nest 2 (ppPrec 0 s)
      ppDflt Nothing  = empty
      ppDflt (Just s) = text "__DEFAULT__:" $$ nest 2 (ppPrec 0 s)

  ppPrec _ (ForEach x (True, e) s)
    = text "for" <+> pp x <+> text "in" <+> pp e <> colon $$
      nest 2 (ppPrec 0 s)

  ppPrec _ (ForEach x (False, e) s)
    = text "iter" <+> pp x <+> text "in" <+> pp e <> colon $$
      nest 2 (ppPrec 0 s)

  ppPrec _ (While s)
    = text "while true" <> colon $$
      nest 2 (ppPrec 0 s)

  ppPrec _ Fail     = text "abort"
  ppPrec _ Skip     = text "skip"
  ppPrec _ Continue = text "continue"

ppRecv t Nothing 
  = text "recv" <> brackets (pp t)
ppRecv t (Just w)
  = text "recvFrom" <> brackets (pp t) <> parens (pp w)
                  
instance Pretty (IceTProcess a) where
  ppPrec _ (Single p s)
    = text "proctype" <+> text p <> colon $$
      nest 2 (pp s)
  ppPrec _ (Unfold p _ ps s t)
    = text "proctype" <+> parens (text p <> text "*" <> colon <> text ps) <> colon $$
      nest 2 (pp s)
  ppPrec _ (ParIter p ps s)
    = text "proctype" <+> parens (text p <> colon <> text ps) <> colon $$
      nest 2 (pp s)
