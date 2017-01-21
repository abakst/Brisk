{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Brisk.Model.IceT where

import           Name
import           Type
import           Control.Monad.Trans.State
import           Data.Maybe
import           Brisk.Pretty
import           Brisk.Model.GhcInterface
import qualified Brisk.Model.Types as E
import           Brisk.UX

type ProcessId = String

type IceTExpr a = E.EffExpr E.Id a
type IceTType   = Type

data IceTStmt a = Send IceTType (IceTExpr a) (IceTExpr a)
                | Recv IceTType (Maybe E.Id)
                | Assgn E.Id IceTType (IceTExpr a)
                | Seq [IceTStmt a]
                | Case (IceTExpr a) [(IceTExpr a, IceTStmt a)] (Maybe (IceTStmt a))
                | ForEach E.Id (IceTExpr a) (IceTStmt a)
                | While (IceTStmt a)
                | Skip
                | Continue
                  deriving (Show, Eq)

data IceTProcess a = Single  ProcessId (IceTStmt a)
                   | ParIter ProcessId ProcessId (IceTStmt a)
                     deriving Show

data IceTState a = IS { current   :: Char
                      , recFns    :: [(E.Id, [E.Id])]
                      , par       :: [IceTProcess a]
                      , params    :: [E.Id]
                      , paramSets :: [(E.Id, IceTExpr a)]
                      }

class HasType a where
  getType :: a -> Maybe Type
  setType :: Maybe Type -> a -> a

instance HasType a => HasType (IceTExpr a) where
  getType     = getType . E.annot
  setType t e = e { E.annot = setType t (E.annot e) }

recCall :: E.Id -> ITM a (Maybe [E.Id])
recCall f
  = do fs <- gets recFns
       case fs of
         []         -> return Nothing
         (f', xs):_ -> return (Just xs)

type ITM a r = State (IceTState a) r

type Store a = [(E.Id, IceTExpr a)]

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

seqStmts :: [IceTStmt a] -> IceTStmt a    
seqStmts = flattenSeq . Seq

flattenSeq :: IceTStmt a -> IceTStmt a
flattenSeq (Seq ss)
  = dropSingleton
  . simplifySkips
  $ Seq (foldl go [] ss')
  where
    go ss (Seq ss') = ss ++ ss'
    go ss Skip      = ss
    go ss s         = ss ++ [s]
    ss'             = flattenSeq <$> ss
    dropSingleton (Seq [s]) = s
    dropSingleton s         = s
flattenSeq (ForEach x y s)
  = ForEach x y (flattenSeq s)
flattenSeq s
  = s

simplifySkips :: IceTStmt a -> IceTStmt a
simplifySkips (Seq ss) = Seq ss'
  where ss'    = filter (not . isSkip) ss
        isSkip Skip = True
        isSkip _    = False

runIceT :: (Show a, HasType a) => IceTExpr a -> [IceTProcess a]
runIceT e
  = anormalizeProc <$> (Single "A" stmt : par st)
  where
    ((stmt, _), st) = runState (fromTopEffExp e) (IS 'A' [] [] [] [])

---------------------------------------------------
anormalizeProc :: (Show a, HasType a)
               => IceTProcess a
               -> IceTProcess a
---------------------------------------------------
anormalizeProc (Single p s) = Single p (anormalize s)
anormalizeProc (ParIter p ps s) = ParIter p ps (anormalize s)

---------------------------------------------------
fromTopEffExp :: (Show a, HasType a)
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
fromEffExp :: (Show a, HasType a)
           => Store a
           -> IceTExpr a
           -> Maybe E.Id
           -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromEffExp s (E.Recv (E.EType t _) l) x
  = return (Recv t x, flip E.EVar l <$> x)

fromEffExp s (E.Send (E.EType t _) p m l) x
  = do to  <- fromPure s p
       msg <- fromPure s m
       return (Send t to msg, flip E.EVar l <$> x)

fromEffExp s (E.Spawn p l) x
  = fromSpawn l s p x

fromEffExp s (E.SymSpawn xs p l) x
  = fromSymSpawn l s xs p x

fromEffExp s (E.EBind e1 (E.ELam x e2 l2) l1) y
  = fromBind s l1 l2 e1 x e2 y

fromEffExp s (E.EReturn e _) y
  = do e' <- fromPure s e
       return (Skip, Just e')

fromEffExp s (E.EProcess p e l) y
  = fromProcess l s p y

fromEffExp s (E.Self l) _
  = do me <- gets current
       return (Skip, Just (E.EVar [me] (setType t' l)))
         where
           t' = go <$> getType l
           go = head . snd . splitAppTys

fromEffExp s app@(E.EApp _ _ l) _
  = fromApp l s f as
  where
    (f, as) = E.collectAppArgs app

fromEffExp s r@(E.ERec f e l) _
  = fromApp l s r []

fromEffExp s (E.EPrRec acc x body acc0 xs l) mx
  = do (stmt, _) <- fromEffExp s' body mx
       exs       <- fromPure s xs
       return (foreach stmt exs, Nothing)
  where
    s' = addsStore l s [acc, x]
    foreach s exs = ForEach x exs s

fromEffExp s (E.ECase t e alts mdefault l) x
  = do a     <- fromPure s e
       alts' <- mapM (fromAlt l s t) alts
       d'    <- fromDefault mdefault
       return $ (Case a alts' d', Nothing)
         where
           fromDefault Nothing  = return Nothing
           fromDefault (Just d) = do
             (st,_) <- fromEffExp s d Nothing
             return (Just st)

fromEffExp s (E.EVar x l) _
  = recCall x >>= go
  where
    go (Just []) = return (Continue, Nothing)
    go _         = error ("fromEffExpr: bare var (" ++ x ++ ")")

fromEffExp s e _
  = error ("fromEffExpr:\n" ++ E.exprString e)

fromPure :: Store a
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
fromPure s e@(E.EVal (vv,t,p) l)
  = return e
fromPure s (E.EVar b l)
  = return (lookupStore s b)

---------------------------------------------------
fromApp :: (Show a, HasType a)
        => a
        -> Store a
        -> IceTExpr a
        -> [IceTExpr a]
        -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
-- WARNING I am assuming this is tail recursive, but
-- that is not currently checked!!!
fromApp l s (E.ERec f e l') as
  | length xs == length as
  = do modify $ \s -> s { recFns = (f,xs) : recFns s }
       (stmt, ebody) <- fromEffExp s' body Nothing
       modify $ \s -> s { recFns = tail (recFns s) }
       let (rX, while) = mkWhileLoop l f stmt ebody
           initArgs    = mkAssigns (zip xs as)
           app         = seqStmts [initArgs, while]
       return (app, Nothing)
  where
    (xs,body) = E.collectArgs e -- e should be a function in general
    s'        = addsStore l s xs
fromApp l s (E.EVar f _) as
  = recCall f >>= go
  where
    go (Just xs)
      = return (flattenSeq $ Seq [mkAssigns (zip xs as), Continue], Nothing)
    go _
      = abort "fromApp" ("Unknown Function: " ++ render (pp f))
fromApp l s e as
  = abort "fromApp" e

mkAssigns xas
  = Seq [ Assgn x (fromJust $ getType a) a | (x,a) <- xas, nonTrivialAssign x a ]
  where
    nonTrivialAssign x (E.EVar y _) = x /= y
    nonTrivialAssign _ _            = True

mkWhileLoop l f stmt e
  = (retx, While (seqStmts ([stmt] ++ mret)))
  where
    mret = maybe [] (return . mkAssgn) e
    retx = "ret_" ++ f
    mkAssgn e = Assgn retx (fromJust $ getType e) e

---------------------------------------------------
fromAlt :: (Show a, HasType a)
        => a
        -> Store a
        -> IceTType
        -> (E.Id, [E.Id], IceTExpr a)
        -> ITM a (IceTExpr a, IceTStmt a)
---------------------------------------------------
fromAlt l s t (c, xs, e)
  = do (stmt, _) <- fromEffExp s' e Nothing
       return (a, stmt)
  where
    es         = flip E.EVar l <$> xs
    a          = E.ECon c es l
    s'         = foldl go s (zip xs es)
    go s (x,e) = extendStore s x e

---------------------------------------------------
fromSpawn :: (Show a, HasType a)
          => a
          -> Store a
          -> IceTExpr a
          -> Maybe E.Id
          -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromSpawn l s p x
  = do me     <- gets current
       let them    = succ me
       withCurrentM them $ do
         (pSpawn, _) <- fromEffExp s p x
         addProcessM (Single [them] pSpawn)
         return $ (Skip, Just (E.EVar [them] l))

---------------------------------------------------
fromSymSpawn :: (Show a, HasType a)
             => a
             -> Store a
             -> IceTExpr a
             -> IceTExpr a
             -> Maybe E.Id
             -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromSymSpawn l s xs p x
  = do me     <- gets current
       let them    = succ me
           themSet = them : "_Set"
       withCurrentM them $ do
         (pSpawn, _) <- fromEffExp s p x
         addProcessM (ParIter [them] themSet pSpawn)
         return (Skip, Just (E.EVar themSet l))

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
fromBind :: (Show a, HasType a)
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
       let s' = maybe s (extendStore s x) mv1
       (p2, v2) <- fromEffExp s' e2 y
       return (flattenSeq $ Seq [p1, p2], v2)

---------------------------------------------------
fromProcess :: (Show a, HasType a)
            => a
            -> Store a
            -> IceTExpr a
            -> Maybe E.Id
            -> ITM a (IceTStmt a, Maybe (IceTExpr a))
---------------------------------------------------
fromProcess l = fromEffExp

type ANFM a = State Int a

---------------------------------------------------
anormalize :: (Show a, HasType a) => IceTStmt a -> IceTStmt a
---------------------------------------------------
anormalize s = evalState (anf s) 0
  
---------------------------------------------------
anf :: (Show a, HasType a) => IceTStmt a -> ANFM (IceTStmt a)
---------------------------------------------------
anf Skip
  = return Skip
anf Continue
  = return Continue
anf s@Recv {}
  = return s
anf (Send t e1 e2)
  = do (x, bs1) <- imm e1
       (y, bs2) <- imm e2
       return (stitch (bs1 ++ bs2) (Send t x y))
anf (Assgn x t e)
  = do (e', bs) <- imm e
       return $ stitch bs (Assgn x t e')
anf (Seq ss)
  = Seq <$> mapM anf ss
anf (While s)
  = While <$> anf s
anf (Case e es d)
  = do (e', bs) <- imm e
       es'      <- mapM anfAlt es
       d'       <- mapM anf d
       return (stitch bs (Case e' es' d'))
         where
           anfAlt (pat, s) = do s' <- anf s
                                return (pat, s')
anf (ForEach x xs s)
  = do (xs', bs) <- imm xs
       s'        <- anf s
       return (stitch bs (ForEach x xs' s'))

imm :: (Show a, HasType a)
    => IceTExpr a -> ANFM (IceTExpr a, [(E.Id, IceTExpr a)])
imm e@E.EVar{}
  = return (e, [])
imm e@(E.EVal _ _)
  = abort "imm" e
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

fresh :: a -> ANFM (IceTExpr a)
fresh l = do i <- get
             put (i + 1)
             return (E.EVar ("anf" ++ show i) l)

stitch :: HasType a => [(E.Id, IceTExpr a)] -> IceTStmt a -> IceTStmt a
stitch bs s = seqStmts (assigns ++ [s])
  where
    assigns   = go <$> bs
    go (x, e) = Assgn x (fromJust $ getType e) e
