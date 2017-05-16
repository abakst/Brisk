{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language GADTs #-}
module Brisk.Model.Types where

import GhcPlugins (SrcSpan, showSDoc, unsafeGlobalDynFlags, ppr)
import Data.Maybe
import Brisk.Pretty
import GHC.Generics
import Brisk.UX
import Brisk.Model.GhcInterface
import Text.PrettyPrint.HughesPJ
import Unique
import PrelNames
import TysWiredIn
import Data.List hiding ((\\))
import qualified Data.Set as Set
import Name
import BasicTypes (Arity)
import TyCon
import SrcLoc
import FastString
import DataCon
import Data.Data
import Data.Char
import Data.Serialize hiding (Fail)
import qualified Data.ByteString as B
import qualified Data.ByteString.UTF8 as B8
import qualified Data.ByteString.UTF8 as B8
import qualified Codec.Binary.UTF8.String as B8String
import qualified Type as T
import TyCon
import qualified TyCoRep as Tr
import Data.Word
import GHC.Word
import Debug.Trace

import Data.IORef
import System.IO.Unsafe
import System.Random

-----------------------------------------------  
nextStr :: String -> IO String
-----------------------------------------------  
nextStr s = do
  c0 <- randomRIO ('a', 'z') 
  return (s ++ [c0])

type Id = String                 

-----------------------------------------------  
--  Specification Language (Preds, Exprs, Types)
----------------------------------------------- 
data Pred b a = Top | Bot | Conj [Pred b a] | Disj [Pred b a] | LNot (Pred b a)
              | PVar String [EffExpr b a]
              | Pred b a :==>: Pred b a
              | CHC [b] (Pred b a) (Pred b a)
              | BRel Op (EffExpr b a) (EffExpr b a)
              deriving (Eq, Show)

-- instance Functor (Pred b)  where
--   fmap f (Rel o p1 p2) = Rel o (fmap f p1) (fmap f p2)
--   fmap f (PVal b ps)   = PVal b (fmap f <$> ps)
--   fmap f (PEffect e)   = PEffect (fmap f e)
--   fmap f (PConst c)    = PConst c
--   fmap _ PTrue         = PTrue

data Const = CInt Int          
           | CPid Id
           | CPidSet Id
           deriving (Eq, Show, Generic)

instance Serialize Const 

data Op = Eq | Le | NEq | Plus | Minus
        deriving (Eq, Show)

litInt i a = EVal (Just (CInt (fromInteger i))) a
ePlus  = BRel Plus
eMinus = BRel Minus

data Type b = -- ^ Essentially a mirror of GHC's Type  
    TyVar b
  | TyApp (Type b) (Type b)
  | TyConApp b [Type b]
  | TyFun (Type b) (Type b)
  | TyForAll b (Type b)
    deriving (Eq, Ord, Show, Generic)
instance Serialize b => Serialize (Type b)

type Subset b a = (b, T.Type, Pred b a)
data EffExpr b a =
   -- EVal    { valPred :: Subset b a, annot :: a }                -- ^ {v | p}
   EVal    { valVal :: Maybe Const, annot :: a }
 | EVar    { varId :: b, annot :: a }                          -- ^ x
 | ESymElt { symSet :: EffExpr b a, annot :: a }
 | ECon    { conId :: b, conArgs :: [EffExpr b a], annot :: a }
 | ELam    { lamId :: b, lamBody :: EffExpr b a, annot :: a }            -- ^ \x -> e
 | EAny    { anyTy  :: EffType b a, annot :: a }
 | EApp    { appFun :: EffExpr b a, appArg :: EffExpr b a, annot :: a }
 | EPrRec  { precAcc  :: b
           , precNext :: b
           , precBody :: EffExpr b a
           , precBase :: EffExpr b a
           , precArg  :: EffExpr b a
           , annot :: a
           }-- ^ R (\X x -> e, E, X0)
 | ERec    { recId :: b, recBody :: EffExpr b a, annot :: a }
 | ECase   { caseTy :: Type b
           , caseArg :: EffExpr b a
           , caseAlts :: [(b, [b], EffExpr b a)]
           , caseDft :: (Maybe (EffExpr b a))
           , annot :: a
           }
 | ELet    { letId :: b, letExpr :: EffExpr b a, letBody :: EffExpr b a, annot :: a }
 | EType   { typeTy :: Type b, annot :: a }
 -- Processes
 | EPrimOp { primOp   :: PrimOp
           , primArgs :: [EffExpr b a]
           , annot    :: a
           }
 -- This does not occur in programs!
 | EUnion { alts :: [EffExpr b a]
          }
   deriving (Eq, Show, Generic, Functor)
instance (Serialize b, Serialize a) => Serialize (EffExpr b a)

data PrimOp = Bind | Return | Fail | FoldM
            | Send | Recv | Self
            | Spawn | SymSpawn
            deriving (Eq, Show, Generic)
instance Serialize PrimOp

type Process b a  = EffExpr b a
type EffType b a  = EffExpr b a
type PureExpr b a = EffExpr b a

isFun, isVal :: EffExpr b a -> Bool
isVal EVal{} = True                    
isVal ECon{} = True
isVal _      = False

isFun (ELam {})      = True
isFun (ELet _ _ e _) = isFun e
isFun _              = False
----------------------------------------------- 
-- | Joining Types
----------------------------------------------- 
join :: Eq b => EffExpr b a -> EffExpr b a -> EffExpr b a
join (EVar x l) (EVar y _)
  | x == y
  = EVar x l
join e@(EVal c1 l) (EVal c2 _)
  | c1 == c2  = e
join e@(ECon c es l) (ECon c' es' _)
  | c == c'
  = ECon c (zipWith join es es') l
join (EUnion es) (EUnion es') = EUnion (es ++ es')
join (EUnion es) e = EUnion (e:es)
join e (EUnion es) = EUnion (e:es)
join e1 e2 = EUnion [e1, e2]

----------------------------------------------- 
-- | Type Conversion 
----------------------------------------------- 
ofType :: (TyCon.TyCon -> b) -> (Name -> b) -> T.Type -> Type b
ofType f g = go 
  where
    go (Tr.TyVarTy v)
      = TyVar . g $ getName v
    go (Tr.TyConApp tc [t1, t2])
      | isFunTyCon tc
      = TyFun (go t1) (go t2)
    go (Tr.TyConApp tc ts)
      = TyConApp (f tc) (go <$> ts)
    go (Tr.AppTy t1 t2)
      = TyApp (go t1) (go t2)
    -- go (Tr.FunTy t1 t2)
    go (Tr.ForAllTy v t)
      | Just n <- T.binderVar_maybe v
      = TyForAll (g . getName $ n) (go t)
      | otherwise
      = go t
    go ty
      = abort "ofType" (briskShowPpr ty)

isFunTy = T.isFunTy

tyVarName :: String -> String    
tyVarName (s0:s)
  = toUpper s0:s

-- (t1 (t2 (t3 t4)))
splitAppTys (TyApp t1 t2) = (t1, reverse (go [] t2))
  where
    go ts (TyApp t1 t2)
      = go (t1:ts) t2
    go ts t
      = t:ts
splitAppTys t = abort "splitAppTys" t
----------------------------------------------- 
-- | Operations on Expressions  
----------------------------------------------- 
txExprPid :: (Id -> a -> EffExpr b a) -> EffExpr b a -> EffExpr b a
txExprPid f
  = txExprIds (\v l -> EVar v l) f

txExprVars :: (b -> a -> EffExpr b a) -> EffExpr b a -> EffExpr b a    
txExprVars f
  = txExprIds f (\p l -> EVal (Just (CPid p)) l)

txExprIds :: (b -> a -> EffExpr b a)
          -> (Id -> a -> EffExpr b a)
          -> EffExpr b a
          -> EffExpr b a
txExprIds f g
  = go
  where
    go (EVar x l)               = f x l
    go (EVal (Just (CPid x)) l) = g x l -- EVal (Just (CPid (f x))) l
    go (ESymElt e l)            = ESymElt (go e) l
    go (ECon c es l)            = ECon c (go <$> es) l
    go (ELam b m l)             = ELam b (go m) l
    go (ELet b m n l)           = ELet b (go m) (go n) l
    go (EApp m n l)             = EApp (go m) (go n) l
    go (EPrRec a x m b e l)     = EPrRec a x (go m) (go b) (go e) l
    go (ERec x e l)             = ERec x (go e) l
    go (ECase t a alts d l)     = ECase t (go a) (goAlt <$> alts) (go <$> d) l
      where goAlt (x,y,z) = (x,y,go z)
    go (EPrimOp op args l)      = EPrimOp op (go <$> args) l
    go e                        = e

defaultEffExpr :: a -> Tr.Type -> EffExpr Id a 
defaultEffExpr a = go
  where go (Tr.TyConApp tc [t0, t])
          | isFunTyCon tc && T.isDictTy t0
          = go t 
          | isFunTyCon tc
          = ELam "_" (go t) a
        go ft@(Tr.ForAllTy v t)
          | Just n <- T.binderVar_maybe v
          = ELam (nameId (getName n)) (go t) a
          | T.isDictTy (T.funArgTy ft)
          = go t
          | otherwise
          = ELam "_" (go t) a
        go t
          = EAny (EType (ofType tyConId nameId t) a) a
    
substs :: Subst b (EffExpr b a)
       => [b]
       -> [EffExpr b a]
       -> EffExpr b a
       -> EffExpr b a
substs froms tos = subst (zip froms tos)

simplify :: (Show a, Show b, Subst b (EffExpr b a))
         => EffExpr b a -> EffExpr b a
simplify (ECase t e [(c,[],a)] Nothing l)
  = a
simplify (ECase t e alts md l)
  = fromMaybe defCase $ simplifyCasesMaybe e' alts'
  where
    defCase = ECase t e' alts' md' l
    e'      = simplify e
    alts'   = map (\(x,y,z) -> (x,y,simplify z)) alts
    md'     = simplify <$> md
simplify (ERec f e l)
  = ERec f (simplify e) l
simplify (EPrRec x y e b xs l)
  = EPrRec x y (simplify e) (simplify b) (simplify xs) l
simplify (EApp e1 e2 l)
  = case e1' of
      ELam b m _           -> subst [(b,e2')] m
      ECase t e alts md l' -> simplifyCaseApp t e alts md l' e2' l
      _                    -> EApp e1' e2' l
  where
    e1' = simplify e1
    e2' = simplify e2 
simplify (EPrimOp op args l) = EPrimOp op (simplify <$> args) l
simplify (ECon c xs l)   = ECon c (simplify <$> xs) l
simplify (ELam b e l)    = ELam b (simplify e) l
simplify (ELet x e1 e2 l)= ELet x (simplify e1) (simplify e2) l
simplify t@EType{}       = t
simplify x@EVar{}        = x
simplify v@EVal{}        = v
simplify a@EAny{}        = a
simplify (ESymElt set l) = ESymElt (simplify set) l

simplifyCasesMaybe :: (Show a, Show b, Subst b (EffExpr b a))
                   => EffExpr b a
                   -> [(b,[b],EffExpr b a)]
                   -> Maybe (EffExpr b a)
simplifyCasesMaybe e@(ECon c xs _) ((c', xs', alt):alts)
  | c == c' && length xs == length xs'
  = Just $ simplify $ substs xs' xs alt
  | otherwise
  = simplifyCasesMaybe e alts
simplifyCasesMaybe _ _
  = Nothing

simplifyCaseApp :: forall a b. (Show a, Show b, Subst b (EffExpr b a))
                => Type b
                -> EffExpr b a
                -> [(b, [b], EffExpr b a)]
                -> Maybe (EffExpr b a)
                -> a
                -> EffExpr b a
                -> a
                -> EffExpr b a
simplifyCaseApp t caseE alts md l e' l'  
  = ECase t caseE (goAlt <$> alts) (go <$> md) l
  -- | otherwise
  -- = EApp (ECase t e alts md l) e' l'
  where
    goAlt (c,xs,e) = (c,xs,go e)
    go    e        = simplify $ EApp e e' l


unfoldRec :: Subst b (EffExpr b a) => EffExpr b a -> EffExpr b a
unfoldRec m@(ERec b e l)
  = subst [(b, m)] e

substAlt :: (Avoid b, Annot a, Ord b)
         => Sub b (EffExpr b a)
         -> (b, [b], EffExpr b a) -> (b, [b], EffExpr b a)
substAlt s (c, bs, e)
  = (c, bs', substExpr True s' e)
  where
    cas  = [ (b, EVar b' dummyAnnot) | b <- bs | b' <- bs' ]
    bs'  = avoid fvs <$> bs
    fvs  = fvSubst s
    s'   = cas ++ restrSubst s bs
  -- | x `elem` bs
  -- = (c, bs, e)
  -- | otherwise
  -- = (c, bs', subst x a e')  
  -- where
  --   bs'          = avoid fvs <$> bs
  --   e'           = foldl' go e (zip bs bs')
  --   fvs          = fv a
  --   go e (b, b') = if b `elem` fv e then substExpr True b (EVar b' dummyAnnot) e else e

conEffExpr :: Annot a => a -> T.Type -> DataCon -> EffExpr Id a  
conEffExpr l t d
  = foldr go (ECon (dataConId d) xs l) (tvs ++ xs)
  where
    tvs     = [ EVar [x] dummyAnnot | x <- take (length αs) ['A'..] ]
    xs      = [ EVar [x] dummyAnnot | x <- take ar ['a'..] ]
    ar      = length bs
    (αs, t) = T.splitForAllTys (dataConUserType d)
    (bs, _) = T.splitPiTys t
    go x e = ELam (varId x) e dummyAnnot

apConEff :: EffExpr b a -> EffExpr b a -> EffExpr b a
apConEff (ECon d args l) a = ECon d (args ++ [a]) l

dataConId :: DataCon -> Id
dataConId d
  | d == unitDataCon = "Unit"
  | d == consDataCon = "Cons"
  | d == nilDataCon  = "Nil"
  | isTupleDataCon d = "Tuple"
  | otherwise        = nameId (getName (dataConWorkId d))

vv :: Id
vv = "#vv"

exprString :: Pretty (EffExpr b a) => EffExpr b a -> String
exprString e = render (pp e)

type Sub b a = [(b,a)]
class Ord b => Subst b a where
  subst   :: Sub b a -> a -> a
  fv      :: a -> Set.Set b 

apSubst :: Eq b => Sub b a -> b -> Maybe a
apSubst sub x = lookup x sub

restrSubst :: (Subst b a, Eq b) => Sub b a -> [b] -> Sub b a
restrSubst sub xs
  = filter (\(x,_) -> x `notElem` xs) sub
fvSubst sub
  = Set.unions $ (fv . snd <$> sub)
-- class ToTyVar b where
--   toTyVar :: b -> T.TyVar

-- instance ToTyVar Id where
--   toTyVar = mkTyVar

instance Pretty b => Pretty (Type b) where
  ppPrec _ (TyVar b) = pp b
  ppPrec _ (TyConApp b []) = pp b
  ppPrec _ (TyConApp b ts) = pp b <> brackets (spaces ts)
  ppPrec _ (TyApp t1 t2) = pp t1 <+> pp t2
  ppPrec _ (TyFun t1 t2) = pp t1 <+> text "->" <+> pp t2
  ppPrec _ (TyForAll x t) = text "forall" <+> pp x <> text "." <+> pp t

instance (Pretty b, Eq b) => Pretty (EffExpr b a) where
  -- ppPrec _ (EVal (v,t,Rel Eq (PEffect (EVar v' _)) e) _)
  --   | v == v' = pp e
  ppPrec _ (EAny t _)  = braces (pp t)
  ppPrec _ (EVal mv _) = maybe (text "*") pp mv
  ppPrec _ (ESymElt set _) = braces (text "_ ∈" <+> pp set)
  ppPrec _ (ECon c [] _)
    = pp c
  ppPrec _ (ECon c as _)
    = parens (pp c <> parens (hcat (punctuate comma (ppPrec 9 <$> as))))
  ppPrec z (EVar b _)
    = ppPrec z b
  ppPrec z (ECase t e es d _)
    = parensIf (z > 4) (ppCases e es d)
  ppPrec z (EApp e1 e2 _)
    = parensIf (z > 8) (ppPrec 8 e1 <+> ppPrec 9 e2)
  ppPrec z f@(ELet x e1 e2 _)
    = text "let" <+> pp x <+> equals <+> ppPrec 0 e1 $$
      text "in"  <+> ppPrec 0 e2
  ppPrec z f@(ELam _ _ _)
    -- = parensIf (z > 7) (text "\\" <> spaces xs <+> text "->" $$ nest 2 (ppPrec 7 e))
    = parens (text "\\" <> spaces xs <+> text "->" $$ nest 2 (ppPrec 7 e))
    where
      (xs, e)         = collectArgs f
  ppPrec z (EPrimOp Bind [e1, e2] _) = text "do" <+> nest 3 (vcat (body e1 e2))
    where
      body e1 (ELam b e2 _) = [pp b <+> text "<-" <+> pp e1] ++ go e2
      body e1 e2            = [pp e1, pp e2]
      go (EPrimOp Bind [e1,e2] _) = body e1 e2
      go e                        = [pp e]
  ppPrec z (EPrimOp o args _)
    = ppPrec 0 o <> tuple (ppPrec 0 <$> args)
  ppPrec z (ERec b f@(ELam _ _ _) _)
    = text "letrec" <+> ppPrec z b <+> spaces xs <+> equals <+> ppPrec 0 e $$ text "in" <+> ppPrec z b
    where
      (xs, e) = collectArgs f
  ppPrec z (EPrRec x y f b x0 _)
    = parensIf (z > 7)
        (text "R" <+>
          parens (text "\\" <> spaces [x, y] <+> text "->" <+> ppPrec 0 f) 
          <+> ppPrec 8 b <+> ppPrec 8 x0)
  ppPrec z (ERec b e _)
    = text "letrec" <+> ppPrec z b <+> equals <+> ppPrec 0 e $$ text "in" <+> ppPrec z b
  ppPrec _ (EType t _)      = text "@" <> pp t
  ppPrec _ (EUnion es)
    = hcat (punctuate (text "⊔") (ppPrec 0 <$> es))

instance Pretty PrimOp where
  ppPrec _ Self     = text "$self"
  ppPrec _ Send     = text "$send"
  ppPrec _ Recv     = text "$recv"
  ppPrec _ Spawn    = text "$spawn"
  ppPrec _ SymSpawn = text "$symSpawn"
  ppPrec _ Return   = text "$return" 
  ppPrec _ Bind     = text "$bind"
  ppPrec _ Fail     = text "$fail"
  ppPrec _ FoldM    = text "$foldM"

tuple :: [Doc] -> Doc  
tuple xs = parens (hcat (punctuate comma xs))

instance Pretty Const where
  ppPrec _ (CInt i)     = int i
  ppPrec _ (CPid p)     = text "%" <> text p
  ppPrec _ (CPidSet ps) = text "%" <> text ps

instance (Pretty b, Pretty (EffExpr b a)) => Pretty (Pred b a) where
  ppPrec _ Top         = text "⊤"
  ppPrec _ Bot         = text "⊥"
  ppPrec _ (p :==>: q) = parens (pp p <+> text "⇒" <+> pp q)
  ppPrec _ (CHC xs p q) = text "∀" <> brackets (hcat $ list xs)
                                      <> text "."
                                      <+> pp (p :==>: q)
  ppPrec _ (PVar p xs) = text p <+> (hcat $ list xs)
  ppPrec _ (Conj [φ]) = pp φ
  ppPrec _ (Disj [φ]) = pp φ
  ppPrec _ (Conj φs)  = text "∧" <> brackets (vcat $ list φs)
  ppPrec _ (Disj φs)  = text "∨" <> brackets (hcat $ list φs)
  ppPrec _ (LNot φ)   = text "¬" <> parens (pp φ)
  ppPrec _ (BRel Eq e1 e2)
    = (pp e1 <+> text "=" <+> pp e2)
  ppPrec _ (BRel Le e1 e2)
    = (pp e1 <+> text "<=" <+> pp e2)

list xs = punctuate comma (pp <$> xs)

instance Pretty Op where
  ppPrec _ Eq    = text "="
  ppPrec _ NEq   = text "!="
  ppPrec _ Le    = text "<"
  ppPrec _ Plus  = text "+"
  ppPrec _ Minus = text "-"

collectAppArgs (EApp f e _) = go [e] f
  where
    go as (EApp e1 e2 _) = go (e2:as) e1
    go as e'             = (e', as)

collectArgs (ELam b e _) = go [b] e
  where
    go bs (ELam b' e' _) = go (b':bs) e'
    go bs e'             = (reverse bs, e')
collectArgs e            = ([], e)

ppCases e es d
  = text "case" <+> ppPrec 0 e <+> text "of" $$ nest 2 (vcat alts)
  where
    alts           = (alt1 <$> es) ++ [dalt]
    alt1 (c,bs,e') = pp c <+> spaces bs <+> text "->" $$ nest 2 (pp e')
    dalt           = maybe empty ((text "_" <+> text "->" <+>) . pp) d

spacesPrec :: Pretty a => Int -> [a] -> Doc    
spacesPrec n = foldl (<+>) empty . map (ppPrec n)

spaces :: Pretty a => [a] -> Doc
spaces = spacesPrec 0

instance (Avoid b, Annot a, Ord b) => Subst b (EffExpr b a) where
  fv    = fvExpr
  subst = substExpr False

instance Ord b => Subst b (Type b) where
  fv _  = Set.empty
  subst s = go
    where
      go v@(TyVar x)
        = fromMaybe v $ apSubst s x
      go (TyApp t1 t2) = TyApp (go t1) (go t2)
      go (TyConApp b ts) = TyConApp b (go <$> ts)
      go (TyFun t1 t2) = TyFun (go t1) (go t2)

-- A dirty hack, but maybe not so dirty
substExpr :: (Avoid b, Annot a, Ord b)
          => Bool -> Sub b (EffExpr b a) -> EffExpr b a -> EffExpr b a
substExpr flg s = go
    where
      go (EAny t l)      = EAny (go t) l
      go (ESymElt set l) = ESymElt (go set) l
      go v@(EVal{}) = v
      -- go v@(EVal (b,t,p) l) = (EVal (b, t, (substPred x a p)) l)
      go v@(EVar x _)
        = fromMaybe v $ apSubst s x
        -- WTF whas I doing here:
        -- = case a of
        --     EVar y' l | x == x' && b -> EVar y' l
        --     _         | x == x'      -> a
        --               | otherwise    -> v
      go v@(ECon c as l)
        = ECon c (go <$> as) l
      go g@(EPrRec a b f eb e0 l)
        = EPrRec a' b' (go f') (go eb) (go e0) l
        where
          s' = restrSubst s [a,b]
          (ELam a' (ELam b' f' _) _)
            = substExpr flg s' (ELam a (ELam b f dummyAnnot) dummyAnnot)
      go g@(ERec f e l)
        = ERec f' (substExpr flg s' e) l
        where
          f' = avoid (fvSubst s) f
          s' = (f, EVar f' dummyAnnot) : restrSubst s [f]
      go f@(ELam x e l)
        = ELam x' (substExpr flg s' e) l
        where
          x' = avoid (fvSubst s) x
          s' = (x, EVar x' dummyAnnot) : restrSubst s [x]
      go e@(ELet x e1 e2 l)
        = ELet x' e1' e2' l
        where
          e1' = substExpr flg s e1
          x'  = avoid (fvSubst s) x
          e2' = substExpr flg ((x, EVar x' dummyAnnot) : restrSubst s [x]) e2
      go (ECase t e es d l)
        = ECase t (go e) (substAlt s <$> es) (go <$> d) l
      go (EApp e1 e2 l)
        = EApp (go e1) (go e2) l
      go (EPrimOp o es l)
        = EPrimOp o (go <$> es) l
      go ty@(EType t l)
        = EType (subst s' t) l
        where
          s' = [(x, t') | (x, EType t' l') <- s]

fvExpr :: (Avoid b, Annot a, Ord b) => EffExpr b a -> Set.Set b
fvExpr (EAny t _)      = fv t
fvExpr (ESymElt s _)   = fv s
fvExpr (EVal _ _)      = Set.empty
fvExpr (EVar x _)      = Set.singleton x
fvExpr (ECon x as _)   = Set.unions (fv <$> as)
fvExpr (ERec f e _)    = fv e Set.\\ Set.singleton f
fvExpr (EPrRec x y f b e _) = Set.unions (fv <$> [f,b,e]) Set.\\ Set.fromList [x,y]
fvExpr (ELam x e _)    = fv e Set.\\ Set.singleton x
fvExpr (ELet x e1 e2 _)  = Set.unions [fv e1, fv e2 Set.\\ Set.singleton x]
fvExpr (ECase t e es d l)= Set.unions ([fv e] ++ fvDefault d ++ fmap fvAlts es)
  where
    fvDefault Nothing   = []
    fvDefault (Just e)  = [fv e]
fvExpr (EApp e1 e2 _)   = fv e1 `Set.union` fv e2
fvExpr (EPrimOp o es _) = Set.unions (fv <$> es)
fvExpr (EType t _)      = Set.empty

fvAlts :: (Avoid b, Annot a, Ord b) => (b, [b], EffExpr b a) -> Set.Set b
fvAlts (_, xs, e) = fv e Set.\\ (Set.fromList xs)

-- fvPred :: (Avoid b, Annot a, Ord b) => Pred b a -> Set.Set b
-- fvPred (PVal v ps)   = Set.unions (fvPred <$> ps) Set.\\ Set.singleton v
-- fvPred (Rel _ p1 p2) = fvPred p1 `Set.union` fvPred p2
-- fvPred (PEffect e)   = fv e
-- fvPred PTrue         = Set.empty
-- fvPred (PConst _)    = Set.empty

class Avoid b where
  avoid :: Set.Set b -> b -> b

class Eq a => Annot a where
  dummyAnnot :: a

instance Avoid Id where
  avoid fvs x
    | Set.member x fvs
    = let s = unsafePerformIO $ nextStr x
      in avoid fvs s
    | otherwise
    = x

instance Annot () where
  dummyAnnot = ()

data SourceSpan = Span String Int Int Int Int
                deriving (Eq, Generic, Typeable, Show)
instance Serialize SourceSpan 

noSpan :: SourceSpan
noSpan = sourceSpan noSrcSpan

realSpan :: RealSrcSpan -> SourceSpan
realSpan sp
  = Span (unpackFS $ srcLocFile st)
         (srcLocLine st)
         (srcLocCol st)
         (srcLocLine end)
         (srcLocCol end)
  where
    (st, end) = (realSrcSpanStart sp, realSrcSpanEnd sp)

sourceSpan :: SrcSpan -> SourceSpan
sourceSpan span
 = case (st, end) of
     (RealSrcLoc loc, RealSrcLoc loc')
       -> Span (unpackFS $ srcLocFile loc)
               (srcLocLine loc)
               (srcLocCol loc)
               (srcLocLine loc')
               (srcLocCol loc')
     (UnhelpfulLoc fs, _)
       -> Span (unpackFS fs) (-1) (-1) (-1) (-1)
  where
    (st, end) = (srcSpanStart span, srcSpanEnd span)

type TyAnnot  = (Maybe (Type Id), SourceSpan)
data EncodedAnnot = Encoded { unEncode :: TyAnnot }

type AbsEff = EffExpr Id TyAnnot

data SpecTable a = SpecTable { entries :: [SpecEntry a] }
                 deriving (Eq, Show, Generic)
data SpecEntry a = Id :<=: EffExpr Id a
                   deriving (Eq, Show, Generic, Functor)

instance Serialize a => Serialize (SpecEntry a)
instance Serialize a => Serialize (SpecTable a)

lookupTable :: Id -> SpecTable a -> Maybe (EffExpr Id a)
lookupTable b (SpecTable es)
  = listToMaybe [ t | x :<=: t <- es, x == b ]

specTableToWords :: SpecTable TyAnnot -> String
specTableToWords (SpecTable es)
  = map (chr . fromIntegral) . B.unpack . encode $ es

myencode :: Serialize a => a -> String
myencode = B8String.decode . B.unpack . encode  

mydecode :: Serialize a => String -> Either String a
mydecode = decode . B.pack . B8String.encode


wordsToSpecTable :: String -> SpecTable TyAnnot
wordsToSpecTable wds
  = case decode . B.pack . map (fromIntegral . ord) $ wds of 
      Left str -> abort "wordsToSpecTable" str
      Right es -> SpecTable es

data BriskAnnot = AnnotModule

instance Annot TyAnnot where
  dummyAnnot = (Nothing, noSpan)
