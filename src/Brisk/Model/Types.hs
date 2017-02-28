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

type Id = String                 

-----------------------------------------------  
--  Specification Language (Preds, Exprs, Types)
----------------------------------------------- 
data Pred b a = Rel Op (Pred b a) (Pred b a)
              | PVal b [Pred b a]
              | PConst Const
              | PEffect (PureExpr b a)
              | PTrue
              deriving (Eq, Show)

instance Functor (Pred b)  where
  fmap f (Rel o p1 p2) = Rel o (fmap f p1) (fmap f p2)
  fmap f (PVal b ps)   = PVal b (fmap f <$> ps)
  fmap f (PEffect e)   = PEffect (fmap f e)
  fmap f (PConst c)    = PConst c
  fmap _ PTrue         = PTrue

data Const = CInt Int          
           | CPid Id
           | CPidSet Id
           deriving (Eq, Show, Generic)

instance Serialize Const 

data Op = Eq | Le | NEq | Plus | Minus
        deriving (Eq, Show)

litInt i a = EVal (Just (CInt (fromInteger i))) a
ePlus  = Rel Plus
eMinus = Rel Minus

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
 | EAny    { anyTy :: EffType b a, annot :: a }
 | ESymElt { symSet :: EffExpr b a, annot :: a }
 | EVar    { varId :: b, annot :: a }                          -- ^ x
 | ECon    { conId :: b, conArgs :: [EffExpr b a], annot :: a }
 | EField  { fieldExp :: EffExpr b a, fieldNo :: Int, annot :: a }
 | ELam    { lamId :: b, lamBody :: EffExpr b a, annot :: a }            -- ^ \x -> e
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
 | EType   { typeTy :: Type b, annot :: a }
 -- Processes
 | EPrimOp { primOp   :: PrimOp
           , primArgs :: [EffExpr b a]
           , annot    :: a
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
        go (Tr.ForAllTy v t)
          | Just n <- T.binderVar_maybe v
          = ELam (nameId (getName n)) (go t) a
        go t
          = EAny (EType (ofType tyConId nameId t) a) a
    
substs :: Subst b (EffExpr b a)
       => [b]
       -> [EffExpr b a]
       -> EffExpr b a
       -> EffExpr b a
substs froms tos e
  = foldl go e (zip froms tos)
  where
    go e (x,a) = subst x a e

simplify :: (Show a, Show b, Subst b (EffExpr b a))
         => EffExpr b a -> EffExpr b a
simplify (ECase t e alts md l)
  = fromMaybe defCase $ simplifyCasesMaybe e' alts'
  -- = case (e', alts') of
  --     (ECon c xs _, [(c', xs', eAlt)])
  --       | c == c' && length xs == length xs'
  --         -> substs xs' xs eAlt
  --     _   -> ECase t e' alts' md' l
  where
    defCase = ECase t e' alts' md' l
    e'      = simplify e
    alts'   = map (\(x,y,z) -> (x,y,simplify z)) alts
    md'     = simplify <$> md
    
simplify (EField e i l')
  = case e' of
      ECon _ as _ -> as !! i
      _           -> EField e' i l'
  where
    e' = simplify e
simplify (ERec f e l)
  = ERec f (simplify e) l
simplify (EPrRec x y e b xs l)
  = EPrRec x y (simplify e) (simplify b) (simplify xs) l
simplify (EApp e1 e2 l)
  = case e1' of
      ELam b m _           -> subst b e2' m
      ECase t e alts md l' -> simplifyCaseApp t e alts md l' e2' l
      _                    -> EApp e1' e2' l
  where
    e1' = simplify e1
    e2' = simplify e2 
simplify (EPrimOp op args l) = EPrimOp op (simplify <$> args) l
simplify (ECon c xs l)   = ECon c (simplify <$> xs) l
simplify (ELam b e l)    = ELam b (simplify e) l
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
  = subst b m e

substAlt x a (c, bs, e) = (c, bs, subst x a e)  

conEffExpr :: a -> T.Type -> DataCon -> EffExpr Id a  
conEffExpr l t d = ECon (dataConId d) [] l

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

class Ord b => Subst b a where
  subst   :: b -> a -> a -> a
  fv      :: a -> Set.Set b 

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
  ppPrec _ (EVal mv _) = maybe (text "⊥") pp mv
  ppPrec _ (ESymElt set _) = braces (text "_ ∈" <+> pp set)
  -- ppPrec _ (EVal (v,t,p) _)
  --   = braces (pp p)
  ppPrec _ (EField e i _)
    = pp e <> brackets (int i)
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
  ppPrec _ (Rel o p1 p2) = parens (pp p1) <+> pp o <+> parens (pp p2)
  ppPrec _ (PVal n [])   = pp n
  ppPrec _ (PVal n xs)   = parens (pp n <+> hcat (pp <$> xs))
  ppPrec _ (PEffect e)   = pp e
  ppPrec _ (PConst c)    = pp c
  ppPrec _ PTrue         = text "true"

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
  subst x t = go
    where
      go v@(TyVar x') | x == x'   = t
                      | otherwise = v
      go (TyApp t1 t2) = TyApp (go t1) (go t2)
      go (TyConApp b ts) = TyConApp b (go <$> ts)
      go (TyFun t1 t2) = TyFun (go t1) (go t2)

-- A dirty hack, but maybe not so dirty
substExpr :: (Avoid b, Annot a, Ord b)
          => Bool -> b -> EffExpr b a -> EffExpr b a -> EffExpr b a
substExpr b x a = go
    where
      go (EAny t l) = EAny (go t) l
      go (ESymElt set l) = ESymElt (go set) l
      go v@(EVal{}) = v
      -- go v@(EVal (b,t,p) l) = (EVal (b, t, (substPred x a p)) l)
      go v@(EVar x' _)
        = case a of
            EVar y' l | x == x' && b -> EVar y' l
            _         | x == x'      -> a
                      | otherwise    -> v
      go v@(ECon c as l)
        = ECon c (go <$> as) l
      go v@(EField e i l)
        = EField (go e) i l
      go g@(EPrRec a b f eb e0 l)
        | x == a || x == b = g
        | otherwise = EPrRec a' b' (go f') (go eb) (go e0) l
        where
          (ELam a' (ELam b' f' _) _) = go (ELam a (ELam b f dummyAnnot) dummyAnnot)
      go g@(ERec f e l)
        | f == x    = g
        | otherwise = ERec f (go (substExpr True f (EVar f' dummyAnnot) e)) l
        where
          f' = avoid (fv a) f
      go f@(ELam x' e l)
        | x == x'   = f
        | otherwise = ELam x'' (go (substExpr True x' (EVar x'' dummyAnnot) e)) l
        where
          x'' = avoid (fv a) x'
      go (ECase t e es d l)
        = ECase t (go e) (substAlt x a <$> es) (go <$> d) l
      go (EApp e1 e2 l)
        = EApp (go e1) (go e2) l
      go (EPrimOp o es l)
        = EPrimOp o (go <$> es) l
      go ty@(EType t l)
        = case a of
            EType t' l' -> EType (subst x t' t)  l
            _           -> ty

fvExpr :: (Avoid b, Annot a, Ord b) => EffExpr b a -> Set.Set b
fvExpr (EAny t _)      = fv t
fvExpr (ESymElt s _)   = fv s
fvExpr (EVal _ _)      = Set.empty
fvExpr (EVar x _)      = Set.singleton x
fvExpr (ECon x as _)   = Set.unions (fv <$> as)
fvExpr (EField e i _)  = fvExpr e
fvExpr (ERec f e _)    = fv e Set.\\ Set.singleton f
fvExpr (EPrRec x y f b e _) = Set.unions (fv <$> [f,b,e]) Set.\\ Set.fromList [x,y]
fvExpr (ELam x e _)    = fv e Set.\\ Set.singleton x
fvExpr (ECase t e es d l)= Set.unions ([fv e] ++ fvDefault d ++ fmap fvAlts es)
  where
    fvDefault Nothing   = []
    fvDefault (Just e)  = [fv e]
fvExpr (EApp e1 e2 _)   = fv e1 `Set.union` fv e2
fvExpr (EPrimOp o es _) = Set.unions (fv <$> es)
fvExpr (EType t _)      = Set.empty

fvAlts :: (Avoid b, Annot a, Ord b) => (b, [b], EffExpr b a) -> Set.Set b
fvAlts (_, xs, e) = fv e Set.\\ (Set.fromList xs)

fvPred :: (Avoid b, Annot a, Ord b) => Pred b a -> Set.Set b
fvPred (PVal v ps)   = Set.unions (fvPred <$> ps) Set.\\ Set.singleton v
fvPred (Rel _ p1 p2) = fvPred p1 `Set.union` fvPred p2
fvPred (PEffect e)   = fv e
fvPred PTrue         = Set.empty
fvPred (PConst _)    = Set.empty

class Avoid b where
  avoid :: Set.Set b -> b -> b

class Annot a where
  dummyAnnot :: a

instance Avoid Id where
  avoid fvs x
    | Set.member x fvs = avoid fvs (x ++ "'")
    | otherwise        = x

instance Annot () where
  dummyAnnot = ()

type TyAnnot  = (Maybe (Type Id), SrcSpan)
type AbsEff = EffExpr Id TyAnnot

data SpecTable a = SpecTable [SpecEntry a]
                 deriving (Show, Generic)
data SpecEntry a = Id :<=: EffExpr Id a
                   deriving (Show, Generic)

type AnnOut       = TyAnnot
type AnnIn        = Maybe (Type Id)
type SpecEntryOut = SpecEntry AnnOut
type SpecEntryIn  = SpecEntry AnnIn
type SpecTableOut = SpecTable AnnOut
type SpecTableIn  = SpecTable AnnIn

instance Serialize a => Serialize (SpecEntry a)
instance Serialize a => Serialize (SpecTable a)

instance Annot AnnIn where
  dummyAnnot = Nothing

lookupTable :: Id -> SpecTable a -> Maybe (EffExpr Id a)
lookupTable b (SpecTable es)
  = listToMaybe [ t | x :<=: t <- es ]

specTableToWords :: SpecTableIn -> String
specTableToWords = B8String.decode . B.unpack . encode

wordsToSpecTable :: String -> SpecTableIn    
wordsToSpecTable wds
  = case decode . B.pack . B8String.encode $ wds of 
      Left str -> abort "wordsToSpecTable" str
      Right t  -> t

data BriskAnnot = AnnotModule

