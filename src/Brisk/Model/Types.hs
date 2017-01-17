{-# LANGUAGE DeriveFunctor #-}
{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language GADTs #-}
module Brisk.Model.Types where

import GhcPlugins (showSDoc, unsafeGlobalDynFlags, ppr)
import Brisk.Pretty
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
import qualified Type as T
import qualified TypeRep as Tr

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
           deriving (Eq, Show)
              
data Op = Eq | Le | NEq | Plus | Minus
        deriving (Eq, Show)

pVar v a      = PEffect (var v a)
pInt v i a    = (v, intTy, Rel Eq (pVar v a) (PConst (CInt i)))
pSingle v x a = pVar v `eSingle` pVar x a
eSingle v e a = (v, Rel Eq (pVar v a) e)
pExpr v o e a = (v, Rel o (pVar v a) e)
ePlus  = Rel Plus
eMinus = Rel Minus

type Subset b a = (b, T.Type, Pred b a)
data EffExpr b a =
   EVal    { valPred :: Subset b a, annot :: a }                -- ^ {v | p}
 | ECon    { conId :: b, conArgs :: [EffExpr b a], annot :: a }
 | EField  { fieldExp :: EffExpr b a, fieldNo :: Int, annot :: a }
 | EVar    { varId :: b, annot :: a }                          -- ^ x
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
 | ECase   { caseTy :: T.Type
           , caseArg :: EffExpr b a
           , caseAlts :: [(b, [b], EffExpr b a)]
           , caseDft :: (Maybe (EffExpr b a))
           , annot :: a
           }
 | EType   { typeTy :: T.Type, annot :: a }
 -- Processes
 | EProcess { procProc :: Process b a, procRet :: EffExpr b a, annot :: a }
 | EBind    { bindFst :: EffExpr b a, bindSnd :: EffExpr b a, annot :: a }
 | EReturn  { retExp :: EffExpr b a, annot :: a }
 | Send     { sendTy :: EffType b a, sendPid :: EffExpr b a, sendMsg :: EffExpr b a, annot ::  a } -- ^ send(type, p, msg)
 | Recv     { recvTy :: EffType b a, annot :: a }
 | Spawn    { spawnProc :: Process b a, annot :: a }
 | SymSpawn { symSpawnSet :: EffExpr b a, symSpawnProc :: Process b a, annot ::  a } -- ^ symspawn(xs, p)
 | Self     { annot :: a }
   deriving (Eq, Show, Functor)

type Process b a  = EffExpr b a
type EffType b a  = EffExpr b a
type PureExpr b a = EffExpr b a

-- | Convenient Syntax
var = EVar
lam = ELam
app = EApp
ret = EReturn
fix = ERec
bind = EBind
x $>>$ y    = bind x y ()
x $->$ y    = lam x y ()
x $@$ y     = app x y ()
infixr $->$
infixl $@$

----------------------------------------------- 
-- | Operations on Expressions  
----------------------------------------------- 
substs :: Subst b (EffExpr b a)
       => [b]
       -> [EffExpr b a]
       -> EffExpr b a
       -> EffExpr b a
substs froms tos e
  = foldl go e (zip froms tos)
  where
    go e (x,a) = subst x a e

simplify :: (Show a, Show b, Subst b (EffExpr b a)) => EffExpr b a -> EffExpr b a
simplify (ECase t e alts md l)
  = case (e, alts) of
      (ECon c xs _, [(c', xs', eAlt)])
        | c == c' && length xs == length xs'
          -> substs xs' xs eAlt
      _   -> ECase t e' alts' md' l
  where
    e'    = simplify e
    alts' = map (\(x,y,z) -> (x,y,simplify z)) alts
    md'   = simplify <$> md
    
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
simplify (EBind e1 e2 l) = EBind (simplify e1) (simplify e2) l
simplify (ECon c xs l)   = ECon c (simplify <$> xs) l
simplify (ELam b e l)    = ELam b (simplify e) l
simplify (EReturn e l)   = EReturn (simplify e) l
simplify (Send t p m l)  = Send t (simplify p) (simplify m) l
simplify r@Recv{}        = r
simplify t@EType{}       = t
simplify x@EVar{}        = x
simplify s@Self{}        = s
simplify e = abort "simplify" e

simplifyCaseApp :: forall a b. (Show a, Show b, Subst b (EffExpr b a))
                => Tr.Type
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
  | otherwise        = nameId (getName d)

vv :: Id
vv = "#vv"

exprString :: Pretty (EffExpr b a) => EffExpr b a -> String
exprString e = render (pp e)

class Ord b => Subst b a where
  subst   :: b -> a -> a -> a
  fv      :: a -> Set.Set b 

class ToTyVar b where
  toTyVar :: b -> T.TyVar

instance (Pretty b, Eq b) => Pretty (EffExpr b a) where
  ppPrec _ (EVal (v,t,Rel Eq (PEffect (EVar v' _)) e) _)
    | v == v' = pp e
  ppPrec _ (EVal (v,t,p) _)
    = braces (pp p)
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
    = parensIf (z > 7) (text "\\" <> spaces xs <+> text "->" $$ nest 2 (ppPrec 7 e))
    where
      (xs, e)         = collectArgs f
  ppPrec z (EReturn e _)
    = text "return" <+> ppPrec z e
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
    -- = text "rec" <+> ppPrec z b <> text "." $$ nest 2 (ppPrec z e)


  ppPrec z (EBind e1 e2 _) = text "do" <+> nest 3 (vcat (body e1 e2))
    where
      body e1 (ELam b e2 _) = [pp b <+> text "<-" <+> pp e1] ++ go e2
      -- body e1 (ELam b e2 _) = pp b <+> text "<-" <+> pp e1 $$ go e2
      body e1 e2            = [pp e1, pp e2]
      -- body e1 e2            = pp e1 $$ pp e2
      go (EBind e1 e2 _)    = body e1 e2
      go e                  = [pp e]
  
  ppPrec _ (EProcess p e _) = pp p <> brackets (pp e)
  ppPrec _ (Send t p m _)   = text "$send"  <> brackets (pp t) <> parens (hcat (punctuate comma [pp p, pp m]))
  ppPrec _ (Recv t _)       = text "$expect"  <> brackets (pp t)
  ppPrec _ (Spawn p _)      = text "$spawn" <> parens (parens (pp p))
  ppPrec _ (SymSpawn xs p _)= text "$symSpawn" <> (parens (pp xs <> comma <+> pp p))
  ppPrec _ (Self _)         = text "$getSelfPid"
  ppPrec _ (EType t _)      = pp t

instance Pretty Const where
  ppPrec _ (CInt i) = int i

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

instance (Avoid b, Annot a, ToTyVar b, Ord b) => Subst b (EffExpr b a) where
  fv    = fvExpr
  subst = substExpr False

-- A dirty hack, but maybe not so dirty
substExpr :: (Avoid b, Annot a, ToTyVar b,  Ord b)
          => Bool -> b -> EffExpr b a -> EffExpr b a -> EffExpr b a
substExpr b x a = go
    where
      go v@(EVal (b,t,p) l) = (EVal (b, t, (substPred x a p)) l)
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
      go (EReturn e l)
        = EReturn (go e) l
      go (EBind e1 e2 l)
        = EBind (go e1) (go e2) l
      go (EProcess p e l)
        = EProcess (substExpr b x a p) (go e) l

      go (Send t p m l)   = Send (go t) (go p) (go m) l
      go (Recv t l)       = Recv (go t) l
      go (Spawn p l)      = Spawn (go p) l
      go (Self l)         = Self l
      go (SymSpawn e p l) = SymSpawn (go e) (go p) l
      go ty@(EType t l)
        = case a of
            EType t' l' -> EType (T.substTy tysubst t) l
              where
                tysubst = T.zipOpenTvSubst [toTyVar x] [t']
            _           -> ty

      substPred _ _ PTrue        = PTrue
      substPred x a (PVal n ps)  = PVal n (substPred x a <$> ps)
      substPred _ _ p@(PConst _) = p
      substPred x a (Rel o p1 p2) = Rel o (substPred x a p1) (substPred x a p2)
      substPred x a (PEffect e)   = PEffect (substExpr b x a e)

fvExpr :: (Avoid b, Annot a, ToTyVar b, Ord b) => EffExpr b a -> Set.Set b
fvExpr (EVal (b,_,p) _) = fvPred p Set.\\ Set.singleton b
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
fvExpr (EReturn e _ )   = fv e
fvExpr (EBind e1 e2 _)  = fv e1 `Set.union` fv e2
fvExpr (EProcess p e _) = fv p `Set.union` fv e
fvExpr (Send t p m l)   = fv p `Set.union` fv m
fvExpr (Recv _ _)       = Set.empty
fvExpr (Spawn p _)      = fv p
fvExpr (SymSpawn e p _) = fv e `Set.union` fv p
fvExpr (Self _)         = Set.empty
fvExpr (EType t _)      = Set.empty

fvAlts :: (Avoid b, Annot a, ToTyVar b, Ord b) => (b, [b], EffExpr b a) -> Set.Set b
fvAlts (_, xs, e) = fv e Set.\\ (Set.fromList xs)

fvPred :: (Avoid b, Annot a, ToTyVar b, Ord b) => Pred b a -> Set.Set b
fvPred (PVal v ps)   = Set.unions (fvPred <$> ps) Set.\\ Set.singleton v
fvPred (Rel _ p1 p2) = fvPred p1 `Set.union` fvPred p2
fvPred (PEffect e)   = fv e
fvPred PTrue         = Set.empty
fvPred (PConst _)    = Set.empty

-- caSubst :: (Annot a, Avoid b, Subst b a) => b -> EffExpr b a -> EffExpr b a -> EffExpr b a
-- caSubst x t' e@(ELam y t a)
--   | x == y    = e
--   | otherwise = 
--   where
--     y' = avoid (fv t') y
-- caSubst x t' (ELam y t a)
--   = undefined

-- avoidFvs :: (Annot a, Avoid b, Subst b a,  Ord b) => Set.Set b -> EffExpr b a -> EffExpr b a  
-- avoidFvs fvs (ELam x t a)
--   = ELam y (caSubst x (EVar y noAnnot) t) a
--   where
--     y = avoid fvs x
-- avoidFvs fvs (ERec x t a)
--   = ERec y (caSubst x (EVar y noAnnot) t) a
--   where
--     y = avoid fvs x
-- avoidFvs fvs (

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
