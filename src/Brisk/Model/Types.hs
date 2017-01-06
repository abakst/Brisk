{-# LANGUAGE DeriveFunctor #-}
{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
module Brisk.Model.Types where

import GhcPlugins (showSDoc, unsafeGlobalDynFlags, ppr)
import Brisk.Pretty
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

nameId :: Name -> String
nameId = occNameString . getOccName


-----------------------------------------------  
--  Specification Language (Preds, Exprs, Types)
----------------------------------------------- 
data Type b = TConApp b [Type b]
              | TApp (Type b) (Type b)
              | TFun (Type b) (Type b)
              | TVar b
              deriving (Eq, Show, Functor)

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

tInt :: Type Id
tInt = TConApp "Int" []

pVar v a      = PEffect (var v a)
pInt v i a    = (v, tInt, Rel Eq (pVar v a) (PConst (CInt i)))
pSingle v x a = pVar v `eSingle` pVar x a
eSingle v e a = (v, Rel Eq (pVar v a) e)
pExpr v o e a = (v, Rel o (pVar v a) e)
ePlus e1 e2   = Rel Plus e1 e2
eMinus e1 e2  = Rel Minus e1 e2

type Subset b a = (b, Type b, Pred b a)
data EffExpr b a =
   EVal    (Subset b a) a                -- ^ {v | p}
 | ECon    (Type b) b [EffExpr b a] a
 | EVar    b a                          -- ^ x
 | ELam    b (EffExpr b a) a            -- ^ \x -> e
 | EApp    (EffExpr b a) (EffExpr b a) a
 | EPrRec  b b (EffExpr b a) (EffExpr b a) (EffExpr b a) a -- ^ R (\X x -> e, E, X0)
 | ERec    b  (EffExpr b a) a
 | ECase   (Type b) (EffExpr b a) [(b, [b], EffExpr b a)] (Maybe (EffExpr b a)) a
 | EType   (Type b) a
 -- Processes
 | EProcess (Process b a) (EffExpr b a) a
 | EBind   (EffExpr b a) (EffExpr b a) a
 | EReturn (EffExpr b a) a
 | Send     (EffType b a) (EffExpr b a) (EffExpr b a) a -- ^ send(type, p, msg)
 | Recv     (EffType b a) a
 | Spawn    (Process b a) a
 | SymSpawn (EffExpr b a) (Process b a) a -- ^ symspawn(xs, p)
 | Self     a
   deriving (Eq, Show, Functor)

type Process b a  = EffExpr b a
type EffType b a  = EffExpr b a
type PureExpr b a = EffExpr b a

-- | Convenient Syntax
var b a     = EVar b a
lam b e a   = ELam b e a
app e1 e2 a = EApp e1 e2 a
ret e a     = EReturn e a
fix f e a   = ERec f e a
bind m f a  = EBind m f a
x $>>$ y    = bind x y ()
x $->$ y    = lam x y ()
x $@$ y     = app x y ()
infixr $->$
infixl $@$

----------------------------------------------- 
-- | Operations on Types  
----------------------------------------------- 
ofType :: (Name -> b) -> T.Type -> Type b 
ofType f (Tr.TyVarTy a)
  = TVar (f . getName $ a)
ofType f (Tr.FunTy t t')
  = TFun (ofType f t) (ofType f t')
ofType f (Tr.TyConApp c ts)
  | Just (as, t) <- synTyConDefn_maybe c
  = undefined
  | otherwise
  = TConApp (f . getName $ c) (ofType f <$> ts)
ofType _ t
  = error ("ofType: " ++ showSDoc unsafeGlobalDynFlags (ppr t))

----------------------------------------------- 
-- | Operations on Expressions  
----------------------------------------------- 

simplify :: Subst b (EffExpr b a) => EffExpr b a -> EffExpr b a
simplify (EApp (ELam b m _) e _)
  = subst b e' m'
  where
    e' = simplify e
    m' = simplify m
simplify (EApp e1 e2 l)  = EApp (simplify e1) (simplify e2) l
simplify (EBind e1 e2 l) = EBind (simplify e1) (simplify e2) l
simplify e = e

unfoldRec :: Subst b (EffExpr b a) => EffExpr b a -> EffExpr b a
unfoldRec m@(ERec b e l)
  = subst b m e

substAlt x a (c, bs, e) = (c, bs, subst x a e)  

conEffExpr :: a -> T.Type -> DataCon -> EffExpr Id a  
conEffExpr l t d = ECon (ofType (nameId) t) (dataConId d) [] l

apConEff :: EffExpr b a -> EffExpr b a -> EffExpr b a
apConEff (ECon t d args l) a = ECon t d (args ++ [a]) l

dataConId :: DataCon -> Id
dataConId d
  | d == unitDataCon = "#unit"
  | otherwise        = nameId (dataConName d)

vv :: Id
vv = "#vv"

exprString :: Pretty (EffExpr b a) => EffExpr b a -> String
exprString e = render (pp e)

class Ord b => Subst b a where
  subst :: b -> a -> a -> a
  fv    :: a -> Set.Set b 

instance (Pretty b, Eq b) => Pretty (EffExpr b a) where
  ppPrec _ (EVal (v,t,Rel Eq (PEffect (EVar v' _)) e) _)
    | v == v' = pp e
  ppPrec _ (EVal (v,t,p) _)
    = braces (pp p)
  ppPrec _ (ECon t c [] _)
    = pp c <+> text "::" <+> pp t
  ppPrec _ (ECon t c as _)
    = parens (pp c <> parens (hcat (punctuate comma (ppPrec 9 <$> as)))
              <+> text "::" <+> pp t)
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
  ppPrec _ (Self _)         = text "$getSelfPid"
  ppPrec _ (EType t _)      = pp t

instance Pretty Const where
  ppPrec _ (CInt i) = int i

instance Pretty b => Pretty (Type b) where
  ppPrec z (TConApp c ts)
    = text "@" <> ppPrec 0 c <> brackets (spaces ts)
  ppPrec z (TVar t)
    = ppPrec z t

instance (Pretty b, Pretty (EffExpr b a)) => Pretty (Pred b a) where
  ppPrec _ (Rel o p1 p2) = parens (pp p1) <+> pp o <+> parens (pp p2)
  ppPrec _ (PVal n [])   = pp n
  ppPrec _ (PVal n xs)   = parens (pp n <+> hcat (pp <$> xs))
  ppPrec _ (PEffect e)   = pp e
  ppPrec _ (PConst c)    = pp c
  ppPrec _ (PTrue)       = text "true"

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

instance Ord b => Subst b (Type b) where
  fv (TConApp b ts)  = Set.unions (fv <$> ts)
  fv (TApp t t')     = Set.union (fv t) (fv t')
  fv (TFun t t')     = Set.union (fv t) (fv t')
  fv (TVar a)        = Set.singleton a

  subst x t (TConApp b ts)
    = TConApp b (subst x t <$> ts)
  subst x t (TApp t1 t2)
    = TApp (subst x t t1) (subst x t t2)
  subst x t (TFun t1 t2)
    = TFun (subst x t t1) (subst x t t2)
  subst x t (TVar a)
    | x == a    = t
    | otherwise = TVar a

instance Ord b => Subst b (EffExpr b a) where
  fv a = fvExpr a
  subst x a = go
    where
      go v@(EVal (b,t,p) l) = (EVal (b, t, (substPred x a p)) l)
      go v@(EVar x' _)
        | x == x'   = a
        | otherwise = v
      go v@(ECon t c as l)
        = ECon (goType t) c (go <$> as) l
      go g@(EPrRec a b f eb e0 l)
        | x == a || x == b = g
        | otherwise = EPrRec a b (go f) (go eb) (go e0) l
      go g@(ERec f e l)
        | f == x    = g
        | otherwise = ERec f (go e) l
      go f@(ELam x' e l)
        | x == x'   = f
        | otherwise = ELam x' (go e) l
      go (ECase t e es d l)
        = ECase t (go e) (substAlt x a <$> es) (go <$> d) l
      go (EApp e1 e2 l)
        = EApp (go e1) (go e2) l
      go (EReturn e l)
        = EReturn (go e) l
      go (EBind e1 e2 l)
        = EBind (go e1) (go e2) l
      go (EProcess p e l)
        = EProcess (subst x a p) (go e) l

      go (Send t p m l)   = Send (go t) (go p) (go m) l
      go (Recv t l)       = Recv (go t) l
      go (Spawn p l)      = Spawn (go p) l
      go (Self l)         = Self l
      go (SymSpawn e p l) =  SymSpawn (go e) (go p) l
      go (EType t l)      = EType t l

      goType t
        | x `elem` fv t
        = case a of
            EType t' l -> subst x t' t
            _        -> error "substitution with non type!"
        | otherwise
        = t

      substPred _ _ PTrue        = PTrue
      substPred x a (PVal n ps)  = PVal n (substPred x a <$> ps)
      substPred _ _ p@(PConst _) = p
      substPred x a (Rel o p1 p2) = Rel o (substPred x a p1) (substPred x a p2)
      substPred x a (PEffect e)   = PEffect (subst x a e)

fvExpr :: Ord b => EffExpr b a -> Set.Set b
fvExpr (EVal (b,_,p) _) = fvPred p Set.\\ Set.singleton b
fvExpr (EVar x _)      = Set.singleton x
fvExpr (ECon t x as _) = Set.unions (fv <$> as)
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

fvAlts :: Ord b => (b, [b], EffExpr b a) -> Set.Set b
fvAlts (_, xs, e) = fv e Set.\\ (Set.fromList xs)

fvPred :: Ord b => Pred b a -> Set.Set b
fvPred (PVal v ps)   = Set.unions (fvPred <$> ps) Set.\\ Set.singleton v
fvPred (Rel _ p1 p2) = fvPred p1 `Set.union` fvPred p2
fvPred (PEffect e)   = fv e
fvPred PTrue         = Set.empty
fvPred (PConst _)    = Set.empty
