{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
module Brisk.Model.Types where

import Brisk.Pretty
import Text.PrettyPrint.HughesPJ

import Data.List
import Id
import Type

data Pred b = Rel Op (Pred b) (Pred b)
            | PVar b
            | PTrue
              
data Op = Eq | Le | NEq

pSingle v x = (v, Rel Eq (PVar v) (PVar x))

data EffExpr b a =
   EVal    (b, Pred b) a
 | EVar    b  a
 | ELam    b  (EffExpr b a) a 
 | EApp    (EffExpr b a) (EffExpr b a) a
 | EReturn (EffExpr b a) a
 | ERec    b  (EffExpr b a) a
 | ECase   (EffExpr b a) [(b, [b], EffExpr b a)] (Maybe (EffExpr b a))
 | EBind   (EffExpr b a) (EffExpr b a) a
 | EType   Type
 -- Processes
 | EProcess (Process b a) (EffExpr b a) a
 | Send     (EffExpr b a) (EffExpr b a)
 | Recv     (EffType b a)

type Process b a = EffExpr b a
type EffType b a = EffExpr b a

-- | Convenient Syntax
var b     = EVar b ()
lam b e   = ELam b e ()
app e1 e2 = EApp e1 e2 () 
ret e     = EReturn e ()
fix f e   = ERec f e ()
bind m f  = EBind m f ()
($>>$)    = bind
($->$)    = lam
($@$)     = app
infixr $->$
infixl $@$

class Eq b => Subst b a where
  subst :: b -> a -> a -> a

instance (Pretty Type, Pretty b) => Pretty (EffExpr b a) where
  pp (EVal (v,p) _)   = pp p
  pp (ECase e es d)   = ppCases e es d
  pp (EVar b _)       = pp b
  pp (EApp e1 e2 _)   = parens (pp e1 <+> pp e2)
  pp f@(ELam _ _ _)   = text "\\" <> spaces xs <+> text "->" $$ nest 2 (pp e)
    where
      (xs, e)         = collectArgs f
  pp (EReturn e _)    = text "return" <+> pp e
  pp (ERec b e _)     = text "rec" <+> pp b <> text "." $$ nest 2 (pp e)

  pp  (EBind e1 e2 _) = text "do" <+> nest 0 (body e1 e2)
    where
      body e1 (ELam b e2 _) = pp b <+> text "<-" <+> pp e1 $$ go e2
      body e1 e2            = pp e1 $$ pp e2
      go (EBind e1 e2 _)    = body e1 e2
      go e                  = pp e
  
  pp (EProcess p e _) = braces (pp p) <> brackets (pp e)
  pp (Send p m) = text "send" <> parens (hcat (punctuate comma [pp p, pp m]))
  pp (Recv t)   = text "recv" <> brackets (pp t)
  pp (EType t)  = pp t


instance Pretty b => Pretty (Pred b) where
  pp (Rel o p1 p2) = parens (pp p1) <+> pp o <+> parens (pp p2)
  pp (PVar b)      = pp b
  pp (PTrue)       = text "true"

instance Pretty Op where
  pp Eq  = text "="
  pp NEq = text "!="
  pp Le  = text "<"

collectArgs (ELam b e _) = go [b] e
  where
    go bs (ELam b' e' _) = go (b':bs) e'
    go bs e'             = (reverse bs, e')

ppCases e es d
  = text "case" <+> pp e <+> text "of" $$ nest 2 (vcat alts)
  where
    alts           = (alt1 <$> es) ++ [dalt]
    alt1 (c,bs,e') = pp c <+> spaces bs <+> text "->" $$ nest 2 (pp e')
    dalt           = maybe empty ((text "_" <+> text "->" <+>) . pp) d

spaces :: Pretty a => [a] -> Doc
spaces = foldl (<+>) empty . map pp     
  
instance Eq b => Subst b (EffExpr b a) where
  subst x a = go
    where
      go v@(EVal _ _) = v
      go v@(EVar x' _)
        | x == x'   = a
        | otherwise = v
      go g@(ERec f e l)
        | f == x    = g
        | otherwise = ERec f (go e) l
      go f@(ELam x' e l)
        | x == x'   = f
        | otherwise = ELam x' (go e) l
      go (ECase e es d)
        = ECase (go e) (substAlt x a <$> es) (go <$> d)
      go (EApp e1 e2 l)
        = EApp (go e1) (go e2) l
      go (EReturn e l)
        = EReturn (go e) l
      go (EBind e1 e2 l)
        = EBind (go e1) (go e2) l
      go (EProcess p e l)
        = EProcess (subst x a p) (go e) l
      go (Send p m) = Send (subst x a p) (subst x a m)
      go (Recv t)   = Recv (subst x a t)
      go (EType t)  = EType t

substAlt x a (c, bs, e) = (c, bs, subst x a e)  
