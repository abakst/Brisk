{-# LANGUAGE BangPatterns #-}

module Brisk.Transform.SpanStack
   ( -- * Stack of positions
     Span (..)
   , SpanStack

     -- * Creating Stacks
   , empty, push

     -- * Using Stacks
   , srcSpan

     -- * Creating general spans
   , showSpan
   , showPpr
   ) where

import           Prelude                   hiding (error)
import           GhcPlugins                hiding (empty, Tick, Var)
import           SrcLoc
import qualified Var
import           CoreSyn                   hiding (Tick, Var)
import           Name
import           FastString                       (fsLit)
import           Data.Maybe                       (listToMaybe, fromMaybe)
import           Brisk.Transform.Misc (tickSrcSpan)

-- | Opaque type for a stack of spans
newtype SpanStack = SpanStack { unStack :: [(Span, SrcSpan)] }

--------------------------------------------------------------------------------
empty :: SpanStack
--------------------------------------------------------------------------------
empty = SpanStack []

--------------------------------------------------------------------------------
push :: Span -> SpanStack -> SpanStack
--------------------------------------------------------------------------------
push !s stk -- @(SpanStack stk)
  | Just sp <- spanSrcSpan s = SpanStack ((s, sp) : unStack stk)
  | otherwise                = stk

-- | A single span
data Span
  = Var  !Var.Var           -- ^ binder for whom we are generating constraint
  | Tick !(Tickish Var.Var) -- ^ nearest known Source Span

instance Show Span where
  show (Var x)   = showSDocDebug unsafeGlobalDynFlags (ppr (getName x))
  show (Tick tt) = showPpr unsafeGlobalDynFlags tt

--------------------------------------------------------------------------------
srcSpan :: SpanStack -> SrcSpan
--------------------------------------------------------------------------------
srcSpan s  = fromMaybe noSpan (mbSrcSpan s)
  where
    noSpan = showSpan "Yikes! No source information"

mbSrcSpan :: SpanStack -> Maybe SrcSpan
mbSrcSpan = fmap snd . listToMaybe  . unStack

spanSrcSpan :: Span -> Maybe SrcSpan
spanSrcSpan      = maybeSpan Nothing . go
  where
    go (Var x)   = getSrcSpan x
    go (Tick tt) = tickSrcSpan tt

maybeSpan :: Maybe SrcSpan -> SrcSpan -> Maybe SrcSpan
maybeSpan d sp
  | isGoodSrcSpan sp = Just sp
  | otherwise        = d

--------------------------------------------------------------------------------
showSpan :: (Show a) => a -> SrcSpan
--------------------------------------------------------------------------------
showSpan = mkGeneralSrcSpan . fsLit . show
