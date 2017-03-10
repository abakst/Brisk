{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module Brisk.Transform.Misc where

import           Class                                      (classKey)
import           Data.String
import           PrelNames                                  (fractionalClassKeys)

import           Debug.Trace

import           DataCon                                    (isTupleDataCon)
import           Prelude                                    hiding (error)
import           Avail                                      (availsToNameSet)
import           BasicTypes                                 (Arity)
import           CoreSyn                                    hiding (Expr, sourceName)
import qualified CoreSyn                                    as Core
import           CostCentre
import           GHC                                        hiding (L)
import           HscTypes                                   (Dependencies, ImportedMods, ModGuts(..), HscEnv(..), FindResult(..))
import           NameSet                                    (NameSet)
import           SrcLoc                                     hiding (L)
import           Bag
import           ErrUtils
import           CoreLint
import           CoreMonad

-- import           Text.Parsec.Pos                            (sourceName, sourceLine, sourceColumn, newPos)

import           Name
import           Module                                     (moduleNameFS)
import           Unique
import           Finder                                     (findImportedModule, cannotFindModule)
import           Panic                                      (throwGhcException)
import           FastString
import           TcRnDriver
-- import           TcRnTypes


import           RdrName
import           Type                                       (liftedTypeKind)
import           Var
import           IdInfo
import qualified TyCon                                      as TC
import           Data.Char                                  (isLower, isSpace)
import           Data.Maybe                                 (isJust, fromMaybe)
import           Data.Hashable
import qualified Data.HashSet                               as S

import qualified Data.Text.Encoding                         as T
import qualified Data.Text                                  as T
import           Control.Arrow                              (second)
import           Control.Monad                              ((>=>))
import           Outputable                                 (Outputable (..), text, ppr)
import qualified Outputable                                 as Out
import           DynFlags
import qualified Text.PrettyPrint.HughesPJ                  as PJ
-- import           Language.Fixpoint.Types                    hiding (L, Loc (..), SrcSpan, Constant, SESearch (..))
-- import qualified Language.Fixpoint.Types                    as F
-- import           Language.Fixpoint.Misc                     (safeHead, safeLast, safeInit)
-- import           Language.Haskell.Liquid.Desugar710.HscMain
import           Control.DeepSeq
-- import           Language.Haskell.Liquid.Types.Errors

--------------------------------------------------------------------------------
-- | Datatype For Holding GHC ModGuts ------------------------------------------
--------------------------------------------------------------------------------

data MGIModGuts = MI {
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: !ImportedMods
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  , mgi_exports   :: !NameSet
  , mgi_cls_inst  :: !(Maybe [ClsInst])
  }

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote cc _ _) = cc_loc cc
tickSrcSpan (SourceNote ss _) = RealSrcSpan ss
tickSrcSpan _                 = noSrcSpan
