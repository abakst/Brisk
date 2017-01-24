{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TupleSections #-}
{-# Language TemplateHaskell #-}
{-# Language DeriveGeneric #-}
module Brisk.Model.EmbedCore where

import GHC.Generics
import Data.List
import Control.Applicative hiding (Const)
import Control.Monad
import Brisk.Model.GhcInterface
import Brisk.Model.Types
import Brisk.UX
import Unique
import Data.Maybe
import OccName
import CoreSyn
import ConLike
import GhcPlugins hiding (Id, idType)
import TcRnMonad
import DynamicLoading
import IfaceEnv
import Linker
import TypeRep
import Generics.Deriving.TH
import Data.Serialize
import Data.Data hiding (mkTyConApp)
import Data.Word
import GHC.Word

-- type Ann         = (Maybe Type, SrcSpan)
-- type EffExprBare = EffExpr Id Ann
type EffExprOut = EffExpr Id AnnOut
type EffExprIn  = EffExpr Id AnnIn

-------------------------------------------
-- Functions for *retrieving* specifications
-------------------------------------------
tabOccName  = mkVarOcc "brisk_tab__"
tabName mod = do u <- getUniqueM
                 return $ mkExternalName u mod tabOccName noSrcSpan

retrieveAllSpecs :: HscEnv -> ModGuts -> CoreM [SpecTableIn]
retrieveAllSpecs env mg
  = catMaybes <$> mapM (retrieveIfExport env mg) mods
  where
    mods = usedModules mg
    retrieveIfExport env mg mod
      = whenExports env mg mod tabOccName $ retrieveSpecs env mod

type WordList = [Word]
retrieveSpecs :: HscEnv -> Module -> CoreM SpecTableIn
retrieveSpecs env mod
  = do origNm <- liftIO . initTcForLookup env $
         lookupOrig mod tabOccName
       specTableTy  <- tyFromName env ''WordList
       words <- liftIO $ getValueSafely env origNm specTableTy
       case words of
         Nothing -> abort "retrieveSpecs" ":("
         Just words' -> return (wordsToSpecTable words')

-------------------------------------------
-- Functions for *embedding* specifications
-------------------------------------------
tyFromName env nm
  = do n     <- thNameToGhcName nm
       liftIO $ mkTyConTy <$> initTcForLookup env (lookupTyCon $ fromJust n)

embedSpecTable :: Module -> [Name] -> SpecTableOut -> CoreM CoreBind
embedSpecTable mod names tab@(SpecTable entries)
  = do t      <- tabName mod
       return $ NonRec (mkExportedLocalId VanillaId t ty) wordList
         where
           wordExp  = mkWordExprWord unsafeGlobalDynFlags
           entries' = [ x :<=: fmap fst t | x :<=: t <- entries, x `elem` ids ]
           ids      = nameId <$> names
           words    = wordExp <$> specTableToWords (SpecTable entries')
           wordList = mkExprList (Type wordTy) words
           ty       = mkTyConApp listTyCon [wordTy]

mkExprList :: CoreExpr -> [CoreExpr] -> CoreExpr
mkExprList ty es
  = foldr cons nil es
  where
    cons e1 e2 = mkCoreConApps consDataCon [ty,e1,e2]
    nil        = mkCoreConApps nilDataCon  [ty]
