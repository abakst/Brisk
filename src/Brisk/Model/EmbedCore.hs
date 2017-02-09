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
import LoadIface (loadInterfaceForModule)

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
  = catMaybes <$> mapM (retrieveIfExport env mg) (usedModules mg)
  where
    retrieveIfExport env mg mod
      = whenExports env mg mod tabOccName $ retrieveSpecs env mod

retrieveSpecs :: HscEnv -> Module -> CoreM SpecTableIn
retrieveSpecs env mod
  = do origNm <- liftIO . initTcForLookup env $ do
         loadInterfaceForModule (text "retrieveSpecs") mod
         lookupOrig mod tabOccName
       liftIO $ do
         linkModule env mod
         hv <- getHValue env origNm  :: IO HValue
         v  <- lessUnsafeCoerce unsafeGlobalDynFlags "retrieveSpecs" hv
         return (wordsToSpecTable v)
       -- Is the above even safe ^^^^ ????
       -- Can this safely be deleted (???):
       -- liftIO $ putStrLn "HERE"
       -- words <- liftIO $ getValueSafely env origNm stringTy
       -- case words of
       --   Nothing -> abort "retrieveSpecs" ":("
       --   Just words' -> return (wordsToSpecTable words')

-------------------------------------------
-- Functions for *embedding* specifications
-------------------------------------------
tyFromName env nm
  = do n     <- thNameToGhcName nm
       liftIO $ mkTyConTy <$> initTcForLookup env (lookupTyCon $ fromJust n)

embedSpecTable :: Module -> [Name] -> SpecTableOut -> CoreM CoreBind
embedSpecTable mod names tab@(SpecTable entries)
  = do t      <- tabName mod
       encoded <- mkStringExpr str
       return $ NonRec (mkExportedLocalId VanillaId t ty) encoded
         where
           entries' = [ x :<=: fmap fst t | x :<=: t <- entries, x `elem` ids ]
           ids      = nameId <$> names
           str      = specTableToWords (SpecTable entries')
           ty       = stringTy

mkExprList :: CoreExpr -> [CoreExpr] -> CoreExpr
mkExprList ty es
  = foldr cons nil es
  where
    cons e1 e2 = mkCoreConApps consDataCon [ty,e1,e2]
    nil        = mkCoreConApps nilDataCon  [ty]
