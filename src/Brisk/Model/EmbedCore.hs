{-# LANGUAGE TupleSections #-}
{-# Language TemplateHaskell #-}
module Brisk.Model.EmbedCore where

import Control.Applicative
import Brisk.Model.GhcInterface
import Brisk.Model.Types
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

type Ann         = ()
type EffExprBare = EffExpr Id Ann
type SubsetBare  = Subset Id Ann

-------------------------------------------
-- Functors for *retrieving* specifications
-------------------------------------------
tabName mod = mkExternalName (mkUnique 't' 0) mod (mkVarOcc "brisk_tab__") noSrcSpan

retrieveSpecs :: HscEnv -> Module -> CoreEmbedder -> CoreM (Maybe EffExprBare)
retrieveSpecs env mod ce
  = do liftIO $ putStrLn "retrieveSpecs"
       liftIO $ putStrLn (showSDoc unsafeGlobalDynFlags (pprModuleName (moduleName mod)))
       origNm <- liftIO $ initTcForLookup env $ do
         lookupOrig mod (getOccName nm) -- >>= lookupId
       liftIO $ putStrLn (showSDoc unsafeGlobalDynFlags (ppr origNm))
       liftIO $ forceLoadNameModuleInterface env (ppr origNm) origNm
       liftIO $ putStrLn "ASDF"
       liftIO $ linkModule env mod
       liftIO $ lookupTypeHscEnv env origNm
       liftIO $ putStrLn "BAR"
       effTy  <- tyFromName env ''EffExprBare
       -- liftIO $ initTcInteractive env
       liftIO $ putStrLn "BAZ"
       liftIO $ getValueSafely env origNm effTy
  where nm = tabName mod

-------------------------------------------
-- Functors for *embedding* specifications
-------------------------------------------
tyFromName env nm
  = do n     <- thNameToGhcName nm
       liftIO $ mkTyConTy <$> initTcForLookup env (lookupTyCon $ fromJust n)

dcFromName env nm
  = do n     <- thNameToGhcName nm
       liftIO $ initTcForLookup env (lookupDataCon $ fromJust n)

data CoreEmbedder = CE {
    idType  :: Type
  , annType :: Type
  , effType :: Type
  , eVar    :: CoreExpr -> CoreExpr -> CoreExpr
  , eCon    :: CoreExpr -> [CoreExpr] -> CoreExpr -> CoreExpr
  , eField  :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
  , eLam    :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
  , eBind   :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
  , eVal    :: CoreExpr -> CoreExpr -> CoreExpr
  }

initEmbedCore :: HscEnv -> Module -> CoreM CoreEmbedder
initEmbedCore env mod
  = do idTy   <- tyFromName env ''Id
       effTy  <- tyFromName env ''EffExprBare
       annTy  <- tyFromName env ''Annot
       eVal   <- dcFromName env 'EVal
       eVar   <- dcFromName env 'EVar
       eCon   <- dcFromName env 'ECon
       eField <- dcFromName env 'EField
       eLam   <- dcFromName env 'ELam
       eBind  <- dcFromName env 'EBind
       let cstr c args = mkCoreConApps c ([Type idTy, Type annTy] ++ args)
       return CE { idType  = idTy
                 , effType = effTy
                 , annType = annTy
                 , eVal    = \p a    -> cstr eVal [p,a]
                 , eVar    = \e1 e2  -> cstr eVar [e1, e2]
                 , eCon    = \e es a -> cstr eCon (e : es ++ [a])
                 , eField  = \e i a  -> cstr eField [e,i,a]
                 , eLam    = \b e a  -> cstr eLam [b,e,a]
                 , eBind   = \f g a  -> cstr eBind [f,g,a]
                 }

embedCore :: CoreEmbedder -> HscEnv -> Module -> (Id, EffExprBare) -> CoreM CoreBind
embedCore ce env mod binds
  = bind <$> go binds
  where
    go (x,e) = embedCore' ce env mod e
    b        = tabName mod
    bind e   = NonRec (mkExportedLocalId VanillaId b (effType ce)) e

embedCore' :: CoreEmbedder -> HscEnv -> Module -> EffExprBare -> CoreM CoreExpr
embedCore' ce env mod = go
  where
    dflt = pure (mkCoreConApps unitDataCon [])
    go (EVal p _)
      = eVal ce <$> embedSubset ce p <*> dflt
    go (EVar x _)
      = eVar ce <$> mkStringExpr x <*> dflt
    go (ECon b xs _)
      = eCon ce <$> mkStringExpr b <*> mapM go xs <*> dflt
    go (EField e i _)
      = eField ce <$> go e
                  <*> pure (mkIntExprInt unsafeGlobalDynFlags i)
                  <*> dflt
    go (ELam b e a)
      = eLam ce <$> mkStringExpr b <*> go e <*> dflt
    go (EBind f g a)
      = eBind ce <$> go f <*> go g <*> dflt

embedSubset :: CoreEmbedder -> SubsetBare -> CoreM CoreExpr
embedSubset ce (x, t, p) = go p
  where
    go = undefined
