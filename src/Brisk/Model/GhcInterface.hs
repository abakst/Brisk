{-# language DoAndIfThenElse #-}
module Brisk.Model.GhcInterface where

import GhcPlugins
import Avail
import Var
import Id  
import Unique
import OccName
import Name
import IfaceEnv
import IdInfo
import TcRnMonad
import Finder
import HscTypes
import Type
import Control.Monad
import HscMain
import TcRnDriver
import ConLike
import TcEnv

import Data.Char
import Data.Maybe
import Data.List

import Brisk.UX
import Brisk.Pretty
import Text.PrettyPrint.HughesPJ as PP (text, (<>))

-- Looking up names
ghcVarName :: HscEnv -> String -> String -> IO Name  
ghcVarName env mod var
  = do let occNm = mkOccName ns var 
       m  <- liftIO $ lookupMod env (mkModuleName mod) 
       liftIO $ initTcForLookup env $ do
         lookupOrig m occNm
         -- res <- tcLookup nm
         -- case res of
           -- AConLike (RealDataCon dc) -> return $ getName dc
           -- _                         -> return nm
  where
    ns | isUpper (var !! 0) = OccName.dataName
       | otherwise          = OccName.varName

ghcRawVarName :: HscEnv -> String -> IO Name
ghcRawVarName env nm
  = fromJust <$> ghcRawVarName_maybe env nm

ghcRawVarName_maybe :: HscEnv -> String -> IO (Maybe Name)
ghcRawVarName_maybe env nm
  = do rdrNm    <- hscParseIdentifier env nm
       (_, nms) <- tcRnLookupRdrName env rdrNm
       case nms of
         Just [name] -> do
           res <- initTcForLookup env (tcLookupGlobal name)
           case res of
             AConLike (RealDataCon dc) -> return $ Just (getName dc)
             _                         -> return $ Just name
         _           -> return Nothing

ghcFindName :: HscEnv -> ModGuts -> String -> IO (Maybe Name)
ghcFindName env mg str = do
       rdrNm <- hscParseIdentifier env str 
       let rdrEnv = mg_rdr_env mg
       mn <- case lookupGRE_RdrName (unLoc rdrNm) rdrEnv of
              [gre] -> return (Just (gre_name gre))
              _     -> return Nothing
       case mn of
         Just nm -> (Just . getName) <$> do
           initTcForLookup env (tcLookupGlobal nm)
         Nothing -> return Nothing

ghcFindTy :: HscEnv -> ModGuts -> String -> String -> IO TyCon
ghcFindTy env mg modstr str = do
  let occNm = mkTcOcc str
      modNm = mkModuleName modstr
  liftIO $ do mod <- lookupMod env modNm
              initTcForLookup env $ do
                nm <- lookupOrig mod occNm
                tcLookupTyCon nm

lookupName :: HscEnv -> Module -> String -> IO Name
lookupName env m x
  = liftIO $ initTcForLookup env (lookupOrig m n)
  where
    n = mkOccName OccName.varName x

ghcVar :: HscEnv -> String -> String -> IO Var
ghcVar env mod var
  = do let occNm = mkOccName OccName.varName var 
       m  <- lookupMod env (mkModuleName mod) 
       initTcForLookup env (lookupOrig m occNm >>= lookupId)

ghcDataCon :: HscEnv -> String -> String -> IO DataCon
ghcDataCon env mod var
  = do let occNm = mkOccName OccName.dataName var 
       m  <- lookupMod env (mkModuleName mod) 
       initTcForLookup env (lookupOrig m occNm >>= lookupDataCon)

ghcTyName :: HscEnv -> String -> String -> IO Name
ghcTyName env mod ty
  = do let occNm = mkOccName OccName.clsName ty
       m  <- lookupMod env (mkModuleName mod) 
       liftIO $ initTcForLookup env (lookupOrig m occNm)

lookupModMaybe :: HscEnv -> ModuleName -> IO (Maybe Module)
lookupModMaybe hsc_env mod_nm = do
    found_module <- findImportedModule hsc_env mod_nm Nothing
    case found_module of
      Found _ md -> return (Just md)
      _          -> return Nothing

lookupMod :: HscEnv -> ModuleName -> IO Module
lookupMod hsc_env mod_nm = do
  mm <- lookupModMaybe hsc_env mod_nm
  case mm of
      Just md -> return md
      _       -> error $ "Unable to resolve module looked up by plugin: " ++ moduleNameString mod_nm --      return t

-- Distinguishing types & special expressions                    
isRecordSel :: Var -> Bool
isRecordSel x
  = case idDetails x of
      RecSelId {} -> True
      _           -> False

builtinName :: Int -> Name
builtinName i
  = mkSystemName (mkUnique 'b' i) (mkVarOcc (show i))

-- mkTyVar :: String -> TyVar  
-- mkTyVar t = Var.mkTyVar nm anyKind
--   where
--     nm = mkSystemName (mkUnique 't' (sum (ord <$> t))) (mkTyVarOcc t)

resolve :: HscEnv -> [(String, String, a)] -> IO [(Name, a)]
resolve env binds
  = forM binds $ \(m, x, e) -> do
      n <- ghcVarName env m x
      return (n, e)

nameId :: Name -> String
nameId n = briskShowPpr $ concatFS [modFS, occFS, uniqFS] 
  where
    modFS = case nameModule_maybe n of
            Nothing -> fsLit ""
            Just m  -> concatFS [moduleNameFS (moduleName m), fsLit "."]
    occFS = occNameFS (getOccName n)
    uniqFS
       | isSystemName n
       = concatFS [fsLit "_",  fsLit (briskShowPpr (getUnique n))]
       | otherwise
       = fsLit ""

tyConId :: TyCon -> String    
tyConId tc
  | tc == listTyCon = "List"
  | isTupleTyCon tc = "Tuple"
  | otherwise       = nameId (getName tc)

instance Show Type where
  show = showSDoc unsafeGlobalDynFlags . ppr
  
instance Pretty Type where
  ppPrec z t = PP.text "@" PP.<> PP.text (show t)

briskShowPpr :: Outputable a => a -> String
briskShowPpr = showSDoc unsafeGlobalDynFlags . ppr

getImportedNames :: HscEnv -> ModGuts -> Module -> IO [Name]
getImportedNames env mg mod
  = do epsPIT <- liftIO $ eps_PIT <$> hscEPS env
       let enames = [ n | Avail _ n <- concat (mi_exports <$> lookupModuleEnv epsPIT mod)    ]
           inames = [ n | Avail _ n <- concat (mi_exports . hm_iface <$> lookupUFM hpt muniq) ]
           muniq  = modUnique mod
           hpt    = hsc_HPT env
       return (enames ++ inames)

exportedNames :: ModGuts -> [Name]        
exportedNames mg
  = [ n | Avail _ n <- mg_exports mg ]

whenExports :: MonadIO m => HscEnv -> ModGuts -> Module -> OccName -> m a -> m (Maybe a)       
whenExports env mg mod nm act
  = do nms <- (getOccName <$>) <$> liftIO (getImportedNames env mg mod)
       if nm `elem` nms then
         Just <$> act
       else
         return Nothing

usedModules :: ModGuts -> [ModuleName]
usedModules mg = nub nms
  where
    nms = [ mn | UsageHomeModule { usg_mod_name = mn } <- mg_usages mg ]
       ++ [ moduleName m | UsagePackageModule { usg_mod = m } <- mg_usages mg ]
-- usedModules = nub . mapMaybe nameModule_maybe . uniqSetToList . mg_used_names

modUnique :: Module -> Unique
modUnique = getUnique . moduleName 
