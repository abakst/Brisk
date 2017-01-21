module Brisk.Model.GhcInterface where

import GhcPlugins
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
  = do rdrNm    <- hscParseIdentifier env nm
       (_, nms) <- tcRnLookupRdrName env rdrNm
       case nms of
         Just [name] -> do
           res <- initTcForLookup env (tcLookupGlobal name)
           case res of
             AConLike (RealDataCon dc) -> return $ getName dc
             _                         -> return name
         _           -> error ("Unable to resolve: " ++ nm)

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

lookupMod :: HscEnv -> ModuleName -> IO Module
lookupMod hsc_env mod_nm = do
    found_module <- findImportedModule hsc_env mod_nm Nothing
    case found_module of
      Found _ md -> return md
      _          -> error $ "Unable to resolve module looked up by plugin: " ++ moduleNameString mod_nm --      return t

-- Distinguishing types & special expressions                    
isRecordSel :: Var -> Bool
isRecordSel x
  = case idDetails x of
      RecSelId {} -> True
      _           -> False

builtinName :: Int -> Name
builtinName i
  = mkSystemName (mkUnique 'b' i) (mkVarOcc (show i))

mkTyVar :: String -> TyVar  
mkTyVar t = Var.mkTyVar nm anyKind
  where
    nm = mkSystemName (mkUnique 't' (sum (ord <$> t))) (mkTyVarOcc t)

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

instance Show Type where
  show = showSDoc unsafeGlobalDynFlags . ppr
  
instance Pretty Type where
  ppPrec z t = PP.text "@" PP.<> PP.text (show t)

briskShowPpr :: Outputable a => a -> String
briskShowPpr = showSDoc unsafeGlobalDynFlags . ppr
