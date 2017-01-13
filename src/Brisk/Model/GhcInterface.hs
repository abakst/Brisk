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

import Brisk.Pretty
import Text.PrettyPrint.HughesPJ as PP (text, (<>))

-- Looking up names
ghcVarName :: HscEnv -> String -> String -> IO Name  
ghcVarName env mod var
  = do let occNm = mkOccName OccName.varName var 
       m  <- liftIO $ lookupMod env (mkModuleName mod) 
       liftIO $ initTcForLookup env (lookupOrig m occNm)

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

resolve :: HscEnv -> [(String, String, a)] -> IO [(Name, a)]
resolve env binds
  = forM binds $ \(m, x, e) -> do
      n <- ghcVarName env m x
      return (n, e)

nameId :: Name -> String
nameId n = briskShowPpr $ concatFS [occFS, uniqFS] 
  where
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
