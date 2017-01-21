{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Brisk.Plugin (plugin) where

import Unique
import GhcPlugins
import System.FilePath.Find
import Paths_brisk
import Brisk.Model.Extract
import Brisk.Model.Spec
import Control.Exception
import Data.Maybe
import Data.List (nub)

import Control.Monad       

import ErrUtils
import HscMain
import HscTypes
import IfaceEnv
import Finder
import OccName
import TcEnv
import TcRnMonad
import TcRnDriver
import DynamicLoading
import Annotations
import Avail
import Brisk.Pretty
import Brisk.Model.GhcInterface
import Brisk.Model.EmbedCore
import Brisk.Model.Types
import Control.Distributed.Process (expect)

plugin = briskPlugin       

briskPlugin :: Plugin
briskPlugin = defaultPlugin {
  installCoreToDos = installBrisk
  }

installBrisk :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]  
installBrisk bs todo
  = do reinitializeGlobals
       return (CoreDoPluginPass "Brisk" (briskPass bs) : todo)

briskPass :: [String] -> ModGuts -> CoreM ModGuts       
briskPass bs guts
  = do dflags <- getDynFlags
       runBrisk bs guts (mg_binds guts)

runBrisk :: [String] -> ModGuts -> CoreProgram -> CoreM ModGuts 
runBrisk bs mg binds 
  = do hsenv <- GhcPlugins.getHscEnv
       epsPIT   <- liftIO $ eps_PIT <$> hscEPS hsenv
       -- Just nm' <- thNameToGhcName specTy
       -- Just ty  <- liftIO $ lookupTypeHscEnv hsenv nm'
       dynflags <- getDynFlags
       -- liftIO $ putStrLn (nameId nm')
       ce                <- initEmbedCore hsenv (mg_module mg)
       let mods     = nub $ mapMaybe nameModule_maybe (uniqSetToList (mg_used_names mg))
       forM_ mods $ \mod -> do
           let hpt  = hsc_HPT hsenv
               extinfo  = [ n | Avail n <- concat (mi_exports <$> lookupModuleEnv epsPIT mod) ]
               info = extinfo ++ [ n | Avail n <- concat (mi_exports . hm_iface <$> lookupUFM hpt (getUnique (moduleName mod))) ]
           let foo = (take 1 [ (mod, n) | n <- info, getOccName n == (getOccName $ tabName mod) ])
           unless (null foo) $ do 
             e <- retrieveSpecs hsenv mod ce
             liftIO $ putStrLn (show e)
       tab@(NonRec x _)  <- embedCore ce hsenv (mg_module mg) ("x", EVar "x" ())
       -- e@(NonRec x _) <- embedCore hsenv (mg_module mg) (EVar "x" ())
       putMsgS (showSDocDebug dynflags (ppr tab))
       liftIO . withExceptions $ do
         specs   <- readSpecFiles hsenv mg
         spectab <- runMGen bs hsenv mg specs (deShadowBinds binds)
         return $ mg { mg_binds = binds ++ [tab]
                     , mg_exports = mg_exports mg ++ [Avail $ getName x]
                     }
         where
           withExceptions act
             = catch act handleUserError
           handleUserError e@(ErrorCall _)
             = putStrLn (displayException e) >> return mg

readSpecFiles :: HscEnv -> ModGuts -> IO [Spec]
readSpecFiles env mg
  = do specs <- getSpecFiles
       concat <$> mapM (parseSpecFile env mg) specs
       
getSpecFiles :: IO [String]
getSpecFiles = find always (extension ==? ".espec") =<< getDataDir

specTy = ''SpecTable
