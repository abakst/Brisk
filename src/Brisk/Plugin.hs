module Brisk.Plugin (plugin) where

import GhcPlugins
import System.FilePath.Find
import Paths_brisk
import Brisk.Model.Extract
import Brisk.Model.Spec
import Control.Exception

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
import Brisk.Pretty
import Brisk.Model.GhcInterface

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
       bindsOnlyPass (runBrisk bs guts) guts

runBrisk :: [String] -> ModGuts -> CoreProgram -> CoreM CoreProgram   
runBrisk bs mg binds 
  = do hsenv <- GhcPlugins.getHscEnv
       liftIO . withExceptions $ do
         specs <- readSpecFiles hsenv mg
         runMGen bs hsenv mg specs (deShadowBinds binds)
       return binds
         where
           withExceptions act
             = catch act handleUserError
           handleUserError e@(ErrorCall _)
             = putStrLn (displayException e) 

readSpecFiles :: HscEnv -> ModGuts -> IO [Spec]
readSpecFiles env mg
  = do specs <- getSpecFiles
       concat <$> mapM (parseSpecFile env mg) specs
       
getSpecFiles :: IO [String]
getSpecFiles = find always (extension ==? ".espec") =<< getDataDir
