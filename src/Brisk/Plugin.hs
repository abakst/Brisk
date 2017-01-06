module Brisk.Plugin (plugin) where

import GhcPlugins
import System.FilePath.Find
import Paths_brisk
import Brisk.Model.Extract
import Brisk.Model.Spec

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
  = do hsenv <- getHscEnv
       liftIO $ do
         specs <- readSpecFiles
         runMGen bs hsenv mg specs (deShadowBinds binds)
       return binds

readSpecFiles :: IO [Spec]
readSpecFiles = do specs <- getSpecFiles
                   concat <$> mapM parseSpecFile specs
       
getSpecFiles :: IO [String]
getSpecFiles = find always (extension ==? ".espec") =<< getDataDir
