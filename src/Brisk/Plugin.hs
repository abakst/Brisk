module Brisk.Plugin (plugin) where

import GhcPlugins
import Brisk.Model.Extract

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
       liftIO $ runMGen bs hsenv mg (deShadowBinds binds)
       return binds
