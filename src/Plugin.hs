module Plugin (plugin) where

import GhcPlugins
import IfaceEnv
import Finder
import OccName
import TcEnv
import TcRnMonad

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
       let occNm = mkOccName OccName.dataName "ProcessDefinition"
           modNm = mkModuleName "Control.Distributed.Process.ManagedProcess"
       liftIO $ do
         found_module <- findImportedModule hsenv modNm Nothing
         case found_module of
           Found _ mod -> liftIO $ do
             putStrLn "doing lookup"
             initTcForLookup hsenv $ do
               nm  <- lookupOrig mod occNm
               liftIO $ putStrLn "found orig"
               tcLookup nm
             putStrLn "OK"
       return binds
