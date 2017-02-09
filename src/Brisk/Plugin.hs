{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Brisk.Plugin (plugin) where

import Unique
import GHC.CString (unpackCString#)
import GhcPlugins hiding (Id)
import System.FilePath.Find
import Paths_brisk
import Brisk.Model.Extract
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
import Panic
import Brisk.Pretty
import Brisk.Model.GhcInterface
import Brisk.Model.EmbedCore
import Brisk.Model.Types
import Brisk.Annotations
import Control.Distributed.Process (expect)
import qualified Language.Haskell.TH as TH

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
  = do hsenv        <- GhcPlugins.getHscEnv
       dynflags     <- getDynFlags
       annEnv       <- loadBriskAnns hsenv mg
       let specMods = specModules mg annEnv
       let go (SpecTable entries) mod =

             do (SpecTable entries') <- retrieveSpecs hsenv mod
                return (SpecTable (entries ++ entries'))
       putMsgS (showSDoc dynflags (ppr specMods))
       specs0       <- retrieveAllSpecs hsenv mg
       let specTab0 = SpecTable (concat [ es | SpecTable es <- specs0 ])
       specs <- foldM go specTab0 specMods
       spec_tab <- liftIO . withExceptions $ do
         runMGen bs hsenv mg specs (deShadowBinds binds)
       case spec_tab of
         Just tab -> do
           --  This one implements "Assume" specs
           (tab', ns) <- fixupSpecNames mg tab annEnv
           --  Next, look in the exported names to see if
           --  we are exporting any spec modules, and if so
           --  merge the spec table in with ours

           --  We'll do this stupidly by *reloading* the table,
           --  but we should probably store the table when it
           --  it was first loaded...
           let names  = exportedNames mg ++ ns
               -- specModsOut = [ m | m <- specMods, getName m `elem` names ]
           -- error "need to re-export exported spec modules"
           tabbind@(NonRec tabid _) <- embedSpecTable (mg_module mg) names tab'
           return $ mg { mg_binds   = binds ++ [tabbind]
                       , mg_exports = mg_exports mg ++ [Avail $ getName tabid]
                       }
         _ -> return mg
         where
           withExceptions act
             = catch (act >>= return . return) handleUserError
           handleUserError e@(ErrorCall _)
             = throwGhcException (ProgramError (displayException e))

specModules :: ModGuts -> AnnEnv -> [Module]
specModules mg annEnv
  = [ mod | mod <- imports, isSpecMod annEnv mod ]
  where
    imports   = fst <$> (moduleEnvToList $ mg_dir_imps mg)

isSpecMod annEnv = not . null . lookupAnns annEnv ModuleTarget

fixupSpecNames :: ModGuts -> SpecTableOut -> AnnEnv -> CoreM (SpecTableOut, [Name])
fixupSpecNames mg (SpecTable specs) annEnv
  = do let exported = [(nameId n, n') | Avail n   <- mg_exports mg
                                      , Assume n' <- lookupAnns annEnv NamedTarget n
                                      ]
       exportedNames <- forM exported $ \(x,thn) ->
         do n <- thNameToGhcName thn
            return (x,n)
       specs' <- forM specs $ \(x :<=: t) -> do
         return $ case lookup x exportedNames of
                    Just (Just n) -> (nameId n :<=: t)
                    _             -> (x :<=: t)
       return (SpecTable specs', mapMaybe snd exportedNames)
        
lookupAnns :: AnnEnv -> (a -> CoreAnnTarget) -> a -> [BriskAnnotation]
lookupAnns annEnv t = findAnns deserializeWithData annEnv . t    

loadBriskAnns env mg
  = liftIO $ prepareAnnotations env (Just mg)

isModuleSpec :: ModGuts -> UniqFM [()] -> Bool       
isModuleSpec mg units
  = elemUFM uniq units
  where
    uniq = getUnique . moduleName $ mg_module mg
