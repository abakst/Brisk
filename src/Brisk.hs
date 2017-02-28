module Main where

import GHC
import DynamicLoading
import Debugger
import RtClosureInspect
import GHC.Paths ( libdir )
import System.Environment
import DynFlags
import Exception
import MonadUtils
import StaticFlags

import Brisk.Model.Types
import Brisk.Model.Prolog

main :: IO ()
main = do [fn, mn, fun] <- getArgs
          runBrisk fn mn fun

runBrisk :: String -> String -> String -> IO ()
runBrisk fn mn fun
  = runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      let dflags' = dflags { hscTarget = HscInterpreted
                           , ghcLink   = LinkInMemory
                           , pluginModNames = [ mkModuleName "Brisk.Plugin" ]
                           , verbosity = 1
                           }
      setSessionDynFlags dflags'
      setTargets [Target (TargetFile fn Nothing) False Nothing]
      load LoadAllTargets
      let impDecl = simpleImportDecl (mkModuleName mn)
          qualImp = impDecl { ideclQualified = True }
      setContext [ IIDecl qualImp ]
      hv     <- compileExpr (mn ++ ".brisk_tab__")
      v      <- liftIO $ lessUnsafeCoerce dflags "runBrisk" hv
      let st   = wordsToSpecTable v
          effm = lookupTable fun st
      case effm of
        Just eff -> liftIO . putStrLn . toBriskString $ eff
        Nothing ->  liftIO . putStrLn $ ":("
