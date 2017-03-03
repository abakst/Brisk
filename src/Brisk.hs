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
import HscTypes
import ErrUtils
import Outputable

import DriverPipeline
import StringBuffer
import HeaderInfo

import Brisk.Model.Types
import Brisk.Model.Prolog
import Text.Show.Pretty

main :: IO ()
main = do [fn, fun] <- getArgs
          runBrisk fn fun

runBrisk :: String -> String -> IO ()
runBrisk fn fun
  = runGhc (Just libdir) $ do
      hsc_env <- getSession
      dflags  <- getSessionDynFlags
      let dflags' = dflags { hscTarget         = HscInterpreted
                           , ghcLink           = LinkInMemory
                           , pluginModNames    = [plugMod]
                           , verbosity         = 0
                           }
          plugMod = mkModuleName "Brisk.Plugin"
      setSessionDynFlags dflags'
      setTargets [Target (TargetFile fn Nothing) False Nothing]
      liftIO $ putStrLn "Compiling..."
      load LoadAllTargets
      mod <- topLevelModule hsc_env fn
      let impDecl = simpleImportDecl mod
          qualImp = impDecl { ideclQualified = True }
          modNm   = moduleNameString mod
      liftIO $ putStrLn "Loading..."
      setContext [ IIDecl qualImp ]
      hv     <- compileExpr (modNm `qualify` "brisk_tab__")
      v      <- liftIO $ lessUnsafeCoerce dflags "runBrisk" hv
      let st   = wordsToSpecTable v
          effm = lookupTable (modNm `qualify` fun) st
      liftIO $ case effm of
                 Nothing  ->
                   putStrLn $ ":("
                 Just eff -> do
                   liftIO $ putStrLn "Checking..."
                   runRewriter eff Nothing

qualify :: String -> String -> String
qualify mn b = mn ++ "." ++ b

topLevelModule :: MonadIO m => HscEnv -> String -> m ModuleName
topLevelModule hsc_env fn
  = liftIO $ do
      (dflags'', hspp_fn) <- preprocess hsc_env (fn, Nothing)
      buf <- hGetStringBuffer hspp_fn
      (_,_,mod) <- getImports dflags'' buf fn hspp_fn
      return (unLoc mod)
