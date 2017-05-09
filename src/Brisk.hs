{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Data.Maybe
import Brisk.Model.Types
import Brisk.Pretty
-- import Brisk.Model.Prolog
import Brisk.Model.IceT
import Brisk.Model.Rewrite
import Text.Show.Pretty
import Options.Generic
import System.Exit

main :: IO ()
main = do Check f b q <- getRecord "Brisk"
          let binder   = fromMaybe "main" b
          runBrisk f binder q

data Brisk = Check { file   :: String
                   , binder :: Maybe String
                   , query  :: Maybe String
                   }
             deriving (Generic, Show)
instance ParseRecord Brisk

runBrisk :: String -> String -> Maybe String -> IO ()
runBrisk fn fun msave
  = runGhc (Just libdir) $ do
      hsc_env       <- getSession
      dflags        <- getSessionDynFlags
      let dflags'    = dflags { hscTarget      = HscInterpreted
                              , ghcLink        = LinkInMemory
                              , pluginModNames = [plugMod]
                              , packageFlags   = [distStatic]
                              , verbosity      = 1
                              }
          plugMod    = mkModuleName "Brisk.Plugin"
          distStatic = ExposePackage "distributed-static"
                                     (PackageArg "distributed-static")
                                     (ModRenaming True [])
      setSessionDynFlags dflags'
      setTargets [Target (TargetFile fn Nothing) False Nothing]
      liftIO $ putStrLn "Compiling..."
      load LoadAllTargets
      mod        <- topLevelModule hsc_env fn
      let impDecl = simpleImportDecl mod
          qualImp = impDecl { ideclQualified = True }
          modNm   = moduleNameString mod
      liftIO $ putStrLn "Loading..."
      setContext [ IIDecl qualImp ]
      hv         <- compileExpr (modNm `qualify` "brisk_tab__")
      v          <- liftIO $ lessUnsafeCoerce dflags "runBrisk" hv
      let st      = wordsToSpecTable v
          effm    = lookupTable (modNm `qualify` fun) st
      liftIO $ case effm of
                 Nothing  -> do
                   putStrLn $ "Unknown name: " ++ fun
                   exitFailure
                 -- Just eff -> runRewriter eff msave
                 Just eff -> let (_, ps) = runIceT eff
                                 res     = fromIceT ps
                             in putStrLn (render (pp res))

qualify :: String -> String -> String
qualify mn b = mn ++ "." ++ b

topLevelModule :: MonadIO m => HscEnv -> String -> m ModuleName
topLevelModule hsc_env fn
  = liftIO $ do
      (dflags'', hspp_fn) <- preprocess hsc_env (fn, Nothing)
      buf <- hGetStringBuffer hspp_fn
      (_,_,mod) <- getImports dflags'' buf fn hspp_fn
      return (unLoc mod)
