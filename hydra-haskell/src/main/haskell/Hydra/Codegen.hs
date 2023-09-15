-- | Entry point for Hydra code generation utilities

module Hydra.Codegen (
  modulesToGraph,
  writeGraphql,
  writeHaskell,
  writeJava,
  writePdl,
  writeProtobuf,
  writeScala,
  writeYaml,
  module Hydra.Sources.Tier4.All
) where

import Hydra.Kernel
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Langs.Graphql.Coder
import Hydra.Langs.Haskell.Coder
import Hydra.Langs.Java.Coder
import Hydra.Langs.Json.Coder
import Hydra.Langs.Pegasus.Coder
import Hydra.Langs.Protobuf.Coder
import Hydra.Langs.Scala.Coder
import Hydra.Langs.Yaml.Modules

import Hydra.Sources.Libraries
import Hydra.Sources.Tier4.All

import qualified Control.Monad as CM
import qualified System.FilePath as FP
import qualified Data.List as L
import qualified Data.Map as M
import qualified System.Directory as SD
import qualified Data.Maybe as Y


findType :: Graph Kv -> Term -> Flow (Graph Kv) (Maybe (Type Kv))
findType cx term = annotationClassTermType (graphAnnotations cx) term

generateSources :: (Module Kv -> Flow (Graph Kv) (M.Map FilePath String)) -> FilePath -> [Module Kv] -> IO ()
generateSources printModule basePath mods = do
    mfiles <- runFlow kernelSchema generateFiles
    case mfiles of
      Nothing -> fail "Transformation failed"
      Just files -> mapM_ writePair files
  where
    generateFiles = do
      withTrace "generate files" $ do
        withState (modulesToGraph mods) $ do
          g' <- inferGraphTypes
          withState g' $ do
              maps <- CM.mapM forModule $ refreshModule (graphElements g') <$> mods
              return $ L.concat (M.toList <$> maps)
            where
              refreshModule els mod = mod {
                moduleElements = Y.catMaybes ((\e -> M.lookup (elementName e) els) <$> moduleElements mod)}

    writePair (path, s) = do
      let fullPath = FP.combine basePath path
      SD.createDirectoryIfMissing True $ FP.takeDirectory fullPath
      writeFile fullPath s

    forModule mod = withTrace ("module " ++ unNamespace (moduleNamespace mod)) $ printModule mod

-- Note: currently a subset of the kernel which is used as a schema graph.
--       The other modules are not yet needed in the runtime environment
kernelSchema :: Graph Kv
kernelSchema = elementsToGraph bootstrapGraph Nothing $ L.concatMap moduleElements [
  hydraCodersModule,
  hydraComputeModule,
  hydraCoreModule,
  hydraGraphModule,
  hydraMantleModule,
  hydraModuleModule,
  hydraTestingModule]

modulesToGraph :: [Module Kv] -> Graph Kv
modulesToGraph mods = elementsToGraph kernelSchema (Just kernelSchema) elements
  where
    elements = L.concat (moduleElements <$> modules)
    modules = L.concat (close <$> mods)
      where
        close mod = mod:(L.concat (close <$> moduleDependencies mod))

printTrace :: Bool -> Trace -> IO ()
printTrace isError t = do
  CM.unless (L.null $ traceMessages t) $ do
      putStrLn $ if isError then "Flow failed. Messages:" else "Messages:"
      putStrLn $ indentLines $ traceSummary t

runFlow :: s -> Flow s a -> IO (Maybe a)
runFlow cx f = do
  let FlowState v _ t = unFlow f cx emptyTrace
  printTrace (Y.isNothing v) t
  return v

writeGraphql :: FP.FilePath -> [Module Kv] -> IO ()
writeGraphql = generateSources moduleToGraphql

writeHaskell :: FilePath -> [Module Kv] -> IO ()
writeHaskell = generateSources moduleToHaskell

writeJava :: FP.FilePath -> [Module Kv] -> IO ()
writeJava = generateSources moduleToJava

-- writeJson :: FP.FilePath -> [Module Kv] -> IO ()
-- writeJson = generateSources Json.printModule

writePdl :: FP.FilePath -> [Module Kv] -> IO ()
writePdl = generateSources moduleToPdl

writeProtobuf :: FP.FilePath -> [Module Kv] -> IO ()
writeProtobuf = generateSources moduleToProtobuf

writeScala :: FP.FilePath -> [Module Kv] -> IO ()
writeScala = generateSources moduleToScala

writeYaml :: FP.FilePath -> [Module Kv] -> IO ()
writeYaml = generateSources moduleToYaml
