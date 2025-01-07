-- | Entry point for Hydra code generation utilities

module Hydra.Codegen (
  modulesToGraph,
  writeGraphql,
  writeHaskell,
  writeJava,
  writeJsonSchema,
  writePdl,
  writeProtobuf,
  writeScala,
  writeYaml,
  module Hydra.Sources.Tier4.All
) where

import Hydra.Kernel
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Ext.Graphql.Coder
import Hydra.Ext.Haskell.Coder
import Hydra.Ext.Java.Coder
import Hydra.Ext.Json.Coder
import Hydra.Ext.Json.Schema.Coder
import Hydra.Ext.Pegasus.Coder
import Hydra.Ext.Protobuf.Coder
import Hydra.Ext.Python.Coder
import Hydra.Ext.Scala.Coder
import Hydra.Ext.Yaml.Modules

import Hydra.Sources.Libraries
import Hydra.Sources.Tier4.All

import qualified Control.Monad as CM
import qualified System.FilePath as FP
import qualified Data.List as L
import qualified Data.Map as M
import qualified System.Directory as SD
import qualified Data.Maybe as Y


generateSources :: (Module -> Flow (Graph) (M.Map FilePath String)) -> FilePath -> [Module] -> IO ()
generateSources printModule basePath mods = do
    mfiles <- runFlow bootstrapGraph generateFiles
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

modulesToGraph :: [Module] -> Graph
modulesToGraph mods = elementsToGraph parent (Just schemaGraph) dataElements
  where
    parent = bootstrapGraph
    dataElements = L.concat (moduleElements <$> (L.concat (close <$> mods)))
    schemaElements = L.concat (moduleElements <$> (L.concat (close <$> (L.nub $ L.concat (moduleTypeDependencies <$> mods)))))
    schemaGraph = elementsToGraph bootstrapGraph Nothing schemaElements
    close mod = mod:(L.concat (close <$> moduleTermDependencies mod))

printTrace :: Bool -> Trace -> IO ()
printTrace isError t = do
  CM.unless (L.null $ traceMessages t) $ do
      putStrLn $ if isError then "Flow failed. Messages:" else "Messages:"
      putStrLn $ indentLines $ traceSummary t

runFlow :: s -> Flow s a -> IO (Maybe a)
runFlow cx f = do
    printTrace (Y.isNothing v) t
    return v
  where
    FlowState v _ t = unFlow f cx emptyTrace

writeGraphql :: FP.FilePath -> [Module] -> IO ()
writeGraphql = generateSources moduleToGraphql

writeHaskell :: FilePath -> [Module] -> IO ()
writeHaskell = generateSources moduleToHaskell

writeJava :: FP.FilePath -> [Module] -> IO ()
writeJava = generateSources moduleToJava

-- writeJson :: FP.FilePath -> [Module] -> IO ()
-- writeJson = generateSources Json.printModule

writeJsonSchema :: FP.FilePath -> [Module] -> IO ()
writeJsonSchema = generateSources (moduleToJsonSchemaFiles (JsonSchemaOptions True))

writePdl :: FP.FilePath -> [Module] -> IO ()
writePdl = generateSources moduleToPdl

writeProtobuf :: FP.FilePath -> [Module] -> IO ()
writeProtobuf = generateSources moduleToProtobuf

writePython :: FP.FilePath -> [Module] -> IO ()
writePython = generateSources moduleToPython

writeScala :: FP.FilePath -> [Module] -> IO ()
writeScala = generateSources moduleToScala

writeYaml :: FP.FilePath -> [Module] -> IO ()
writeYaml = generateSources moduleToYaml
