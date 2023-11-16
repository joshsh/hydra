-- | A utility for transforming OSV JSON to RDF. See https://osv.dev

module Hydra.Tools.OsvToRdf (
  executeOsvToRdfWorkflow,
  osvJsonDirectoryToNtriples,
) where

import Hydra.Kernel
import Hydra.Flows
import Hydra.Langs.Json.Serde
import Hydra.Langs.Json.Coder
import Hydra.CoreDecoding
import Hydra.Codegen
import Hydra.Tools.Formatting
import qualified Hydra.Json as Json
import qualified Hydra.Langs.Shacl.Coder as Shacl
import Hydra.Langs.Rdf.Serde
import Hydra.Workflow
import qualified Hydra.Langs.Rdf.Utils as RdfUt

import Hydra.Models.Osv
import qualified Dev.Osv.Schema as Osv

import System.IO
import System.FilePath
import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import System.FilePath.Posix
import System.Directory


emptyInstanceContext :: Graph -> Graph
emptyInstanceContext scx = elementsToGraph scx (Just scx) []

-- | A convenience for osvJsonDirectoryToNtriples, bundling all of the input parameters together as a workflow
executeOsvToRdfWorkflow :: TransformWorkflow -> IO ()
executeOsvToRdfWorkflow (TransformWorkflow name schemaSpec srcDir destDir) = do
    case schemaSpec of
      SchemaSpecProvided -> pure ()
      _ -> fail "unsupported schema spec"
    putStrLn $ "Executing workflow " ++ show name ++ ":"
    osvJsonDirectoryToNtriples srcDir destDir

-- Replace all lists with sets, for better query performance.
-- This is a last-mile step which breaks type/term conformance
-- (a more robust solution would modify the target language in the SHACL coder, so that list types are also transformed to set types).
listsToSets :: Term -> Term
listsToSets = rewriteTerm mapExpr
  where
    mapExpr recurse = recurse . replaceLists
    replaceLists term = case term of
      TermList els -> TermSet $ S.fromList els
      _ -> term

-- | Given a source directory full of OSV JSON files, and a destination directory,
--   transform the content of each file to a corresponding RDF (N-Triples) file in the destination directory.
osvJsonDirectoryToNtriples :: FilePath -> FilePath -> IO ()
osvJsonDirectoryToNtriples srcDir destDir = do
    entryType <- fromFlowIo osvContext (requireType Osv._Entry)
    coder <- fromFlowIo osvInstanceContext $ jsonCoder entryType
    paths <- getDirectoryContents srcDir
    conf <- CM.mapM (transformFile coder) paths
    let count = L.length $ L.filter id conf
    putStrLn $ "Transformed " ++ show count ++ " JSON files to N-triples"
  where
    transformFile coder srcFile = do
      if takeExtension srcFile /= ".json"
        then return False
        else do
          let destFile = replaceExtension srcFile "nt"
          osvJsonToNtriples coder (combine srcDir srcFile) (combine destDir destFile)
          return True

osvContext = modulesToGraph [osvSchemaModule]

osvInstanceContext = emptyInstanceContext osvContext

osvJsonToNtriples :: Coder Graph Graph (Term) Json.Value -> FilePath -> FilePath -> IO ()
osvJsonToNtriples coder inFile outFile = do
    contents <- readFile inFile
    case stringToJsonValue contents of
      Left msg -> fail $ "Failed to read JSON value in file " ++ inFile ++ ": " ++ msg
      Right v -> do
        let v' = rewriteJsonFieldCase v
        term0 <- fromFlowIo osvInstanceContext $ coderDecode coder v'
        let term1 = listsToSets term0
        node <- fromFlowIo osvInstanceContext $ RdfUt.nextBlankNode
        graph <- fromFlowIo osvInstanceContext $ (RdfUt.descriptionsToGraph <$> Shacl.encodeTerm node term1)
        let graphStr = rdfGraphToNtriples graph
        writeFile outFile graphStr

rewriteJsonFieldCase :: Json.Value -> Json.Value
rewriteJsonFieldCase v = case v of
  Json.ValueArray values -> Json.ValueArray (rewriteJsonFieldCase <$> values)
  Json.ValueObject m -> Json.ValueObject $ M.fromList (rewriteEntry <$> M.toList m)
    where
      rewriteEntry (k, v) = (rewriteKey k, rewriteJsonFieldCase v)
      rewriteKey = convertCase CaseConventionLowerSnake CaseConventionCamel
  _ -> v
