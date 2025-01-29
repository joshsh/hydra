-- | A utility for transforming Avro-compliant JSON into other models

module Hydra.Tools.AvroWorkflows (
  TransformWorkflow(..),
  JsonPayloadFormat(..),
  TermEncoder(..),
  LastMile(..),
  defaultTinkerpopAnnotations,
  exampleGraphsonContext,
  examplePgSchema,
  executeAvroTransformWorkflow,
  propertyGraphGraphsonLastMile,
  propertyGraphJsonLastMile,
  rdfDescriptionsToNtriples,
  shaclRdfLastMile,
  typedTermToShaclRdf,
  transformAvroJsonDirectory,
) where

import Hydra.Kernel
import Hydra.Flows
import Hydra.Dsl.Annotations
import qualified Hydra.Ext.Org.Apache.Avro.Schema as Avro
import qualified Hydra.Json as Json
import Hydra.Ext.Json.Coder
import Hydra.Ext.Json.Eliminate
import Hydra.Ext.Json.Serde
import Hydra.Ext.Avro.Coder
import Hydra.Ext.Avro.SchemaJson
import Hydra.Ext.Pg.Coder
import qualified Hydra.Ext.Shacl.Coder as Shacl
import qualified Hydra.Ext.Org.W3.Rdf.Syntax as Rdf
import qualified Hydra.Ext.Rdf.Utils as RdfUt
import qualified Hydra.Pg.Model as PG
import qualified Hydra.Pg.Mapping as PGM
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import qualified Hydra.Dsl.Expect as Expect
import Hydra.Ext.Rdf.Serde
import Hydra.Sources.Core
import Hydra.Ext.Pg.Graphson.Coder
import Hydra.Pg.Graphson.Syntax as G

import qualified Control.Monad as CM
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import System.IO
import System.FilePath
import System.FilePath.Posix
import System.Directory


data JsonPayloadFormat = Json | Jsonl

type TermEncoder x = Term -> Graph -> Flow Graph [x]

defaultTinkerpopAnnotations :: PGM.AnnotationSchema
defaultTinkerpopAnnotations = PGM.AnnotationSchema {
  PGM.annotationSchemaVertexLabel = "vertexLabel",
  PGM.annotationSchemaEdgeLabel = "edgeLabel",
  PGM.annotationSchemaVertexId = "vertexId",
  PGM.annotationSchemaEdgeId = "edgeId",
  PGM.annotationSchemaPropertyKey = "key",
  PGM.annotationSchemaPropertyValue = "value",
  PGM.annotationSchemaOutVertex = "outVertex",
  PGM.annotationSchemaOutVertexLabel = "outVertexLabel",
  PGM.annotationSchemaInVertex = "inVertex",
  PGM.annotationSchemaInVertexLabel = "inVertexLabel",
  PGM.annotationSchemaOutEdge = "outEdge",
  PGM.annotationSchemaOutEdgeLabel = "outEdgeLabel",
  PGM.annotationSchemaInEdge = "inEdge",
  PGM.annotationSchemaInEdgeLabel = "inEdgeLabel",
  PGM.annotationSchemaIgnore = "ignore"}

examplePgSchema :: PGM.Schema s () String
examplePgSchema = PGM.Schema {
    PGM.schemaVertexIdTypes = mkCoder "encode vertex id type" encodeType decodeType,
    PGM.schemaVertexIds = mkCoder "encode vertex id" Expect.string (pure . Terms.string),
    PGM.schemaEdgeIdTypes = mkCoder "encode edge id type" encodeType decodeType,
    PGM.schemaEdgeIds = mkCoder "encode edge id" Expect.string (pure . Terms.string),
    PGM.schemaPropertyTypes = mkCoder "encode property type" encodeType decodeType,
    PGM.schemaPropertyValues = mkCoder "encode property value" Expect.string (pure . Terms.string),
    PGM.schemaAnnotations = defaultTinkerpopAnnotations,
    PGM.schemaDefaultVertexId = "defaultVertexId",
    PGM.schemaDefaultEdgeId = "defaultEdgeId"}
  where
    mkCoder lab encode decode = Coder (withTrace lab . encode) decode
    encodeType _ = pure ()
    decodeType _ = pure Types.unit

-- | A convenience for transformAvroJsonDirectory, bundling all of the input parameters together as a workflow
executeAvroTransformWorkflow :: LastMile Graph x -> TransformWorkflow -> IO ()
executeAvroTransformWorkflow lastMile (TransformWorkflow name schemaSpec srcDir destDir) = do
    schemaPath <- case schemaSpec of
      SchemaSpecFile p -> pure p
      _ -> fail "unsupported schema spec"
    putStrLn $ "Executing workflow " ++ show name ++ ":"
    transformAvroJsonDirectory lastMile schemaPath srcDir destDir

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

pgElementToJson :: PGM.Schema Graph t v -> PG.Element v -> Flow Graph Json.Value
pgElementToJson schema el = case el of
    PG.ElementVertex vertex -> do
      let labelJson = Json.ValueString $ PG.unVertexLabel $ PG.vertexLabel vertex
      idJson <- coderDecode (PGM.schemaVertexIds schema) (PG.vertexId vertex) >>= untypedTermToJson
      propsJson <- propsToJson $ PG.vertexProperties vertex
      return $ Json.ValueObject $ M.fromList $ Y.catMaybes [
        Just ("label", labelJson),
        Just ("id", idJson),
        propsJson]
    PG.ElementEdge edge -> do
      let labelJson = Json.ValueString $ PG.unEdgeLabel $ PG.edgeLabel edge
      idJson <- coderDecode (PGM.schemaEdgeIds schema) (PG.edgeId edge) >>= untypedTermToJson
      outJson <- coderDecode (PGM.schemaVertexIds schema) (PG.edgeOut edge) >>= untypedTermToJson
      inJson <- coderDecode (PGM.schemaVertexIds schema) (PG.edgeIn edge) >>= untypedTermToJson
      propsJson <- propsToJson $ PG.edgeProperties edge
      return $ Json.ValueObject $ M.fromList $ Y.catMaybes [
        Just ("label", labelJson),
        Just ("id", idJson),
        Just ("out", outJson),
        Just ("in", inJson),
        propsJson]
  where
    propsToJson pairs = if L.null pairs
        then pure Nothing
        else do
          p <- CM.mapM propToJson $ M.toList pairs
          return $ Just $ ("properties", Json.ValueObject $ M.fromList p)
      where
        propToJson (PG.PropertyKey key, v) = do
          json <- coderDecode (PGM.schemaPropertyValues schema) v >>= untypedTermToJson
          return (key, json)

pgElementsToJson :: PGM.Schema Graph t v -> [PG.Element v] -> Flow Graph Json.Value
pgElementsToJson schema els = Json.ValueArray <$> CM.mapM (pgElementToJson schema) els

pgElementsToPgVerticesWithAdjacentEdges :: Ord v => [PG.Element v] -> [PG.VertexWithAdjacentEdges v]
pgElementsToPgVerticesWithAdjacentEdges els = M.elems vertexMap1
  where
    vertices = E.lefts eithers
    edges = E.rights eithers
    eithers = fmap toEither els
      where
        toEither el = case el of
          PG.ElementVertex v -> Left v
          PG.ElementEdge e -> Right e
    vertexMap0 = M.fromList $ fmap toPair vertices
      where
        toPair v = (PG.vertexId v, PG.VertexWithAdjacentEdges v [] [])
    vertexMap1 = L.foldl addEdges vertexMap0 edges
      where
        addEdges vertexMap (PG.Edge label id outV inV props) = addEdge True $ addEdge False vertexMap
          where
            addEdge out vertexMap = case M.lookup focusV vertexMap of
                Nothing -> vertexMap -- Disconnected edges are ignored
                Just v -> M.insert focusV (appendE v) vertexMap
              where
                focusV = if out then outV else inV
                otherV = if out then inV else outV
                adjEdge = PG.AdjacentEdge label id otherV props
                appendE v = if out
                  then v {PG.vertexWithAdjacentEdgesOuts = (adjEdge:(PG.vertexWithAdjacentEdgesOuts v))}
                  else v {PG.vertexWithAdjacentEdgesIns = (adjEdge:(PG.vertexWithAdjacentEdgesIns v))}

pgElementsToGraphson :: (Ord v, Show v) => GraphsonContext s v -> [PG.Element v] -> Flow s [Json.Value]
pgElementsToGraphson ctx els = CM.mapM encode vertices
  where
    vertices = pgElementsToPgVerticesWithAdjacentEdges els
    encode = coderEncode (vertexToJsonCoder ctx)

propertyGraphGraphsonLastMile :: (Ord v, Show t, Show v) => GraphsonContext Graph v -> PGM.Schema Graph t v -> t -> t -> LastMile Graph (PG.Element v)
propertyGraphGraphsonLastMile ctx schema vidType eidType =
  LastMile (\typ -> typedTermToPropertyGraph schema typ vidType eidType) (\els -> jsonValuesToString <$> pgElementsToGraphson ctx els) "jsonl"

exampleGraphsonContext :: GraphsonContext s String
exampleGraphsonContext = GraphsonContext $ Coder encodeValue decodeValue
  where
    encodeValue s = pure $ G.ValueString s
    decodeValue _ = fail "decoding from GraphSON is not yet supported"

propertyGraphJsonLastMile :: (Show t, Show v) => PGM.Schema Graph t v -> t -> t -> LastMile Graph (PG.Element v)
propertyGraphJsonLastMile schema vidType eidType =
  LastMile (\typ -> typedTermToPropertyGraph schema typ vidType eidType) (\els -> jsonValueToString <$> pgElementsToJson schema els) "json"

rdfDescriptionsToNtriples :: [Rdf.Description] -> String
rdfDescriptionsToNtriples = rdfGraphToNtriples . RdfUt.descriptionsToGraph

shaclRdfLastMile :: LastMile Graph Rdf.Description
shaclRdfLastMile = LastMile typedTermToShaclRdf (pure . rdfDescriptionsToNtriples) "nt"

typedTermToPropertyGraph :: (Show t, Show v) => PGM.Schema Graph t v -> Type -> t -> t -> Flow Graph (Term -> Graph -> Flow Graph [PG.Element v])
typedTermToPropertyGraph schema typ vidType eidType = do
    adapter <- elementCoder Nothing schema typ vidType eidType
    return $ \term graph -> flattenTree <$> coderEncode (adapterCoder adapter) term
  where
    flattenTree tree = (PG.elementTreeSelf tree):(L.concat $ (flattenTree <$> PG.elementTreeDependencies tree))

typedTermToShaclRdf :: Type -> Flow Graph (Term -> Graph -> Flow Graph [Rdf.Description])
typedTermToShaclRdf _ = pure encode
  where
    encode term graph = do
        elDescs <- CM.mapM encodeElement $ M.elems $ graphElements graph
        termDescs <- encodeBlankTerm
        return $ L.concat (termDescs:elDescs)
      where
        encodeElement el = do
          let subject = Rdf.ResourceIri $ RdfUt.nameToIri $ elementName el
          Shacl.encodeTerm subject $ listsToSets $ elementData el
        encodeBlankTerm = if notInGraph
          then do
            subject <- RdfUt.nextBlankNode
            Shacl.encodeTerm subject $ listsToSets term
          else pure []
        notInGraph = L.null $ L.filter (\e -> elementData e == term) $ M.elems $ graphElements graph

transformAvroJson :: JsonPayloadFormat -> AvroHydraAdapter -> LastMile Graph x -> FilePath -> FilePath -> IO ()
transformAvroJson format adapter lastMile inFile outFile = do
    putStr $ "\t" ++ inFile ++ " --> "
    contents <- readFile inFile
    let entities = case format of
          Json -> [contents]
          Jsonl -> L.filter (not . L.null) $ lines contents
    lmEncoder <- fromFlowIo hydraCore $ lastMileEncoder lastMile (adapterTarget adapter)
    descs <- L.concat <$> fromFlowIo hydraCore (CM.zipWithM (jsonToTarget inFile adapter lmEncoder) [1..] entities)
    result <- fromFlowIo hydraCore $ lastMileSerializer lastMile descs
    writeFile outFile result
    putStrLn $ outFile ++ " (" ++ descEntities entities ++ ")"
  where
    descEntities entities = if L.length entities == 1 then "1 entity" else show (L.length entities) ++ " entities"

    jsonToTarget inFile adapter lmEncoder index payload = case stringToJsonValue payload of
        Left msg -> fail $ "Failed to read JSON payload #" ++ show index ++ " in file " ++ inFile ++ ": " ++ msg
        Right json -> withState emptyAvroEnvironment $ do
          -- TODO; the core graph is neither the data nor the schema graph
          let dataGraph = hydraCore
          let schemaGraph = Just hydraCore

          term <- coderEncode (adapterCoder adapter) json
          env <- getState
          let graph = elementsToGraph dataGraph schemaGraph (M.elems $ avroEnvironmentElements env)
          withState hydraCore $ lmEncoder term graph

-- | Given a payload format (one JSON object per file, or one per line),
--   a path to an Avro *.avsc schema, a path to a source directory containing JSON files conforming to the schema,
--   and a path to a destination directory, map each input file to a corresponding output file in the
--   destination directory. This transformation is sensitive to Hydra-specific annotations (primaryKey/foreignKey)
--   in the Avro schema, which tell Hydra which objects to treat as elements and which fields are references to elements.
transformAvroJsonDirectory :: LastMile Graph x -> FilePath -> FilePath -> FilePath -> IO ()
transformAvroJsonDirectory lastMile schemaPath srcDir destDir = do
    createDirectoryIfMissing True destDir
    schemaStr <- readFile schemaPath
    adapter <- fromFlowIo () $ loadAdapter schemaStr
    paths <- getDirectoryContents srcDir
    conf <- CM.mapM (transformFile adapter) paths
    return ()
  where
    loadAdapter schemaStr = do
      avroSchema <- coderDecode avroSchemaStringCoder schemaStr
      withState emptyAvroEnvironment $ avroHydraAdapter avroSchema

    transformFile adapter srcFile = do
      case jsonPayloadFormat srcFile of
        Nothing -> return False
        Just format -> do
          let destFile = replaceExtension srcFile (lastMileFileExtension lastMile)
          transformAvroJson format adapter lastMile (combine srcDir srcFile) (combine destDir destFile)
          return True

    jsonPayloadFormat fileName = if ext == ".json"
        then Just Json
        else if ext == ".jsonl"
        then Just Jsonl
        else Nothing
      where
        ext = takeExtension fileName
