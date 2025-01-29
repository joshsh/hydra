module Hydra.Ext.Pg.Coder (
  elementCoder,
) where

import Hydra.Kernel
import Hydra.Pg.Mapping
import Hydra.Ext.Pg.TermsToElements
import qualified Hydra.Pg.Model as PG
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y


type ElementAdapter s t v = Adapter s s Type (PG.ElementTypeTree t) Term (PG.ElementTree v)

type PropertyAdapter s t v = Adapter s s (FieldType) (PG.PropertyType t) Field (PG.Property v)

type IdAdapter s t v = (Name, Adapter s s Type t Term v)

type IncidentElementAdapter s t v = (Name, ElementAdapter s t v)

data AdjacentEdgeAdapter s a t v = AdjacentEdgeAdapter {
  adjacentEdgeAdapterDirection :: PG.Direction,
  adjacentEdgeAdapterField :: FieldType,
  adjacentEdgeAdapterLabel :: PG.EdgeLabel,
  adjacentEdgeAdapterAdapter :: ElementAdapter s t v}

data ProjectionSpec a = ProjectionSpec {
  projectionSpecField :: FieldType,
  projectionSpecValues :: ValueSpec,
  projectionSpecAlias :: Maybe String}

vertexLabelKey = Name . annotationSchemaVertexLabel . schemaAnnotations
edgeLabelKey = Name . annotationSchemaEdgeLabel . schemaAnnotations
vertexIdKey = Name . annotationSchemaVertexId . schemaAnnotations
edgeIdKey = Name . annotationSchemaEdgeId . schemaAnnotations
propertyKeyKey = Name . annotationSchemaPropertyKey . schemaAnnotations
propertyValueKey = Name . annotationSchemaPropertyValue . schemaAnnotations
outVertexKey = Name . annotationSchemaOutVertex . schemaAnnotations
outVertexLabelKey = Name . annotationSchemaOutVertexLabel . schemaAnnotations
inVertexKey = Name . annotationSchemaInVertex . schemaAnnotations
inVertexLabelKey = Name . annotationSchemaInVertexLabel . schemaAnnotations
outEdgeLabelKey = Name . annotationSchemaOutEdgeLabel . schemaAnnotations
inEdgeLabelKey = Name . annotationSchemaInEdgeLabel . schemaAnnotations
ignoreKey = Name . annotationSchemaIgnore . schemaAnnotations

check :: Bool -> Flow s () -> Flow s ()
check b err = if b then pure () else err

checkRecordName expected actual = check (actual == expected) $
  unexpected ("record of type " ++ unName expected) ("record of type " ++ unName actual)

constructEdgeCoder :: (Show t, Show v)
                   => PG.VertexLabel -> Schema s t v -> Type -> t -> t -> PG.Direction -> Name -> [FieldType]
                   -> [PropertyAdapter s t v] -> Y.Maybe (ProjectionSpec v) -> Y.Maybe (ProjectionSpec v)
                   -> Flow s (ElementAdapter s t v)
constructEdgeCoder parentLabel schema source vidType eidType dir name fields propAdapters mOutSpec mInSpec = do
  label <- PG.EdgeLabel <$> findLabelString source name (edgeLabelKey schema)
  idAdapter <- edgeIdAdapter schema eidType name (edgeIdKey schema) fields

  outIdAdapter <- traverse (\s -> projectionAdapter vidType (schemaVertexIds schema) s "out") mOutSpec
  inIdAdapter <- traverse (\s -> projectionAdapter vidType (schemaVertexIds schema) s "in") mInSpec

  outVertexAdapter <- traverse (findIncidentVertexAdapter schema vidType eidType) mOutSpec
  inVertexAdapter <- traverse (findIncidentVertexAdapter schema vidType eidType) mInSpec
  let vertexAdapters = Y.catMaybes [outVertexAdapter, inVertexAdapter]

  outLabel <- case mOutSpec of
    Nothing -> pure parentLabel
    Just spec -> Y.maybe (fail "no out-vertex label") (pure . PG.VertexLabel) $ projectionSpecAlias spec
  inLabel <- case mInSpec of
    Nothing -> pure parentLabel
    Just spec -> Y.maybe (fail "no in-vertex label") (pure . PG.VertexLabel) $ projectionSpecAlias spec
  return $ edgeCoder dir schema source eidType name label outLabel inLabel idAdapter outIdAdapter inIdAdapter propAdapters vertexAdapters

constructVertexCoder :: (Show t, Show v)
                     => Schema s t v -> Type -> t -> t -> Name -> [FieldType] -> [PropertyAdapter s t v]
                     -> Flow s (ElementAdapter s t v)
constructVertexCoder schema source vidType eidType name fields propAdapters = do
  label <- PG.VertexLabel <$> findLabelString source name (vertexLabelKey schema)
  idAdapter <- vertexIdAdapter schema vidType name (vertexIdKey schema) fields
  outEdgeAdapters <- findAdjacenEdgeAdapters schema vidType eidType label PG.DirectionOut fields
  inEdgeAdapters <- findAdjacenEdgeAdapters schema vidType eidType label PG.DirectionIn fields
  return $ vertexCoder schema source vidType name label idAdapter propAdapters (outEdgeAdapters ++ inEdgeAdapters)

edgeCoder
  :: PG.Direction
  -> Schema s t v
  -> Type
  -> t
  -> Name
  -> PG.EdgeLabel -> PG.VertexLabel -> PG.VertexLabel
  -> Maybe (IdAdapter s t v) -> Maybe (IdAdapter s t v) -> Maybe (IdAdapter s t v) -> [PropertyAdapter s t v]
  -> [IncidentElementAdapter s t v]
  -> ElementAdapter s t v
edgeCoder dir schema source eidType tname label outLabel inLabel mIdAdapter outAdapter inAdapter propAdapters vertexAdapters
    = Adapter lossy source (elementTypeTreeEdge et []) coder
  where
    et = PG.EdgeType label eidType outLabel inLabel $ propertyTypes propAdapters
    coder = Coder encode decode
      where
        encode term = case stripTerm term of
          TermOptional (Just ot) -> encode ot
          TermRecord (Record tname' fields) -> do
              checkRecordName tname tname'
              let fieldsm = fieldMap fields
              id <- case mIdAdapter of
                Nothing -> pure $ schemaDefaultEdgeId schema
                Just ad -> selectEdgeId fieldsm ad
              props <- encodeProperties fieldsm propAdapters
              outId <- getVertexId PG.DirectionOut fieldsm outAdapter
              inId <- getVertexId PG.DirectionIn fieldsm inAdapter

              deps <- Y.catMaybes <$> CM.mapM (findDependency fieldsm) vertexAdapters

              return $ elementTreeEdge (PG.Edge label id outId inId props) deps
            where
              findDependency fieldsm (fname, ad) = case M.lookup fname fieldsm of
                  Nothing -> pure Nothing
                  Just fterm -> Just <$> (coderEncode (adapterCoder ad) fterm)
          _ -> unexpected "record (1)" $ show term
        decode el = noDecoding "edge"
        getVertexId dir1 fieldsm adapter = if dir1 == dir
          then pure $ schemaDefaultVertexId schema
          else case adapter of
            Nothing -> fail $ "no adapter for " ++ show dir1 ++ " with " ++ show dir
            Just ad -> selectVertexId fieldsm ad

edgeIdAdapter :: Schema s t v -> t -> Name -> Name -> [FieldType] -> Flow s (Y.Maybe (IdAdapter s t v))
edgeIdAdapter schema eidType name idKey fields = do
  mIdSpec <- findIdProjectionSpec False name idKey fields
  case mIdSpec of
    Nothing -> pure Nothing
    Just idSpec -> Just <$> projectionAdapter eidType (schemaEdgeIds schema) idSpec "id"

-- | Constructs an element adapter for a given type, interpreting it either as a vertex specification or an edge specification
--   The adapter maps terms of the given type to property graph element trees (rooted at a vertex or an edge)
elementCoder :: (Show t, Show v)
  => Y.Maybe (PG.Direction, PG.VertexLabel) -- For edge specs, their direction and parent vertex label
  -> Schema s t v
  -> Type
  -> t -> t
  -> Flow s (ElementAdapter s t v)
elementCoder mparent schema source vidType eidType = case stripType source of
    TypeOptional ot -> elementCoder mparent schema ot vidType eidType

    TypeRecord (RowType name fields) -> withTrace ("adapter for " ++ unName name) $ do

      -- Construct out- and in-vertex specs (only in edge specs)
      mOutSpec <- findProjectionSpec name (outVertexKey schema) (outVertexLabelKey schema) fields
      mInSpec <- findProjectionSpec name (inVertexKey schema) (inVertexLabelKey schema) fields

      -- Decide whether this is a vertex spec or edge spec
      let kind = if hasVertexAdapters dir mOutSpec mInSpec then PG.ElementKindEdge else PG.ElementKindVertex

      -- Construct property adapters
      propAdapters <- findPropertySpecs schema kind fields >>= CM.mapM (propertyAdapter schema)

      -- Construct either a vertex adapter or an edge adapter
      case kind of
        PG.ElementKindVertex -> constructVertexCoder schema source vidType eidType name fields propAdapters
        PG.ElementKindEdge -> constructEdgeCoder parentLabel schema source vidType eidType dir name fields propAdapters mOutSpec mInSpec

    _ -> unexpected "record type" $ show source
  where
    dir = Y.maybe PG.DirectionBoth fst mparent
    parentLabel = Y.maybe (PG.VertexLabel "NOLABEL") snd mparent

elementTreeEdge :: PG.Edge v -> [PG.ElementTree v] -> PG.ElementTree v
elementTreeEdge edge = PG.ElementTree (PG.ElementEdge edge)

elementTreeVertex :: PG.Vertex v -> [PG.ElementTree v] -> PG.ElementTree v
elementTreeVertex vertex = PG.ElementTree (PG.ElementVertex vertex)

elementTypeTreeEdge :: PG.EdgeType t -> [PG.ElementTypeTree t] -> PG.ElementTypeTree t
elementTypeTreeEdge etype = PG.ElementTypeTree (PG.ElementTypeEdge etype)

elementTypeTreeVertex :: PG.VertexType t -> [PG.ElementTypeTree t] -> PG.ElementTypeTree t
elementTypeTreeVertex vtype = PG.ElementTypeTree (PG.ElementTypeVertex vtype)

encodeProperties :: M.Map Name Term -> [PropertyAdapter s t v] -> Flow s (M.Map PG.PropertyKey v)
encodeProperties fields adapters = do
  props <- Y.catMaybes <$> CM.mapM (encodeProperty fields) adapters
  return $ M.fromList $ fmap (\(PG.Property key val) -> (key, val)) props

encodeProperty :: M.Map Name Term -> PropertyAdapter s t v -> Flow s (Maybe (PG.Property v))
encodeProperty fields adapter = do
  case M.lookup fname fields of
    Nothing -> case ftyp of
      TypeOptional _ -> pure Nothing
      _ -> fail $ "expected field not found in record: " ++ unName fname
    Just value -> case ftyp of
      TypeOptional _ -> case fullyStripTerm value of
        TermOptional ov -> case ov of
          Nothing -> pure Nothing
          Just v -> Just <$> encodeValue v
        _ -> unexpected "optional term" $ show value
      _ -> Just <$> encodeValue value
  where
    fname = fieldTypeName $ adapterSource adapter
    ftyp = stripType (fieldTypeType $ adapterSource adapter)
    encodeValue v = coderEncode (adapterCoder adapter) (Field fname v)

findAdjacenEdgeAdapters :: (Show t, Show v)
  => Schema s t v -> t -> t -> PG.VertexLabel -> PG.Direction -> [FieldType] -> Flow s [AdjacentEdgeAdapter s a t v]
findAdjacenEdgeAdapters schema vidType eidType parentLabel dir fields = Y.catMaybes <$> CM.mapM toSpec fields
  where
    toSpec field = case getTypeAnnotation key (fieldTypeType field) of
      Nothing -> pure Nothing
      Just a -> do
        label <- PG.EdgeLabel <$> Expect.string a
        elad <- elementCoder (Just (dir, parentLabel)) schema (fieldTypeType field) vidType eidType
        return $ Just $ AdjacentEdgeAdapter dir field label elad
    key = case dir of
      PG.DirectionOut -> outEdgeLabelKey schema
      PG.DirectionIn -> inEdgeLabelKey schema

findIdProjectionSpec :: Bool -> Name -> Name -> [FieldType] -> Flow s (Y.Maybe (ProjectionSpec a))
findIdProjectionSpec required tname idKey fields = withTrace "find id field" $ do
  mid <- findSingleFieldWithAnnotationKey tname idKey fields
  case mid of
    Nothing -> if required
      then fail $ "no " ++ unName idKey ++ " field"
      else pure Nothing
    Just mi -> do
      spec <- case getTypeAnnotation idKey (fieldTypeType mi) of
        Nothing -> pure ValueSpecValue
        Just t -> decodeValueSpec t
      return $ Just $ ProjectionSpec mi spec Nothing

findIncidentVertexAdapter :: (Show t, Show v) => Schema s t v -> t -> t -> ProjectionSpec v -> Flow s (Name, ElementAdapter s t v)
findIncidentVertexAdapter schema vidType eidType spec = do
    adapter <- elementCoder Nothing schema (fieldTypeType field) vidType eidType
    return (fieldTypeName field, adapter)
  where
    field = projectionSpecField spec

findLabelString :: Type -> Name -> Name -> Flow s String
findLabelString source tname labelKey = case getTypeAnnotation labelKey source of
  Nothing -> pure $ unName tname
  Just labelTerm -> Expect.string labelTerm

findProjectionSpec :: Name -> Name -> Name -> [FieldType] -> Flow s (Y.Maybe (ProjectionSpec a))
findProjectionSpec tname key aliasKey fields = withTrace ("find " ++ show key ++ " projection") $ do
  mfield <- findSingleFieldWithAnnotationKey tname key fields
  case mfield of
    Nothing -> pure Nothing
    Just field -> do
      spec <- decodeValueSpec $ Y.fromJust $ getTypeAnnotation key $ fieldTypeType field
      alias <- case getTypeAnnotation aliasKey $ fieldTypeType field of
        Nothing -> pure Nothing
        Just t -> Just <$> Expect.string t
      return $ Just $ ProjectionSpec field spec alias

findPropertySpecs :: Schema s t v -> PG.ElementKind -> [FieldType] -> Flow s [ProjectionSpec a]
findPropertySpecs schema kind fields = CM.mapM toSpec $ L.filter isPropField fields
  where
    isPropField field = not (hasSpecialAnnotation || hasSpecialFieldName)
      where
        hasSpecialAnnotation = L.foldl (\b k -> b || hasAnnotation k) False ((ignoreKey schema):specialKeys)
        hasSpecialFieldName = L.foldl (\b n -> b || hasName n) False specialKeys
        specialKeys = case kind of
          PG.ElementKindVertex -> [vertexIdKey schema, outEdgeLabelKey schema, inEdgeLabelKey schema]
          PG.ElementKindEdge -> [edgeIdKey schema, outVertexKey schema, inVertexKey schema]
        hasAnnotation key = Y.isJust $ getTypeAnnotation key $ fieldTypeType field
        hasName fname = fieldTypeName field == fname
    toSpec field = do
      alias <- case (getTypeAnnotation (propertyKeyKey schema) $ fieldTypeType field) of
        Nothing -> pure Nothing
        Just a -> Just <$> Expect.string a
      values <- case (getTypeAnnotation (propertyValueKey schema) $ fieldTypeType field) of
        Nothing -> pure ValueSpecValue
        Just sp -> decodeValueSpec sp
      return $ ProjectionSpec field values alias

findSingleFieldWithAnnotationKey :: Name -> Name -> [FieldType] -> Flow s (Y.Maybe FieldType)
findSingleFieldWithAnnotationKey tname key fields = withTrace ("find " ++ show key ++ " field") $ do
  let matches = L.filter (\f -> Y.isJust $ getTypeAnnotation key $ fieldTypeType f) fields
  if L.length matches > 1
    then fail $ "Multiple fields marked as '" ++ unName key ++ "' in record type " ++ unName tname ++ ": "
      ++ (L.intercalate ", " (unName . fieldTypeName <$> matches))
    else return $ if L.null matches then Nothing else Just $ L.head matches

hasVertexAdapters :: PG.Direction -> Y.Maybe (ProjectionSpec a) -> Y.Maybe (ProjectionSpec a) -> Bool
hasVertexAdapters dir mOutSpec mInSpec = case dir of
  PG.DirectionOut -> Y.isJust mInSpec
  PG.DirectionIn -> Y.isJust mOutSpec
  PG.DirectionBoth -> Y.isJust mOutSpec && Y.isJust mInSpec

-- TODO; infer lossiness
lossy = True

noDecoding :: String -> Flow s x
noDecoding cat = fail $ cat ++ " decoding is not yet supported"

projectionAdapter :: t
  -> Coder s s Term v
  -> ProjectionSpec a
  -> String
  -> Flow s (IdAdapter s t v)
projectionAdapter idtype coder spec key = do
    traversal <- parseValueSpec $ projectionSpecValues spec
    let field = projectionSpecField spec
    let encode = \typ -> traverseToSingleTerm (key ++ "-projection") traversal typ >>= coderEncode coder
    return (fieldTypeName field, Adapter lossy (fieldTypeType field) idtype $ Coder encode decode)
  where
    decode _ = noDecoding $ "edge '" ++ key ++ "'"

propertyAdapter :: Schema s t v -> ProjectionSpec a -> Flow s (PropertyAdapter s t v)
propertyAdapter schema (ProjectionSpec tfield values alias) = do
  let key = PG.PropertyKey $ case alias of
        Nothing -> unName $ fieldTypeName tfield
        Just k -> k
  pt <- coderEncode (schemaPropertyTypes schema) $ fieldTypeType tfield
  traversal <- parseValueSpec values
  let coder = Coder encode decode
        where
          encode dfield = withTrace ("encode property field " ++ show (unName $ fieldTypeName tfield)) $ do
            if fieldName dfield /= fieldTypeName tfield
              then unexpected ("field '" ++ unName (fieldTypeName tfield) ++ "'") $ show dfield
              else do
                result <- traverseToSingleTerm "property traversal" traversal $ fieldTerm dfield
                value <- coderEncode (schemaPropertyValues schema) result
                return $ PG.Property key value
          decode _ = noDecoding "property"
  return $ Adapter lossy tfield (PG.PropertyType key pt True) coder

propertyTypes propAdapters = toPropertyType <$> propAdapters
  where
    toPropertyType a = PG.PropertyType (PG.propertyTypeKey $ adapterTarget a) (PG.propertyTypeValue $ adapterTarget a) True

selectEdgeId fields (fname, ad) = case M.lookup fname fields of
  Nothing -> fail $ "no " ++ unName fname ++ " in record"
  Just t -> coderEncode (adapterCoder ad) t

selectVertexId :: M.Map Name Term -> IdAdapter s t v -> Flow s v
selectVertexId  fields (fname, ad) = case M.lookup fname fields of
  Nothing -> fail $ "no " ++ unName fname ++ " in record"
  Just t -> coderEncode (adapterCoder ad) t

traverseToSingleTerm :: String -> (Term -> Flow s [Term]) -> Term -> Flow s Term
traverseToSingleTerm desc traversal term = do
  terms <- traversal term
  case terms of
    [] -> fail $ desc ++ " did not resolve to a term"
    [t] -> pure t
    _ -> fail $ desc ++ " resolved to multiple terms"

vertexCoder :: (Show t, Show v)
  => Schema s t v
  -> Type
  -> t
  -> Name
  -> PG.VertexLabel -> IdAdapter s t v -> [PropertyAdapter s t v]
  -> [AdjacentEdgeAdapter s a t v]
  -> ElementAdapter s t v
vertexCoder schema source vidType tname vlabel idAdapter propAdapters edgeAdapters = Adapter lossy source target coder
  where
    target = elementTypeTreeVertex vtype depTypes
    vtype = PG.VertexType vlabel vidType $ propertyTypes propAdapters
    depTypes = adapterTarget . adjacentEdgeAdapterAdapter <$> edgeAdapters
    coder = Coder encode decode
      where
        encode term = case stripTerm term of
            TermOptional (Just ot) -> encode ot
            TermRecord (Record tname' fields) -> do
              checkRecordName tname tname'
              let fieldsm = fieldMap fields
              vid <- selectVertexId fieldsm idAdapter
              props <- encodeProperties (fieldMap fields) propAdapters
              deps <- L.concat <$> CM.mapM (findDependency vid fieldsm) edgeAdapters
              return $ elementTreeVertex (PG.Vertex vlabel vid props) deps
            _ -> unexpected "record (2)" $ show term
          where
            findDependency vid fieldsm (AdjacentEdgeAdapter dir field elabel ad) = do
                case M.lookup (fieldTypeName field) fieldsm of
                  Nothing -> pure []
                  Just fterm -> fixTree <$> coderEncode (adapterCoder ad) fterm
              where
                fixTree tree = case PG.elementTreeSelf tree of
                  -- If the child element is a vertex, we also need an edge
                  PG.ElementVertex v -> do
                      [PG.ElementTree edge [tree]]
                    where
                      edgeid = schemaDefaultEdgeId schema
                      edge = PG.ElementEdge $ PG.Edge elabel edgeid (proj True) (proj False) M.empty
                      otherid = PG.vertexId v
                      proj out = case dir of
                        PG.DirectionOut -> if out then vid else otherid
                        PG.DirectionIn -> if out then otherid else vid

                  -- If the child element is an edge, populate the in/out vertex
                  PG.ElementEdge e -> [tree {PG.elementTreeSelf = PG.ElementEdge $ fixEdge e}]
                fixEdge e = case dir of
                  PG.DirectionOut -> e {PG.edgeOut = vid}
                  PG.DirectionIn -> e {PG.edgeIn = vid}
        decode el = noDecoding "vertex"

vertexIdAdapter :: Schema s t v -> t -> Name -> Name -> [FieldType] -> Flow s (IdAdapter s t v)
vertexIdAdapter schema vidType name idKey fields = do
  idSpec <- Y.fromJust <$> findIdProjectionSpec True name idKey fields
  idAdapter <- projectionAdapter vidType (schemaVertexIds schema) idSpec "id"
  return idAdapter
