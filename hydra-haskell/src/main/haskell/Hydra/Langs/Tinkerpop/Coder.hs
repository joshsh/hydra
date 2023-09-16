module Hydra.Langs.Tinkerpop.Coder (
  elementCoder,
) where

import Hydra.Kernel
import Hydra.Langs.Tinkerpop.Mappings
import Hydra.Langs.Tinkerpop.TermsToElements
import qualified Hydra.Langs.Tinkerpop.PropertyGraph as PG
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y


type ElementAdapter s t v = Adapter s s Type (PG.ElementTypeTree t) Term (PG.ElementTree v)

type PropertyAdapter s t v = Adapter s s (FieldType) (PG.PropertyType t) (Field) (PG.Property v)

type IdAdapter s t v = (FieldName, Adapter s s Type t Term v)

data AdjacentEdgeAdapter s a t v = AdjacentEdgeAdapter {
  adjacentEdgeAdapterDirection :: PG.Direction,
  adjacentEdgeAdapterField :: FieldType,
  adjacentEdgeAdapterLabel :: PG.EdgeLabel,
  adjacentEdgeAdapterAdapter :: ElementAdapter s t v}

data ProjectionSpec a = ProjectionSpec {
  projectionSpecField :: FieldType,
  projectionSpecValues :: ValueSpec,
  projectionSpecAlias :: Maybe String}

check :: Bool -> Flow s () -> Flow s ()
check b err = if b then pure () else err

checkRecordName expected actual = check (actual == expected) $
  unexpected ("record of type " ++ unName expected) ("record of type " ++ unName actual)

edgeCoder :: PG.Direction -> Schema s t v
  -> Type
  -> t
  -> Name
  -> PG.EdgeLabel -> PG.VertexLabel -> PG.VertexLabel
  -> Maybe (IdAdapter s t v) -> Maybe (IdAdapter s t v) -> Maybe (IdAdapter s t v) -> [PropertyAdapter s t v]
  -> ElementAdapter s t v
edgeCoder dir schema source eidType tname label outLabel inLabel mIdAdapter outAdapter inAdapter propAdapters
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
            return $ elementTreeEdge (PG.Edge label id outId inId props) []
          _ -> unexpected "record (1)" $ show term
        decode el = noDecoding "edge"
        getVertexId dir1 fieldsm adapter = if dir1 == dir
          then pure $ schemaDefaultVertexId schema
          else case adapter of
            Nothing -> fail $ "no adapter for " ++ show dir1 ++ " with " ++ show dir
            Just ad -> selectVertexId fieldsm ad

elementCoder :: (Show t, Show v) => Y.Maybe (PG.Direction, PG.VertexLabel)
  -> Schema s t v
  -> Type
  -> t -> t
  -> Flow s (ElementAdapter s t v)
elementCoder mparent schema source vidType eidType = case stripType source of
    TypeOptional ot -> elementCoder mparent schema ot vidType eidType
    TypeRecord (RowType name _ fields) -> withTrace ("adapter for " ++ unName name) $ do
      mOutSpec <- findProjectionSpec name outVertexKey outVertexLabelKey fields
      mInSpec <- findProjectionSpec name inVertexKey inVertexLabelKey fields

      -- TODO: deprecate "kind"
      kind <- case getTypeAnnotation "kind" source of
        Nothing -> pure $ if hasVertexAdapters mOutSpec mInSpec
          then PG.ElementKindEdge
          else PG.ElementKindVertex
        Just kindTerm -> do
          s <- Expect.string kindTerm
          case s of
            "vertex" -> return PG.ElementKindVertex
            "edge" -> if Y.isNothing mOutSpec || Y.isNothing mInSpec
              then fail $ "Record type marked as an edge type, but missing 'out' and/or 'in' fields: " ++ unName name
              else return PG.ElementKindEdge

      propSpecs <- findPropertySpecs kind fields
      propAdapters <- CM.mapM (propertyAdapter schema) propSpecs

      case kind of
        PG.ElementKindVertex -> do
          label <- PG.VertexLabel <$> findLabelString name vertexLabelKey
          idAdapter <- vertexIdAdapter name vertexIdKey fields
          outEdgeAdapters <- edgeAdapters label PG.DirectionOut fields
          inEdgeAdapters <- edgeAdapters label PG.DirectionIn fields
          return $ vertexCoder schema source vidType name label idAdapter propAdapters (outEdgeAdapters ++ inEdgeAdapters)
        PG.ElementKindEdge -> do
          label <- PG.EdgeLabel <$> findLabelString name edgeLabelKey
          idAdapter <- edgeIdAdapter name edgeIdKey fields
          outAdapter <- Y.maybe (pure Nothing) (\s -> Just <$> projectionAdapter vidType (schemaVertexIds schema) s "out") mOutSpec
          inAdapter <- Y.maybe (pure Nothing) (\s -> Just <$> projectionAdapter vidType (schemaVertexIds schema) s "in") mInSpec
          outLabel <- case mOutSpec of
            Nothing -> pure parentLabel
            Just spec -> Y.maybe (fail "no out-vertex label") (pure . PG.VertexLabel) $ projectionSpecAlias spec
          inLabel <- case mInSpec of
            Nothing -> pure parentLabel
            Just spec -> Y.maybe (fail "no in-vertex label") (pure . PG.VertexLabel) $ projectionSpecAlias spec
          return $ edgeCoder dir schema source eidType name label outLabel inLabel idAdapter outAdapter inAdapter propAdapters

    _ -> unexpected "record type" $ show source
  where
    dir = Y.maybe PG.DirectionBoth fst mparent
    parentLabel = Y.maybe (PG.VertexLabel "NOLABEL") snd mparent

    vertexIdAdapter name idKey fields = do
      idSpec <- Y.fromJust <$> findId True name idKey fields
      idAdapter <- projectionAdapter vidType (schemaVertexIds schema) idSpec "id"
      return idAdapter

    edgeIdAdapter name idKey fields = do
      mIdSpec <- findId False name idKey fields
      case mIdSpec of
        Nothing -> pure Nothing
        Just idSpec -> Just <$> projectionAdapter eidType (schemaEdgeIds schema) idSpec "id"

    hasVertexAdapters mOutSpec mInSpec = case dir of
      PG.DirectionOut -> Y.isJust mInSpec
      PG.DirectionIn -> Y.isJust mOutSpec
      PG.DirectionBoth -> Y.isJust mOutSpec && Y.isJust mInSpec

    vertexLabelKey = annotationSchemaVertexLabel $ schemaAnnotations schema
    edgeLabelKey = annotationSchemaEdgeLabel $ schemaAnnotations schema
    vertexIdKey = annotationSchemaVertexId $ schemaAnnotations schema
    edgeIdKey = annotationSchemaEdgeId $ schemaAnnotations schema
    propertyKeyKey = annotationSchemaPropertyKey $ schemaAnnotations schema
    propertyValueKey = annotationSchemaPropertyValue $ schemaAnnotations schema
    outVertexKey = annotationSchemaOutVertex $ schemaAnnotations schema
    outVertexLabelKey = annotationSchemaOutVertexLabel $ schemaAnnotations schema
    inVertexKey = annotationSchemaInVertex $ schemaAnnotations schema
    inVertexLabelKey = annotationSchemaInVertexLabel $ schemaAnnotations schema
    outEdgeLabelKey = annotationSchemaOutEdgeLabel $ schemaAnnotations schema
    inEdgeLabelKey = annotationSchemaInEdgeLabel $ schemaAnnotations schema
    ignoreKey = annotationSchemaIgnore $ schemaAnnotations schema

    findLabelString tname labelKey = case getTypeAnnotation labelKey source of
      Nothing -> pure $ unName tname
      Just labelTerm -> Expect.string labelTerm

    findId required tname idKey fields = withTrace "find id field" $ do
      mid <- findField tname idKey fields
      case mid of
        Nothing -> if required
          then fail $ "no " ++ idKey ++ " field"
          else pure Nothing
        Just mi -> do
          spec <- case getTypeAnnotation idKey (fieldTypeType mi) of
            Nothing -> pure ValueSpecValue
            Just t -> decodeValueSpec t
          return $ Just $ ProjectionSpec mi spec Nothing

    findProjectionSpec tname key aliasKey fields = withTrace ("find " ++ show key ++ " projection") $ do
      mfield <- findField tname key fields
      case mfield of
        Nothing -> pure Nothing
        Just field -> do
          spec <- decodeValueSpec $ Y.fromJust $ getTypeAnnotation key $ fieldTypeType field
          alias <- case getTypeAnnotation aliasKey $ fieldTypeType field of
            Nothing -> pure Nothing
            Just t -> Just <$> Expect.string t
          return $ Just $ ProjectionSpec field spec alias

    findField tname key fields = withTrace ("find " ++ show key ++ " field") $ do
      let matches = L.filter (\f -> Y.isJust $ getTypeAnnotation key $ fieldTypeType f) fields
      if L.length matches > 1
        then fail $ "Multiple fields marked as '" ++ key ++ "' in record type " ++ unName tname ++ ": "
          ++ (L.intercalate ", " (unFieldName . fieldTypeName <$> matches))
        else return $ if L.null matches then Nothing else Just $ L.head matches

    findPropertySpecs kind fields = CM.mapM toSpec $ L.filter isPropField fields
      where
        isPropField field = not (hasSpecialAnnotation || hasSpecialFieldName)
          where
            hasSpecialAnnotation = L.foldl (\b k -> b || hasAnnotation k) False (ignoreKey:specialKeys)
            hasSpecialFieldName = L.foldl (\b n -> b || hasName n) False specialKeys
            specialKeys = case kind of
              PG.ElementKindVertex -> [vertexIdKey, outEdgeLabelKey, inEdgeLabelKey]
              PG.ElementKindEdge -> [edgeIdKey, outVertexKey, inVertexKey]
            hasAnnotation key = Y.isJust $ getTypeAnnotation key $ fieldTypeType field
            hasName fname = fieldTypeName field == FieldName fname
        toSpec field = do
          alias <- case (getTypeAnnotation propertyKeyKey $ fieldTypeType field) of
            Nothing -> pure Nothing
            Just a -> Just <$> Expect.string a
          values <- case (getTypeAnnotation propertyValueKey $ fieldTypeType field) of
            Nothing -> pure ValueSpecValue
            Just sp -> decodeValueSpec sp
          return $ ProjectionSpec field values alias

    edgeAdapters vlabel dir fields = Y.catMaybes <$> CM.mapM toSpec fields
      where
        toSpec field = case getTypeAnnotation key (fieldTypeType field) of
          Nothing -> pure Nothing
          Just a -> do
            label <- PG.EdgeLabel <$> Expect.string a
            elad <- elementCoder (Just (dir, vlabel)) schema (fieldTypeType field) vidType eidType 
            return $ Just $ AdjacentEdgeAdapter dir field label elad
        key = case dir of
          PG.DirectionOut -> outEdgeLabelKey
          PG.DirectionIn -> inEdgeLabelKey

elementTreeEdge :: PG.Edge v -> [PG.ElementTree v] -> PG.ElementTree v
elementTreeEdge edge = PG.ElementTree (PG.ElementEdge edge)

elementTreeVertex :: PG.Vertex v -> [PG.ElementTree v] -> PG.ElementTree v
elementTreeVertex vertex = PG.ElementTree (PG.ElementVertex vertex)

elementTypeTreeEdge :: PG.EdgeType t -> [PG.ElementTypeTree t] -> PG.ElementTypeTree t
elementTypeTreeEdge etype = PG.ElementTypeTree (PG.ElementTypeEdge etype)

elementTypeTreeVertex :: PG.VertexType t -> [PG.ElementTypeTree t] -> PG.ElementTypeTree t
elementTypeTreeVertex vtype = PG.ElementTypeTree (PG.ElementTypeVertex vtype)

encodeProperties :: M.Map FieldName Term -> [PropertyAdapter s t v] -> Flow s (M.Map PG.PropertyKey v)
encodeProperties fields adapters = do
  props <- Y.catMaybes <$> CM.mapM (encodeProperty fields) adapters
  return $ M.fromList $ fmap (\(PG.Property key val) -> (key, val)) props

encodeProperty :: M.Map FieldName Term -> PropertyAdapter s t v -> Flow s (Maybe (PG.Property v))
encodeProperty fields adapter = do
  case M.lookup fname fields of
    Nothing -> case ftyp of
      TypeOptional _ -> pure Nothing
      _ -> fail $ "expected field not found in record: " ++ unFieldName fname
    Just value -> case ftyp of
      TypeOptional _ -> case stripTerm value of
        TermOptional ov -> case ov of
          Nothing -> pure Nothing
          Just v -> Just <$> encodeValue v
        _ -> unexpected "optional term" $ show value
      _ -> Just <$> encodeValue value
  where
    fname = fieldTypeName $ adapterSource adapter
    ftyp = stripType (fieldTypeType $ adapterSource adapter)
    encodeValue v = coderEncode (adapterCoder adapter) (Field fname v)

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
        Nothing -> unFieldName $ fieldTypeName tfield
        Just k -> k
  pt <- coderEncode (schemaPropertyTypes schema) $ fieldTypeType tfield
  traversal <- parseValueSpec values
  let coder = Coder encode decode
        where
          encode dfield = withTrace ("encode property field " ++ show (unFieldName $ fieldTypeName tfield)) $ do
            if fieldName dfield /= fieldTypeName tfield
              then unexpected ("field '" ++ unFieldName (fieldTypeName tfield) ++ "'") $ show dfield
              else do
                result <- traverseToSingleTerm "property traversal" traversal $ fieldTerm dfield
                value <- coderEncode (schemaPropertyValues schema) result
                return $ PG.Property key value
          decode _ = noDecoding "property"
  return $ Adapter lossy tfield (PG.PropertyType key pt) coder

propertyTypes propAdapters = toPropertyType <$> propAdapters
  where
    toPropertyType a = PG.PropertyType (PG.propertyTypeKey $ adapterTarget a) (PG.propertyTypeValue $ adapterTarget a)

selectEdgeId fields (fname, ad) = case M.lookup fname fields of
  Nothing -> fail $ "no " ++ unFieldName fname ++ " in record"
  Just t -> coderEncode (adapterCoder ad) t

selectVertexId :: M.Map FieldName Term -> IdAdapter s t v -> Flow s v
selectVertexId  fields (fname, ad) = case M.lookup fname fields of
  Nothing -> fail $ "no " ++ unFieldName fname ++ " in record"
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
vertexCoder schema source vidType tname label idAdapter propAdapters edgeAdapters = Adapter lossy source target coder
  where
    target = elementTypeTreeVertex vtype depTypes
    vtype = PG.VertexType label vidType $ propertyTypes propAdapters
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
              deps <- Y.catMaybes <$> CM.mapM (findDeps vid fieldsm) edgeAdapters
              return $ elementTreeVertex (PG.Vertex label vid props) deps
            _ -> unexpected "record (2)" $ show term
          where
            findDeps vid fieldsm (AdjacentEdgeAdapter dir field label ad) = do
                case M.lookup (fieldTypeName field) fieldsm of
                  Nothing -> pure Nothing
                  Just fterm -> Just <$> (coderEncode (adapterCoder ad) fterm >>= fixTree)
              where
                fixTree tree = case PG.elementTreeSelf tree of
                  PG.ElementEdge e -> pure $ tree {PG.elementTreeSelf = PG.ElementEdge $ fixEdge e}
                  _ -> unexpected "edge tree" $ show tree
                fixEdge e = case dir of
                  PG.DirectionOut -> e {PG.edgeOut = vid}
                  PG.DirectionIn -> e {PG.edgeIn = vid}
        decode el = noDecoding "vertex"
