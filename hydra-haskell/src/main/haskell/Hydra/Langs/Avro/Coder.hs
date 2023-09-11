module Hydra.Langs.Avro.Coder (
  AvroEnvironment(..),
  AvroHydraAdapter(..),
  AvroQualifiedName(..),
  avroHydraAdapter,
  emptyAvroEnvironment,
) where

import Hydra.Kernel
import Hydra.Langs.Json.Eliminate
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Types as Types
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Langs.Avro.Schema as Avro
import qualified Hydra.Json as Json

import qualified Text.Read as TR
import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


data AvroEnvironment a = AvroEnvironment {
  avroEnvironmentNamedAdapters :: M.Map AvroQualifiedName (AvroHydraAdapter a),
  avroEnvironmentNamespace :: Maybe String,
  avroEnvironmentElements :: M.Map Name (Element a), -- note: only used in the term coders
  avroEnvironmentCreateAnnotation :: M.Map String (Term a) -> a}
type AvroHydraAdapter a = Adapter (AvroEnvironment a) (AvroEnvironment a) Avro.Schema (Type a) Json.Value (Term a)

data AvroQualifiedName = AvroQualifiedName (Maybe String) String deriving (Eq, Ord, Show)

data ForeignKey = ForeignKey Name (String -> Name)

data PrimaryKey = PrimaryKey FieldName (String -> Name)

emptyAvroEnvironment = AvroEnvironment M.empty Nothing M.empty

avro_foreignKey = "@foreignKey"
avro_primaryKey = "@primaryKey"

avroHydraAdapter :: (Ord a, Show a) => Avro.Schema -> Flow (AvroEnvironment a) (AvroHydraAdapter a)
avroHydraAdapter schema = case schema of
    Avro.SchemaArray (Avro.Array s) -> do
      ad <- avroHydraAdapter s
      let coder = Coder {
            coderEncode = \(Json.ValueArray vals) -> Terms.list <$> (CM.mapM (coderEncode $ adapterCoder ad) vals),
            coderDecode = \(TermList vals) -> Json.ValueArray <$> (CM.mapM (coderDecode $ adapterCoder ad) vals)}
      return $ Adapter (adapterIsLossy ad) schema (Types.list $ adapterTarget ad) coder
    Avro.SchemaMap (Avro.Map_ s) -> do
      ad <- avroHydraAdapter s
      let pairToHydra (k, v) = do
            v' <- coderEncode (adapterCoder ad) v
            return (Terms.string k, v')
      let coder = Coder {
            coderEncode = \(Json.ValueObject m) -> Terms.map . M.fromList <$> (CM.mapM pairToHydra $ M.toList m),
            coderDecode = \m -> Json.ValueObject <$> Expect.map Expect.string (coderDecode (adapterCoder ad)) m}
      return $ Adapter (adapterIsLossy ad) schema (Types.map Types.string $ adapterTarget ad) coder
    Avro.SchemaNamed n -> do
        let ns = Avro.namedNamespace n
        env <- getState

        let manns = namedAnnotationsToCore n
        let ann = if M.null manns then Nothing else (Just $ avroEnvironmentCreateAnnotation env manns)

        let lastNs = avroEnvironmentNamespace env
        let nextNs = Y.maybe lastNs Just ns
        putState $ env {avroEnvironmentNamespace = nextNs}

        let qname = AvroQualifiedName nextNs (Avro.namedName n)
        let hydraName = avroNameToHydraName qname

        -- Note: if a named type is redefined (an illegal state for which the Avro spec does not provide a resolution),
        --       we just take the first definition and ignore the second.
        ad <- case getAvroHydraAdapter qname env of
          Just ad -> fail $ "Avro named type defined more than once: " ++ show qname
          Nothing -> do
            ad <- case Avro.namedType n of
              Avro.NamedTypeEnum (Avro.Enum_ syms mdefault) -> simpleAdapter typ encode decode  -- TODO: use default value
                where
                  typ = TypeUnion (RowType hydraName Nothing $ toField <$> syms)
                    where
                      toField s = FieldType (FieldName s) Types.unit
                  encode (Json.ValueString s) = pure $ TermUnion (Injection hydraName $ Field (FieldName s) Terms.unit)
                  -- Note: we simply trust that data coming from the Hydra side is correct
                  decode (TermUnion (Injection _ (Field fn _))) = return $ Json.ValueString $ unFieldName fn
              Avro.NamedTypeFixed (Avro.Fixed size) -> simpleAdapter Types.binary encode decode
                where
                  encode (Json.ValueString s) = pure $ Terms.binary s
                  decode term = Json.ValueString <$> Expect.binary term
              Avro.NamedTypeRecord r -> do
                  let avroFields = Avro.recordFields r
                  adaptersByFieldName <- M.fromList <$> (CM.mapM prepareField avroFields)
                  pk <- findPrimaryKeyField qname avroFields
                  -- TODO: Nothing values for optional fields
                  let encodePair (k, v) = case M.lookup k adaptersByFieldName of
                        Nothing -> fail $ "unrecognized field for " ++ showQname qname ++ ": " ++ show k
                        Just (f, ad) -> do
                          v' <- coderEncode (adapterCoder ad) v
                          return $ Field (FieldName k) v'
                  let decodeField (Field (FieldName k) v) = case M.lookup k adaptersByFieldName of
                        Nothing -> fail $ "unrecognized field for " ++ showQname qname ++ ": " ++ show k
                        Just (f, ad) -> do
                          v' <- coderDecode (adapterCoder ad) v
                          return (k, v')
                  let lossy = L.foldl (\b (_, ad) -> b || adapterIsLossy ad) False $ M.elems adaptersByFieldName
                  let hfields = toHydraField <$> M.elems adaptersByFieldName
                  let target = TypeRecord $ RowType hydraName Nothing hfields
                  let coder = Coder {
                    -- Note: the order of the fields is changed
                    coderEncode = \(Json.ValueObject m) -> do
                      fields <- CM.mapM encodePair $ M.toList m
                      let term = TermRecord $ Record hydraName fields
                      addElement term target pk fields
                      return term,
                    coderDecode = \(TermRecord (Record _ fields)) -> Json.ValueObject . M.fromList <$> (CM.mapM decodeField fields)}
                  return $ Adapter lossy schema target coder
                where
                  toHydraField (f, ad) = FieldType (FieldName $ Avro.fieldName f) $ adapterTarget ad
            env <- getState
            putState $ putAvroHydraAdapter qname ad env
            return $ annotate ann ad

        env2 <- getState
        putState $ env2 {avroEnvironmentNamespace = lastNs}
        return ad
      where
        addElement term typ pk fields = case pk of
          Nothing -> pure ()
          Just (PrimaryKey fname constr) -> case L.filter isPkField fields of
              [] -> pure ()
              [field] -> do
                  s <- termToString $ fieldTerm field
                  let name = constr s
                  let el = Element name term
                  env <- getState
                  putState $ env {avroEnvironmentElements = M.insert name el (avroEnvironmentElements env)}
                  return ()
              _ -> fail $ "multiple fields named " ++ unFieldName fname
            where
              isPkField field = fieldName field == fname
        findPrimaryKeyField qname avroFields = do
          keys <- Y.catMaybes <$> CM.mapM primaryKey avroFields
          case keys of
            [] -> pure Nothing
            [k] -> pure $ Just k
            _ -> fail $ "multiple primary key fields for " ++ show qname
        prepareField f = do
          fk <- foreignKey f

          env <- getState
          let manns = fieldAnnotationsToCore f
          let ann = if M.null manns then Nothing else (Just $ avroEnvironmentCreateAnnotation env manns)

          ad <- case fk of
            Nothing -> avroHydraAdapter $ Avro.fieldType f
            Just (ForeignKey name constr) -> do
                ad <- avroHydraAdapter $ Avro.fieldType f
                let decodeTerm = \(TermVariable name) -> do -- TODO: not symmetrical
                      term <- stringToTerm (adapterTarget ad) $ unName name
                      coderDecode (adapterCoder ad) term
                let encodeValue v = do
                      s <- coderEncode (adapterCoder ad) v >>= termToString
                      return $ TermVariable $ constr s
                -- Support three special cases of foreign key types: plain, optional, and list
                case stripType (adapterTarget ad) of
                  TypeOptional (TypeLiteral lit) -> forTypeAndCoder ad (Types.optional elTyp) coder
                    where
                      coder = Coder {
                        coderEncode = \json -> (TermOptional . Just) <$> encodeValue json,
                        coderDecode = decodeTerm}
                  TypeList (TypeLiteral lit) -> forTypeAndCoder ad (Types.list elTyp) coder
                    where
                      coder = Coder {
                        coderEncode = \json -> TermList <$> (expectArray json >>= CM.mapM encodeValue),
                        coderDecode = decodeTerm}
                  TypeLiteral lit -> forTypeAndCoder ad elTyp coder
                    where
                      coder = Coder {
                        coderEncode = encodeValue,
                        coderDecode = decodeTerm}
                  _ -> fail $ "unsupported type annotated as foreign key: " ++ (show $ typeVariant $ adapterTarget ad)
              where
                forTypeAndCoder ad typ coder = pure $ Adapter (adapterIsLossy ad) (Avro.fieldType f) typ coder
                elTyp = TypeVariable name
          return (Avro.fieldName f, (f, annotate ann ad))
    Avro.SchemaPrimitive p -> case p of
        Avro.PrimitiveNull -> simpleAdapter Types.unit encode decode
          where
            encode (Json.ValueString s) = pure $ Terms.string s
            decode term = Json.ValueString <$> Expect.string term
        Avro.PrimitiveBoolean -> simpleAdapter Types.boolean encode decode
          where
            encode (Json.ValueBoolean b) = pure $ Terms.boolean b
            decode term = Json.ValueBoolean <$> Expect.boolean term
        Avro.PrimitiveInt -> simpleAdapter Types.int32 encode decode
          where
            encode (Json.ValueNumber d) = pure $ Terms.int32 $ doubleToInt d
            decode term = Json.ValueNumber . fromIntegral <$> Expect.int32 term
        Avro.PrimitiveLong -> simpleAdapter Types.int64 encode decode
          where
            encode (Json.ValueNumber d) = pure $ Terms.int64 $ doubleToInt d
            decode term = Json.ValueNumber . fromIntegral <$> Expect.int64 term
        Avro.PrimitiveFloat -> simpleAdapter Types.float32 encode decode
          where
            encode (Json.ValueNumber d) = pure $ Terms.float32 $ realToFrac d
            decode term = Json.ValueNumber . realToFrac <$> Expect.float32 term
        Avro.PrimitiveDouble -> simpleAdapter Types.float64 encode decode
          where
            encode (Json.ValueNumber d) = pure $ Terms.float64 d
            decode term = Json.ValueNumber <$> Expect.float64 term
        Avro.PrimitiveBytes -> simpleAdapter Types.binary encode decode
          where
            encode (Json.ValueString s) = pure $ Terms.binary s
            decode term = Json.ValueString <$> Expect.binary term
        Avro.PrimitiveString -> simpleAdapter Types.string encode decode
          where
            encode (Json.ValueString s) = pure $ Terms.string s
            decode term = Json.ValueString <$> Expect.string term
      where
        doubleToInt d = if d < 0 then ceiling d else floor d
    Avro.SchemaReference name -> do
      env <- getState
      let qname = parseAvroName (avroEnvironmentNamespace env) name
      case getAvroHydraAdapter qname env of
        Nothing -> fail $ "Referenced Avro type has not been defined: " ++ show qname
         ++ ". Defined types: " ++ show (M.keys $ avroEnvironmentNamedAdapters env)
        Just ad -> pure ad
    Avro.SchemaUnion (Avro.Union schemas) -> if L.length nonNulls > 1
        then fail $ "general-purpose unions are not yet supported: " ++ show schema
        else if L.null nonNulls
        then fail $ "cannot generate the empty type"
        else if hasNull
        then forOptional $ L.head nonNulls
        else do
          ad <- avroHydraAdapter $ L.head nonNulls
          return $ Adapter (adapterIsLossy ad) schema (adapterTarget ad) (adapterCoder ad)
      where
        hasNull = (not . L.null . L.filter isNull) schemas
        nonNulls = L.filter (not . isNull) schemas
        isNull schema = case schema of
          Avro.SchemaPrimitive Avro.PrimitiveNull -> True
          _ -> False
        forOptional s = do
          ad <- avroHydraAdapter s
          let coder = Coder {
                coderDecode = \(TermOptional ot) -> case ot of
                  Nothing -> pure $ Json.ValueNull
                  Just term -> coderDecode (adapterCoder ad) term,
                coderEncode = \v -> case v of
                  Json.ValueNull -> pure $ TermOptional Nothing
                  _ -> TermOptional . Just <$> coderEncode (adapterCoder ad) v}
          return $ Adapter (adapterIsLossy ad) schema (Types.optional $ adapterTarget ad) coder
  where
    simpleAdapter typ encode decode = pure $ Adapter False schema typ $ Coder encode decode
    annotate ann ad = case ann of
      Nothing -> ad
      Just n -> ad {adapterTarget = Types.annot n (adapterTarget ad)}

avroNameToHydraName :: AvroQualifiedName -> Name
avroNameToHydraName (AvroQualifiedName mns local) = unqualifyName $ QualifiedName (Namespace <$> mns) local

-- TODO: use me (for encoding annotations for which the type is not know) or lose me
--       A more robust solution would use jsonCoder together with an expected type
encodeAnnotationValue :: Ord a => Json.Value -> Term a
encodeAnnotationValue v = case v of
  Json.ValueArray vals -> Terms.list (encodeAnnotationValue <$> vals)
  Json.ValueBoolean b -> Terms.boolean b
  Json.ValueNull -> Terms.product []
  Json.ValueNumber d -> Terms.float64 d
  -- Note: JSON objects are untyped maps, not records, in that fields are unordered
  Json.ValueObject m -> Terms.map $ M.fromList (toEntry <$> M.toList m)
    where
      toEntry (k, v) = (Terms.string k, encodeAnnotationValue v)
  Json.ValueString s -> Terms.string s

fieldAnnotationsToCore :: Ord a => Avro.Field -> M.Map String (Term a)
fieldAnnotationsToCore f = M.fromList (toCore <$> (M.toList $ Avro.fieldAnnotations f))
  where
    toCore (k, v) = (k, encodeAnnotationValue v)

namedAnnotationsToCore :: Ord a => Avro.Named -> M.Map String (Term a)
namedAnnotationsToCore n = M.fromList (toCore <$> (M.toList $ Avro.namedAnnotations n))
  where
    toCore (k, v) = (k, encodeAnnotationValue v)

getAvroHydraAdapter :: AvroQualifiedName -> AvroEnvironment a -> Y.Maybe (AvroHydraAdapter a)
getAvroHydraAdapter qname = M.lookup qname . avroEnvironmentNamedAdapters

foreignKey :: Avro.Field -> Flow s (Maybe ForeignKey)
foreignKey f = case M.lookup avro_foreignKey (Avro.fieldAnnotations f) of
    Nothing -> pure Nothing
    Just v -> do
      m <- expectObject v
      tname <- Name <$> requireString "type" m
      pattern <- optString "pattern" m
      let constr = case pattern of
            Nothing -> Name
            Just pat -> patternToNameConstructor pat
      return $ Just $ ForeignKey tname constr

patternToNameConstructor :: String -> String -> Name
patternToNameConstructor pat = \s -> Name $ L.intercalate s $ Strings.splitOn "${}" pat

primaryKey :: Avro.Field -> Flow s (Maybe PrimaryKey)
primaryKey f = do
  case M.lookup avro_primaryKey $ Avro.fieldAnnotations f of
    Nothing -> pure Nothing
    Just v -> do
      s <- expectString v
      return $ Just $ PrimaryKey (FieldName $ Avro.fieldName f) $ patternToNameConstructor s

parseAvroName :: Maybe String -> String -> AvroQualifiedName
parseAvroName mns name = case L.reverse $ Strings.splitOn "." name of
  [local] -> AvroQualifiedName mns local
  (local:rest) -> AvroQualifiedName (Just $ L.intercalate "." $ L.reverse rest) local

putAvroHydraAdapter :: AvroQualifiedName -> AvroHydraAdapter a -> AvroEnvironment a -> AvroEnvironment a
putAvroHydraAdapter qname ad env = env {avroEnvironmentNamedAdapters = M.insert qname ad $ avroEnvironmentNamedAdapters env}

rewriteAvroSchemaM :: ((Avro.Schema -> Flow s Avro.Schema) -> Avro.Schema -> Flow s Avro.Schema) -> Avro.Schema -> Flow s Avro.Schema
rewriteAvroSchemaM f = rewrite fsub f
  where
    fsub recurse schema = case schema of
        Avro.SchemaArray (Avro.Array els) -> Avro.SchemaArray <$> (Avro.Array <$> recurse els)
        Avro.SchemaMap (Avro.Map_ vschema) -> Avro.SchemaMap <$> (Avro.Map_ <$> recurse vschema)
        Avro.SchemaNamed n -> do
          nt <- case Avro.namedType n of
            Avro.NamedTypeRecord (Avro.Record fields) -> Avro.NamedTypeRecord <$> (Avro.Record <$> (CM.mapM forField fields))
            t -> pure t
          return $ Avro.SchemaNamed $ n {Avro.namedType = nt}
        Avro.SchemaUnion (Avro.Union schemas) -> Avro.SchemaUnion <$> (Avro.Union <$> (CM.mapM recurse schemas))
        _ -> pure schema
      where
        forField f = do
          t <- recurse $ Avro.fieldType f
          return f {Avro.fieldType = t}

jsonToString :: Json.Value -> Flow s String
jsonToString v = case v of
  Json.ValueBoolean b -> pure $ if b then "true" else "false"
  Json.ValueString s -> pure s
  Json.ValueNumber d -> pure $ if fromIntegral (round d) == d
    then show (round d)
    else show d
  _ -> unexpected "string, number, or boolean" $ show v

showQname :: AvroQualifiedName -> String
showQname (AvroQualifiedName mns local) = (Y.maybe "" (\ns -> ns ++ ".") mns) ++ local

stringToTerm :: Show a => Type a -> String -> Flow s (Term a)
stringToTerm typ s = case stripType typ of
    TypeLiteral lt -> TermLiteral <$> case lt of
      LiteralTypeBoolean -> LiteralBoolean <$> doRead s
      LiteralTypeInteger it -> LiteralInteger <$> case it of
        IntegerTypeBigint -> IntegerValueBigint <$> doRead s
        IntegerTypeInt8 -> IntegerValueInt8 <$> doRead s
        IntegerTypeInt16 -> IntegerValueInt16 <$> doRead s
        IntegerTypeInt32 -> IntegerValueInt32 <$> doRead s
        IntegerTypeInt64 -> IntegerValueInt64 <$> doRead s
        IntegerTypeUint8 -> IntegerValueUint8 <$> doRead s
        IntegerTypeUint16 -> IntegerValueUint16 <$> doRead s
        IntegerTypeUint32 -> IntegerValueUint32 <$> doRead s
        IntegerTypeUint64 -> IntegerValueUint64 <$> doRead s
      LiteralTypeString -> LiteralString <$> pure s
      _ -> unexpected "literal type" $ show lt
  where
    doRead s = case TR.readEither s of
      Left msg -> fail $ "failed to read value: " ++ msg
      Right term -> pure term

termToString :: Show a => Term a -> Flow s String
termToString term = case stripTerm term of
  TermLiteral l -> case l of
    LiteralBoolean b -> pure $ show b
    LiteralInteger iv -> pure $ case iv of
      IntegerValueBigint i -> show i
      IntegerValueInt8 i -> show i
      IntegerValueInt16 i -> show i
      IntegerValueInt32 i -> show i
      IntegerValueInt64 i -> show i
      IntegerValueUint8 i -> show i
      IntegerValueUint16 i -> show i
      IntegerValueUint32 i -> show i
      IntegerValueUint64 i -> show i
    LiteralString s -> pure s
    _ -> unexpected "boolean, integer, or string" $ show l
  TermOptional (Just term') -> termToString term'
  _ -> unexpected "literal value" $ show term
