module Hydra.Langs.Protobuf.Coder (moduleToProtobuf) where

import Hydra.Kernel
import Hydra.Langs.Protobuf.Language
import qualified Hydra.Langs.Protobuf.Proto3 as P3
import qualified Hydra.Lib.Strings as Strings
import Hydra.Langs.Protobuf.Language
import Hydra.Langs.Protobuf.Serde
import Hydra.Tools.Serialization
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


moduleToProtobuf :: (Ord a, Read a, Show a) => Module a -> Flow (Graph a) (M.Map FilePath String)
moduleToProtobuf mod = do
    files <- transformModule protobufLanguage encodeTerm constructModule mod
    return $ M.fromList (mapPair <$> M.toList files)
  where
    mapPair (path, sf) = (path, printExpr $ parenthesize $ writeProtoFile sf)
    encodeTerm _ = fail "term-level encoding it not yet supported"

--

checkIsStringType :: Show a => Type a -> Flow (Graph a) ()
checkIsStringType typ = case simplifyType typ of
  TypeLiteral lt -> case lt of
    LiteralTypeString -> pure ()
    _ -> unexpected "string type" $ show lt
  TypeVariable name -> requireType name >>= checkIsStringType
  _ -> unexpected "literal (string) type" $ show typ

constructModule :: (Ord a, Read a, Show a)
  => Module a
  -> M.Map (Type a) (Coder (Graph a) (Graph a) (Term a) ())
  -> [(Element a, TypedTerm a)]
  -> Flow (Graph a) (M.Map FilePath P3.ProtoFile)
constructModule mod@(Module ns els _ desc) _ pairs = do
    schemaImports <- (fmap namespaceToFileReference . S.toList) <$> moduleDependencyNamespaces True False False False mod
    types <- CM.mapM toType pairs
    definitions <- CM.mapM toDef types
    let pfile = P3.ProtoFile {
      P3.protoFilePackage = namespaceToPackageName ns,
      P3.protoFileImports = schemaImports ++ (defaultImports $ snd <$> types),
      P3.protoFileTypes = definitions,
      P3.protoFileOptions = []}
    return $ M.singleton path pfile
  where
    path = P3.unFileReference $ namespaceToFileReference ns
    toType (el, (TypedTerm typ term)) = do
      if isType typ
        then do
          t <- coreDecodeType term
          return (el, t)
        else fail $ "mapping of non-type elements to PDL is not yet supported: " ++ unName (elementName el)
    toDef (el, typ) = adaptAndEncodeType protobufLanguage (encodeDefinition ns (elementName el)) $ flattenType typ
    defaultImports types = if L.foldl (||) False (hasWrappers <$> types)
        then [P3.FileReference "google/protobuf/wrappers.proto"]
        else []
      where
        hasWrappers = foldOverType TraversalOrderPre (\b t -> b || isWrapperType t) False
        isWrapperType typ = case typ of
          TypeRecord rt -> checkRowType rt
          TypeUnion rt -> checkRowType rt
          _ -> False
        checkRowType (RowType _ _ fields) = L.foldl (||) False (checkFieldType <$> fields)
        checkFieldType (FieldType _ typ) = case stripType typ of
          TypeOptional ot -> case stripType ot of
            TypeLiteral _ -> True
            _ -> False
          _ -> False

encodeDefinition :: (Eq a, Ord a, Show a) => Namespace -> Name -> Type a -> Flow (Graph a) P3.Definition
encodeDefinition localNs name typ = withTrace ("encoding " ++ unName name) $ do
    resetCount "proto_field_index"
    nextIndex
    options <- findOptions typ
    encode options typ
  where
    wrapAsRecordType t = TypeRecord $ RowType name Nothing [FieldType (FieldName "value") t]
    encode options typ = case simplifyType typ of
      TypeRecord rt -> P3.DefinitionMessage <$> encodeRecordType localNs options rt
      TypeUnion rt -> if isEnumDefinition typ
        then P3.DefinitionEnum <$> encodeEnumDefinition options rt
        else encode options $ wrapAsRecordType $ TypeUnion rt
      t -> encode options $ wrapAsRecordType t

encodeEnumDefinition :: [P3.Option] -> RowType a -> Flow (Graph a) P3.EnumDefinition
encodeEnumDefinition options (RowType tname _ fields) = do
    values <- CM.zipWithM encodeEnumField fields [1..]
    return $ P3.EnumDefinition {
      P3.enumDefinitionName = encodeTypeName tname,
      P3.enumDefinitionValues = unknownField:values,
      P3.enumDefinitionOptions = options}
  where
    unknownField = P3.EnumValue {
      P3.enumValueName = encodeEnumValueName tname $ FieldName "unknown",
      P3.enumValueNumber = 0,
      P3.enumValueOptions = []}
    encodeEnumField (FieldType fname ftype) idx = do
      opts <- findOptions ftype
      return $ P3.EnumValue {
        P3.enumValueName = encodeEnumValueName tname fname,
        P3.enumValueNumber = idx,
        P3.enumValueOptions = opts}

encodeEnumValueName :: Name -> FieldName -> P3.EnumValueName
encodeEnumValueName tname fname = P3.EnumValueName (prefix ++ "_" ++ suffix)
  where
    prefix = localNameOfEager tname
    suffix = convertCase CaseConventionCamel CaseConventionUpperSnake $ unFieldName fname

encodeFieldName :: FieldName -> P3.FieldName
encodeFieldName = P3.FieldName . convertCase CaseConventionCamel CaseConventionLowerSnake . unFieldName

encodeFieldType :: (Ord a, Show a) => Namespace -> FieldType a -> Flow (Graph a) P3.Field
encodeFieldType localNs (FieldType fname ftype) = withTrace ("encode field " ++ show (unFieldName fname)) $ do
    options <- findOptions ftype
    ft <- encodeType ftype
    idx <- nextIndex
    return $ P3.Field {
      P3.fieldName = encodeFieldName fname,
      P3.fieldJsonName = Nothing,
      P3.fieldType = ft,
      P3.fieldNumber = idx,
      P3.fieldOptions = options}
  where
    encodeType typ = case simplifyType typ of
      TypeList lt -> do
        P3.FieldTypeRepeated <$> encodeSimpleType lt
      TypeMap (MapType kt vt) -> do
--        checkIsStringType kt
        P3.FieldTypeMap <$> encodeSimpleType vt
      TypeOptional ot -> case stripType ot of
        TypeLiteral lt -> P3.FieldTypeSimple <$> encodeScalarTypeWrapped lt
        _ -> encodeType ot -- TODO
      TypeUnion (RowType _ _ fields) -> do
        pfields <- CM.mapM (encodeFieldType localNs) fields
        return $ P3.FieldTypeOneof pfields
      _ -> do
        P3.FieldTypeSimple <$> encodeSimpleType typ
    encodeSimpleType typ = case simplifyType typ of
      TypeLiteral lt -> P3.SimpleTypeScalar <$> encodeScalarType lt
      TypeRecord (RowType name _ _) -> forNominal name
      TypeUnion (RowType name _ _) -> forNominal name
      TypeVariable name -> forNominal name
      t -> unexpected "simple type" $ show $ removeTypeAnnotations t
      where
        forNominal name = pure $ P3.SimpleTypeReference $ encodeTypeReference localNs name

encodeRecordType :: (Ord a, Show a) => Namespace -> [P3.Option] -> RowType a -> Flow (Graph a) P3.MessageDefinition
encodeRecordType localNs options (RowType tname _ fields) = do
    pfields <- CM.mapM (encodeFieldType localNs) fields
    return P3.MessageDefinition {
      P3.messageDefinitionName = encodeTypeName tname,
      P3.messageDefinitionFields = pfields,
      P3.messageDefinitionOptions = options}

encodeScalarType :: LiteralType -> Flow s P3.ScalarType
encodeScalarType lt = case lt of
  LiteralTypeBinary -> return P3.ScalarTypeBytes
  LiteralTypeBoolean -> return P3.ScalarTypeBool
  LiteralTypeFloat ft -> case ft of
    FloatTypeFloat32 -> return P3.ScalarTypeFloat
    FloatTypeFloat64 -> return P3.ScalarTypeDouble
    _ -> unexpected "32-bit or 64-bit floating-point type" $ show ft
  LiteralTypeInteger it -> case it of
    IntegerTypeInt32 -> return P3.ScalarTypeInt32
    IntegerTypeInt64 -> return P3.ScalarTypeInt64
    IntegerTypeUint32 -> return P3.ScalarTypeUint32
    IntegerTypeUint64 -> return P3.ScalarTypeUint64
    _ -> unexpected "32-bit or 64-bit integer type" $ show it
  LiteralTypeString -> return P3.ScalarTypeString

encodeScalarTypeWrapped :: LiteralType -> Flow s P3.SimpleType
encodeScalarTypeWrapped lt = toType <$> case lt of
    LiteralTypeBinary -> return "Bytes"
    LiteralTypeBoolean -> return "Bool"
    LiteralTypeFloat ft -> case ft of
      FloatTypeFloat32 -> return "Float"
      FloatTypeFloat64 -> return "Double"
      _ -> unexpected "32-bit or 64-bit floating-point type" $ show ft
    LiteralTypeInteger it -> case it of
      IntegerTypeInt32 -> return "Int32"
      IntegerTypeInt64 -> return "Int64"
      IntegerTypeUint32 -> return "UInt32"
      IntegerTypeUint64 -> return "UInt64"
      _ -> unexpected "32-bit or 64-bit integer type" $ show it
    LiteralTypeString -> return "String"
  where
    toType label = P3.SimpleTypeReference $ P3.TypeName $ "google.protobuf." ++ label ++ "Value"

encodeTypeName :: Name -> P3.TypeName
encodeTypeName = P3.TypeName . localNameOfEager

encodeTypeReference :: Namespace -> Name -> P3.TypeName
encodeTypeReference localNs name = P3.TypeName $ if ns == Just localNs
    then local
    else case ns of
      Nothing -> local
      Just (Namespace n) -> L.last (Strings.splitOn "/" n) ++ "." ++ local
  where
    QualifiedName ns local = qualifyNameEager name

-- Eliminate type lambdas and type applications, simply replacing type variables with the string type
flattenType :: Ord a => Type a -> Type a
flattenType = rewriteType f id
  where
   f recurse typ = case typ of
     TypeLambda (LambdaType v body) -> recurse $ replaceFreeName v Types.string body
     TypeApplication (ApplicationType lhs _) -> recurse lhs
     _ -> recurse typ

findOptions :: Type a -> Flow (Graph a) [P3.Option]
findOptions typ = do
  anns <- graphAnnotations <$> getState
  mdesc <- annotationClassTypeDescription anns typ
  return $ case mdesc of
    Nothing -> []
    Just desc -> [P3.Option descriptionOptionName desc]

isEnumFields :: Eq a => [FieldType a] -> Bool
isEnumFields fields = L.foldl (&&) True $ fmap isEnumField fields
  where
    isEnumField = isUnitType . simplifyType . fieldTypeType

isEnumDefinition :: Eq a => Type a -> Bool
isEnumDefinition typ = case simplifyType typ of
  TypeUnion (RowType _ _ fields) -> isEnumFields fields
  _ -> False

isEnumDefinitionReference :: (Eq a, Show a) => Name -> Flow (Graph a) Bool
isEnumDefinitionReference name = isEnumDefinition <$> ((elementData <$> requireElement name) >>= coreDecodeType)

namespaceToFileReference :: Namespace -> P3.FileReference
namespaceToFileReference (Namespace ns) = P3.FileReference $ ns ++ ".proto"

namespaceToPackageName :: Namespace -> P3.PackageName
namespaceToPackageName (Namespace ns) = P3.PackageName $ Strings.intercalate "." $ Strings.splitOn "/" ns

nextIndex :: Flow s Int
nextIndex = nextCount "proto_field_index"

-- Note: this should probably be done in the term adapters
simplifyType :: Type a -> Type a
simplifyType typ = case stripType typ of
  TypeWrap (Nominal _ t) -> simplifyType t
  t -> t
