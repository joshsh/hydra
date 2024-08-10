module Hydra.Langs.Protobuf.Coder (moduleToProtobuf) where

import Hydra.Kernel
import Hydra.Langs.Protobuf.Language
import qualified Hydra.Langs.Protobuf.Proto3 as P3
import qualified Hydra.Lib.Strings as Strings
import Hydra.Langs.Protobuf.Language
import Hydra.Langs.Protobuf.Serde
import Hydra.Tools.Serialization
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.Annotations

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.Read as TR
import qualified Data.Maybe as Y

-- | Note: follows the Protobuf Style Guide (https://protobuf.dev/programming-guides/style)
moduleToProtobuf :: Module -> Flow (Graph) (M.Map FilePath String)
moduleToProtobuf mod = do
    files <- transformModule protobufLanguage encodeTerm constructModule mod
    return $ M.fromList (mapPair <$> M.toList files)
  where
    mapPair (path, sf) = (path, printExpr $ parenthesize $ writeProtoFile sf)
    encodeTerm _ = fail "term-level encoding is not yet supported"

--

javaMultipleFilesOptionName = "java_multiple_files"
javaPackageOptionName = "java_package"

checkIsStringType :: Type -> Flow (Graph) ()
checkIsStringType typ = case simplifyType typ of
  TypeLiteral lt -> case lt of
    LiteralTypeString -> pure ()
    _ -> unexpected "string type" $ show lt
  TypeVariable name -> requireType name >>= checkIsStringType
  _ -> unexpected "literal (string) type" $ show typ

constructModule :: Module
  -> M.Map (Type) (Coder (Graph) (Graph) (Term) ())
  -> [(Element, TypedTerm)]
  -> Flow (Graph) (M.Map FilePath P3.ProtoFile)
constructModule mod@(Module ns els _ _ desc) _ pairs = do
    schemaImports <- (fmap namespaceToFileReference . S.toList) <$> moduleDependencyNamespaces True False False False mod
    types <- CM.mapM toType pairs
    definitions <- CM.mapM toDef types
    let pfile = P3.ProtoFile {
      P3.protoFilePackage = namespaceToPackageName ns,
      P3.protoFileImports = schemaImports ++ (wrapperImport $ snd <$> types) ++ (emptyImport $ snd <$> types),
      P3.protoFileTypes = definitions,
      P3.protoFileOptions = descOption:javaOptions}
    return $ M.singleton path pfile
  where
    javaOptions = [
      P3.Option javaMultipleFilesOptionName $ P3.ValueBoolean True,
      P3.Option javaPackageOptionName $ P3.ValueString $ P3.unPackageName $ namespaceToPackageName ns]
    descOption = P3.Option descriptionOptionName $ P3.ValueString $
      (Y.maybe "" (\d -> d ++ "\n\n") desc) ++ warningAutoGeneratedFile
    path = P3.unFileReference $ namespaceToFileReference ns
    toType (el, (TypedTerm term typ)) = do
      if isType typ
        then do
          t <- coreDecodeType term
          return (el, t)
        else fail $ "mapping of non-type elements to PDL is not yet supported: " ++ unName (elementName el)
    toDef (el, typ) = adaptAndEncodeType protobufLanguage (encodeDefinition ns (elementName el)) $ flattenType typ
    checkFields checkType checkFieldType types = L.foldl (||) False (hasMatches <$> types)
      where
        hasMatches = foldOverType TraversalOrderPre (\b t -> b || hasMatch t) False
        hasMatch typ = case checkType typ of
          Just b -> b
          Nothing -> case typ of
            TypeRecord rt -> checkRowType rt
            TypeUnion rt -> checkRowType rt
            _ -> False
        checkRowType (RowType _ fields) = L.foldl (||) False (checkField <$> fields)
        checkField (FieldType _ typ) = checkFieldType $ stripType typ
    wrapperImport types = if checkFields (const Nothing) isOptionalScalarField types
        then [P3.FileReference "google/protobuf/wrappers.proto"]
        else []
      where
        isOptionalScalarField typ = case typ of
          TypeOptional ot -> case stripType ot of
            TypeLiteral _ -> True
            _ -> False
          _ -> False
    emptyImport types = if checkFields checkType isUnitField types
        then [P3.FileReference "google/protobuf/empty.proto"]
        else []
      where
        checkType typ = if isEnumDefinition typ
          then Just False
          else Nothing
        isUnitField typ = case typ of
          TypeRecord (RowType name _) -> name == _Unit
          _ -> False

encodeDefinition :: Namespace -> Name -> Type -> Flow (Graph) P3.Definition
encodeDefinition localNs name typ = withTrace ("encoding " ++ unName name) $ do
    resetCount "proto_field_index"
    nextIndex
    options <- findOptions typ
    encode options typ
  where
    wrapAsRecordType t = TypeRecord $ RowType name [FieldType (Name "value") t]
    encode options typ = case simplifyType typ of
      TypeRecord rt -> P3.DefinitionMessage <$> encodeRecordType localNs options rt
      TypeUnion rt -> if isEnumDefinition typ
        then P3.DefinitionEnum <$> encodeEnumDefinition options rt
        else encode options $ wrapAsRecordType $ TypeUnion rt
      t -> encode options $ wrapAsRecordType t

encodeEnumDefinition :: [P3.Option] -> RowType -> Flow (Graph) P3.EnumDefinition
encodeEnumDefinition options (RowType tname fields) = do
    values <- CM.zipWithM encodeEnumField fields [1..]
    return $ P3.EnumDefinition {
      P3.enumDefinitionName = encodeTypeName tname,
      P3.enumDefinitionValues = unspecifiedField:values,
      P3.enumDefinitionOptions = options}
  where
    unspecifiedField = P3.EnumValue {
      P3.enumValueName = encodeEnumValueName tname $ Name "unspecified",
      P3.enumValueNumber = 0,
      P3.enumValueOptions = []}
    encodeEnumField (FieldType fname ftype) idx = do
      opts <- findOptions ftype
      return $ P3.EnumValue {
        P3.enumValueName = encodeEnumValueName tname fname,
        P3.enumValueNumber = idx,
        P3.enumValueOptions = opts}

encodeEnumValueName :: Name -> Name -> P3.EnumValueName
encodeEnumValueName tname fname = P3.EnumValueName (prefix ++ "_" ++ suffix)
  where
    prefix = convertCaseCamelToUpperSnake $ localNameOfEager tname
    suffix = convertCaseCamelToUpperSnake $ unName fname

encodeFieldName :: Bool -> Name -> P3.FieldName
encodeFieldName preserve = P3.FieldName . toPname . unName
  where
    toPname = if preserve
      then id
      else convertCaseCamelToLowerSnake

encodeFieldType :: Namespace -> FieldType -> Flow (Graph) P3.Field
encodeFieldType localNs (FieldType fname ftype) = withTrace ("encode field " ++ show (unName fname)) $ do
    options <- findOptions ftype
    ft <- encodeType ftype
    idx <- nextIndex
    preserve <- readBooleanAnnotation key_preserveFieldName ftype
    return $ P3.Field {
      P3.fieldName = encodeFieldName preserve fname,
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
      TypeUnion (RowType _ fields) -> do
        pfields <- CM.mapM (encodeFieldType localNs) fields
        return $ P3.FieldTypeOneof pfields
      _ -> do
        P3.FieldTypeSimple <$> encodeSimpleType typ
    encodeSimpleType typ = case simplifyType typ of
      TypeLiteral lt -> P3.SimpleTypeScalar <$> encodeScalarType lt
      TypeRecord (RowType name _) -> if name == _Unit
        then pure $ P3.SimpleTypeReference $ P3.TypeName $ "google.protobuf.Empty"
        else forNominal name
      TypeUnion (RowType name _) -> forNominal name
      TypeVariable name -> forNominal name
      t -> unexpected "simple type" $ show $ removeTypeAnnotations t
      where
        forNominal name = pure $ P3.SimpleTypeReference $ encodeTypeReference localNs name

encodeRecordType :: Namespace -> [P3.Option] -> RowType -> Flow (Graph) P3.MessageDefinition
encodeRecordType localNs options (RowType tname fields) = do
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
encodeTypeReference localNs name = P3.TypeName $ if nsParts == Just localNsParts
    then local
    else case nsParts of
      Nothing -> local
      Just parts -> L.intercalate "." (parts ++ [local])
  where
    QualifiedName ns local = qualifyNameEager name
    nsParts = fmap (\n -> L.init $ Strings.splitOn "/" $ unNamespace n) ns
    localNsParts = L.init $ Strings.splitOn "/" $ unNamespace localNs

-- Eliminate type lambdas and type applications, simply replacing type variables with the string type
flattenType :: Type -> Type
flattenType = rewriteType f
  where
   f recurse typ = case typ of
     TypeLambda (LambdaType v body) -> recurse $ replaceFreeName v Types.string body
     TypeApplication (ApplicationType lhs _) -> recurse lhs
     _ -> recurse typ

findOptions :: Type -> Flow (Graph) [P3.Option]
findOptions typ = do
  mdesc <- getTypeDescription typ
  bdep <- readBooleanAnnotation key_deprecated typ
  let mdescAnn = fmap (\desc -> P3.Option descriptionOptionName $ P3.ValueString desc) mdesc
  let mdepAnn = if bdep then Just (P3.Option deprecatedOptionName $ P3.ValueBoolean True) else Nothing
  return $ Y.catMaybes [mdescAnn, mdepAnn]

isEnumFields :: [FieldType] -> Bool
isEnumFields fields = L.foldl (&&) True $ fmap isEnumField fields
  where
    isEnumField = isUnitType . simplifyType . fieldTypeType

isEnumDefinition :: Type -> Bool
isEnumDefinition typ = case simplifyType typ of
  TypeUnion (RowType _ fields) -> isEnumFields fields
  _ -> False

isEnumDefinitionReference :: Name -> Flow (Graph) Bool
isEnumDefinitionReference name = isEnumDefinition <$> ((elementData <$> requireElement name) >>= coreDecodeType)

namespaceToFileReference :: Namespace -> P3.FileReference
namespaceToFileReference (Namespace ns) = P3.FileReference $ pns ++ ".proto"
  where
    pns = Strings.intercalate "/" (convertCaseCamelToLowerSnake <$> (Strings.splitOn "/" ns))

namespaceToPackageName :: Namespace -> P3.PackageName
namespaceToPackageName (Namespace ns) = P3.PackageName $ Strings.intercalate "." $
  convertCaseCamelToLowerSnake <$> (L.init $ Strings.splitOn "/" ns)

nextIndex :: Flow s Int
nextIndex = nextCount "proto_field_index"

readBooleanAnnotation :: String -> Type -> Flow (Graph) Bool
readBooleanAnnotation key typ = do
  let ann = typeAnnotationInternal typ
  case TR.readMaybe $ show ann of
    Just kv -> case getAnnotation key kv of
      Just _ -> return True
      Nothing -> return False
    Nothing -> return False

-- Note: this should probably be done in the term adapters
simplifyType :: Type -> Type
simplifyType typ = case stripType typ of
  TypeWrap (WrappedType _ t) -> simplifyType t
  t -> t
