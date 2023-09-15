-- | Decoding of encoded types (as terms) back to types according to LambdaGraph's epsilon encoding

module Hydra.CoreDecoding (
  coreDecodeFieldType,
  coreDecodeFieldTypes,
  coreDecodeFloatType,
  coreDecodeFunctionType,
  coreDecodeIntegerType,
  coreDecodeLambdaType,
  coreDecodeLiteralType,
  coreDecodeMapType,
  coreDecodeName,
  coreDecodeRowType,
  coreDecodeString,
  coreDecodeType,
  dereferenceType,
  elementAsTypedTerm,
  fieldTypes,
  isSerializable,
  moduleDependencyNamespaces,
  requireRecordType,
  requireType,
  requireUnionType,
  requireWrappedType,
  resolveType,
  typeDependencies,
  typeDependencyNames,
  ) where

import Hydra.Basics
import Hydra.Strip
import Hydra.Coders
import Hydra.Compute
import Hydra.Core
import Hydra.Graph
import Hydra.Mantle
import Hydra.Module
import Hydra.Lexical
import Hydra.Rewriting
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


coreDecodeApplicationType :: Term -> Flow (Graph Kv) (ApplicationType Kv)
coreDecodeApplicationType = matchRecord $ \m -> ApplicationType
  <$> getField m _ApplicationType_function coreDecodeType
  <*> getField m _ApplicationType_argument coreDecodeType

coreDecodeFieldName :: Term -> Flow (Graph Kv) FieldName
coreDecodeFieldName term = FieldName <$> (Expect.wrap _FieldName term >>= Expect.string)

coreDecodeFieldType :: Term -> Flow (Graph Kv) (FieldType Kv)
coreDecodeFieldType = matchRecord $ \m -> FieldType
  <$> getField m _FieldType_name coreDecodeFieldName
  <*> getField m _FieldType_type coreDecodeType

coreDecodeFieldTypes :: Term -> Flow (Graph Kv) [FieldType Kv]
coreDecodeFieldTypes term = case stripTerm term of
  TermList els -> CM.mapM coreDecodeFieldType els
  _ -> unexpected "list" $ show term

coreDecodeFloatType :: Term -> Flow (Graph Kv) FloatType
coreDecodeFloatType = matchEnum _FloatType [
  (_FloatType_bigfloat, FloatTypeBigfloat),
  (_FloatType_float32, FloatTypeFloat32),
  (_FloatType_float64, FloatTypeFloat64)]

coreDecodeFunctionType :: Term -> Flow (Graph Kv) (FunctionType Kv)
coreDecodeFunctionType = matchRecord $ \m -> FunctionType
  <$> getField m _FunctionType_domain coreDecodeType
  <*> getField m _FunctionType_codomain coreDecodeType

coreDecodeIntegerType :: Term -> Flow (Graph Kv) IntegerType
coreDecodeIntegerType = matchEnum _IntegerType [
  (_IntegerType_bigint, IntegerTypeBigint),
  (_IntegerType_int8, IntegerTypeInt8),
  (_IntegerType_int16, IntegerTypeInt16),
  (_IntegerType_int32, IntegerTypeInt32),
  (_IntegerType_int64, IntegerTypeInt64),
  (_IntegerType_uint8, IntegerTypeUint8),
  (_IntegerType_uint16, IntegerTypeUint16),
  (_IntegerType_uint32, IntegerTypeUint32),
  (_IntegerType_uint64, IntegerTypeUint64)]

coreDecodeLambdaType :: Term -> Flow (Graph Kv) (LambdaType Kv)
coreDecodeLambdaType = matchRecord $ \m -> LambdaType
  <$> (getField m _LambdaType_parameter coreDecodeName)
  <*> getField m _LambdaType_body coreDecodeType

coreDecodeLiteralType :: Term -> Flow (Graph Kv) LiteralType
coreDecodeLiteralType = matchUnion _LiteralType [
  matchUnitField _LiteralType_binary LiteralTypeBinary,
  matchUnitField _LiteralType_boolean LiteralTypeBoolean,
  (_LiteralType_float, fmap LiteralTypeFloat . coreDecodeFloatType),
  (_LiteralType_integer, fmap LiteralTypeInteger . coreDecodeIntegerType),
  matchUnitField _LiteralType_string LiteralTypeString]

coreDecodeMapType :: Term -> Flow (Graph Kv) (MapType Kv)
coreDecodeMapType = matchRecord $ \m -> MapType
  <$> getField m _MapType_keys coreDecodeType
  <*> getField m _MapType_values coreDecodeType

coreDecodeName :: Term -> Flow (Graph Kv) Name
coreDecodeName term = Name <$> (Expect.wrap _Name term >>= Expect.string)

coreDecodeNominal :: (Term -> Flow (Graph Kv) x) -> Term -> Flow (Graph Kv) (Nominal x)
coreDecodeNominal mapping term = do
  fields <- Expect.recordWithName _Nominal term
  name <- Expect.field _Nominal_typeName coreDecodeName fields
  obj <- Expect.field _Nominal_object mapping fields
  pure $ Nominal name obj

coreDecodeRowType :: Term -> Flow (Graph Kv) (RowType Kv)
coreDecodeRowType = matchRecord $ \m -> RowType
  <$> getField m _RowType_typeName coreDecodeName
  <*> getField m _RowType_extends (Expect.optional coreDecodeName)
  <*> getField m _RowType_fields coreDecodeFieldTypes

coreDecodeString :: Term -> Flow (Graph Kv) String
coreDecodeString = Expect.string . stripTerm

coreDecodeType :: Term -> Flow (Graph Kv) (Type Kv)
coreDecodeType dat = case dat of
  TermAnnotated (Annotated term ann) -> (\t -> TypeAnnotated $ Annotated t ann) <$> coreDecodeType term
  _ -> matchUnion _Type [
--    (_Type_annotated, fmap TypeAnnotated . coreDecodeAnnotated),
    (_Type_application, fmap TypeApplication . coreDecodeApplicationType),
    (_Type_function, fmap TypeFunction . coreDecodeFunctionType),
    (_Type_lambda, fmap TypeLambda . coreDecodeLambdaType),
    (_Type_list, fmap TypeList . coreDecodeType),
    (_Type_literal, fmap TypeLiteral . coreDecodeLiteralType),
    (_Type_map, fmap TypeMap . coreDecodeMapType),
    (_Type_optional, fmap TypeOptional . coreDecodeType),
    (_Type_product, \l -> do
      types <- Expect.list pure l
      TypeProduct <$> (CM.mapM coreDecodeType types)),
    (_Type_record, fmap TypeRecord . coreDecodeRowType),
    (_Type_set, fmap TypeSet . coreDecodeType),
    (_Type_sum, \(TermList types) -> TypeSum <$> (CM.mapM coreDecodeType types)),
    (_Type_union, fmap TypeUnion . coreDecodeRowType),
    (_Type_variable, fmap TypeVariable . coreDecodeName),
    (_Type_wrap, fmap TypeWrap . (coreDecodeNominal coreDecodeType))] dat

dereferenceType :: Name -> Flow (Graph Kv) (Maybe (Type Kv))
dereferenceType name = do
  mel <- dereferenceElement name
  case mel of
    Nothing -> return Nothing
    Just el -> Just <$> coreDecodeType (elementData el)

elementAsTypedTerm :: Element Kv -> Flow (Graph Kv) (TypedTerm)
elementAsTypedTerm el = do
  typ <- requireTermType (elementData el)
  return $ TypedTerm typ (elementData el)

fieldTypes :: Type Kv -> Flow (Graph Kv) (M.Map FieldName (Type Kv))
fieldTypes t = case stripType t of
    TypeLambda (LambdaType _ body) -> fieldTypes body
    TypeRecord rt -> pure $ toMap $ rowTypeFields rt
    TypeUnion rt -> pure $ toMap $ rowTypeFields rt
    TypeVariable name -> do
      withTrace ("field types of " ++ unName name) $ do
        el <- requireElement name
        coreDecodeType (elementData el) >>= fieldTypes
    _ -> unexpected "record or union type" $ show t
  where
    toMap fields = M.fromList (toPair <$> fields)
    toPair (FieldType fname ftype) = (fname, ftype)

getField :: M.Map FieldName (Term) -> FieldName -> (Term -> Flow (Graph Kv) b) -> Flow (Graph Kv) b
getField m fname decode = case M.lookup fname m of
  Nothing -> fail $ "expected field " ++ show fname ++ " not found"
  Just val -> decode val

isSerializable :: Element Kv -> Flow (Graph Kv) Bool
isSerializable el = do
    deps <- typeDependencies (elementName el)
    let allVariants = S.fromList $ L.concat (variants <$> M.elems deps)
    return $ not $ S.member TypeVariantFunction allVariants
  where
    variants typ = typeVariant <$> foldOverType TraversalOrderPre (\m t -> t:m) [] typ

matchEnum :: Name -> [(FieldName, b)] -> Term -> Flow (Graph Kv) b
matchEnum tname = matchUnion tname . fmap (uncurry matchUnitField)

matchRecord :: (M.Map FieldName (Term) -> Flow (Graph Kv) b) -> Term -> Flow (Graph Kv) b
matchRecord decode term = case stripTerm term of
  TermRecord (Record _ fields) -> decode $ M.fromList $ fmap (\(Field fname val) -> (fname, val)) fields
  _ -> unexpected "record" $ show term

matchUnion :: Name -> [(FieldName, Term -> Flow (Graph Kv) b)] -> Term -> Flow (Graph Kv) b
matchUnion tname pairs term = case stripTerm term of
    TermVariable name -> do
      el <- requireElement name
      matchUnion tname pairs (elementData el)
    TermUnion (Injection tname' (Field fname val)) -> if tname' == tname
      then case M.lookup fname mapping of
        Nothing -> fail $ "no matching case for field " ++ show fname
        Just f -> f val
      else unexpected ("injection for type " ++ show tname) $ show term
    _ -> unexpected ("union with one of {" ++ L.intercalate ", " (unFieldName . fst <$> pairs) ++ "}") $ show term
  where
    mapping = M.fromList pairs

matchUnitField :: FieldName -> y -> (FieldName, x -> Flow (Graph Kv) y)
matchUnitField fname x = (fname, \_ -> pure x)

-- | Find dependency namespaces in various dimensions of a term: va
moduleDependencyNamespaces :: Bool -> Bool -> Bool -> Bool -> Module Kv -> Flow (Graph Kv) (S.Set Namespace)
moduleDependencyNamespaces withVars withPrims withNoms withSchema mod = do
    allNames <- S.unions <$> (CM.mapM elNames $ moduleElements mod)
    let namespaces = S.fromList $ Y.catMaybes (namespaceOfEager <$> S.toList allNames)
    return $ S.delete (moduleNamespace mod) namespaces
  where
    elNames el = do
      let term = elementData el
      let dataNames = termDependencyNames withVars withPrims withNoms term
      schemaNames <- if withSchema
        then typeDependencyNames <$> requireTermType term
        else pure S.empty

      typeNames <- if isEncodedType term
        then typeDependencyNames <$> coreDecodeType term
        else pure S.empty
      return $ S.unions [dataNames, schemaNames, typeNames]

requireRecordType :: Bool -> Name -> Flow (Graph Kv) (RowType Kv)
requireRecordType infer = requireRowType "record" infer $ \t -> case t of
  TypeRecord rt -> Just rt
  _ -> Nothing

requireRowType :: String -> Bool -> (Type Kv -> Maybe (RowType Kv)) -> Name -> Flow (Graph Kv) (RowType Kv)
requireRowType label infer getter name = do
  t <- withSchemaContext $ requireType name
  case getter (rawType t) of
    Just rt -> if infer
      then case rowTypeExtends rt of
        Nothing -> return rt
        Just name' -> do
          rt' <- requireRowType label True getter name'
          return $ RowType name Nothing (rowTypeFields rt' ++ rowTypeFields rt)
      else return rt
    Nothing -> fail $ show name ++ " does not resolve to a " ++ label ++ " type: " ++ show t
  where
    rawType t = case t of
      TypeAnnotated (Annotated t' _) -> rawType t'
      TypeLambda (LambdaType _ body) -> rawType body -- Note: throwing away quantification here
      _ -> t

requireType :: Name -> Flow (Graph Kv) (Type Kv)
requireType name = withTrace ("require type " ++ unName name) $ requireElement name >>= (coreDecodeType . elementData)

requireUnionType :: Bool -> Name -> Flow (Graph Kv) (RowType Kv)
requireUnionType infer = requireRowType "union" infer $ \t -> case t of
  TypeUnion rt -> Just rt
  _ -> Nothing

requireWrappedType :: Name -> Flow (Graph Kv) (Type Kv)
requireWrappedType name = do
  typ <- withSchemaContext $ requireType name
  case stripType typ of
    TypeWrap (Nominal name t) -> return t
    _ -> return typ -- TODO: stop allowing this "slop" once typedefs are clearly separated from newtypes
--     _ -> fail $ "expected wrapped type for " ++ unName name ++ " but got " ++ show typ

resolveType :: Type Kv -> Flow (Graph Kv) (Maybe (Type Kv))
resolveType typ = case stripType typ of
    TypeVariable name -> withSchemaContext $ do
      mterm <- resolveTerm name
      case mterm of
        Nothing -> pure Nothing
        Just t -> Just <$> coreDecodeType t
    _ -> pure $ Just typ

typeDependencies :: Name -> Flow (Graph Kv) (M.Map Name (Type Kv))
typeDependencies name = deps (S.fromList [name]) M.empty
  where
    deps seeds names = if S.null seeds
        then return names
        else do
          pairs <- CM.mapM toPair $ S.toList seeds
          let newNames = M.union names (M.fromList pairs)
          let refs = L.foldl S.union S.empty (typeDependencyNames <$> (snd <$> pairs))
          let visited = S.fromList $ M.keys names
          let newSeeds = S.difference refs visited
          deps newSeeds newNames
      where
        toPair name = do
          typ <- requireType name
          return (name, typ)

    requireType name = do
      withTrace ("type dependencies of " ++ unName name) $ do
        el <- requireElement name
        coreDecodeType (elementData el)
