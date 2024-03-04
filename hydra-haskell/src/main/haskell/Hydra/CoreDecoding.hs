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
  ) where

import Hydra.Strip
import Hydra.Compute
import Hydra.Core
import Hydra.Graph
import Hydra.Lexical
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


--coreDecodeApplicationType :: Term -> Flow Graph ApplicationType
--coreDecodeApplicationType = matchRecord $ \m -> ApplicationType
--  <$> getField m _ApplicationType_function coreDecodeType
--  <*> getField m _ApplicationType_argument coreDecodeType
coreDecodeApplicationType :: Application -> Flow Graph ApplicationType
coreDecodeApplicationType (Application lhs rhs) = ApplicationType <$> coreDecodeType lhs <*> coreDecodeType rhs

coreDecodeFieldName :: Term -> Flow Graph FieldName
coreDecodeFieldName term = FieldName <$> (Expect.wrap _FieldName term >>= Expect.string)

coreDecodeFieldType :: Term -> Flow Graph FieldType
coreDecodeFieldType = matchRecord $ \m -> FieldType
  <$> getField m _FieldType_name coreDecodeFieldName
  <*> getField m _FieldType_type coreDecodeType

coreDecodeFieldTypes :: Term -> Flow Graph [FieldType]
coreDecodeFieldTypes term = case stripTerm term of
  TermList els -> CM.mapM coreDecodeFieldType els
  _ -> unexpected "list" $ show term

coreDecodeFloatType :: Term -> Flow Graph FloatType
coreDecodeFloatType = matchEnum _FloatType [
  (_FloatType_bigfloat, FloatTypeBigfloat),
  (_FloatType_float32, FloatTypeFloat32),
  (_FloatType_float64, FloatTypeFloat64)]

coreDecodeFunctionType :: Term -> Flow Graph FunctionType
coreDecodeFunctionType = matchRecord $ \m -> FunctionType
  <$> getField m _FunctionType_domain coreDecodeType
  <*> getField m _FunctionType_codomain coreDecodeType

coreDecodeIntegerType :: Term -> Flow Graph IntegerType
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

coreDecodeLambdaType :: Term -> Flow Graph LambdaType
coreDecodeLambdaType = matchRecord $ \m -> LambdaType
  <$> (getField m _LambdaType_parameter coreDecodeName)
  <*> getField m _LambdaType_body coreDecodeType

coreDecodeLiteralType :: Term -> Flow Graph LiteralType
coreDecodeLiteralType = matchUnion _LiteralType [
  matchUnitField _LiteralType_binary LiteralTypeBinary,
  matchUnitField _LiteralType_boolean LiteralTypeBoolean,
  (_LiteralType_float, fmap LiteralTypeFloat . coreDecodeFloatType),
  (_LiteralType_integer, fmap LiteralTypeInteger . coreDecodeIntegerType),
  matchUnitField _LiteralType_string LiteralTypeString]

coreDecodeMapType :: Term -> Flow Graph MapType
coreDecodeMapType = matchRecord $ \m -> MapType
  <$> getField m _MapType_keys coreDecodeType
  <*> getField m _MapType_values coreDecodeType

coreDecodeName :: Term -> Flow Graph Name
coreDecodeName term = Name <$> (Expect.wrap _Name term >>= Expect.string)

coreDecodeNominal :: (Term -> Flow Graph a) -> Term -> Flow Graph (Nominal a)
coreDecodeNominal mapping term = do
  fields <- Expect.recordWithName _Nominal term
  name <- Expect.field _Nominal_typeName coreDecodeName fields
  obj <- Expect.field _Nominal_object mapping fields
  pure $ Nominal name obj

coreDecodeRowType :: Term -> Flow Graph RowType
coreDecodeRowType = matchRecord $ \m -> RowType
  <$> getField m _RowType_typeName coreDecodeName
  <*> getField m _RowType_extends (Expect.optional coreDecodeName)
  <*> getField m _RowType_fields coreDecodeFieldTypes

coreDecodeString :: Term -> Flow Graph String
coreDecodeString = Expect.string . stripTerm

coreDecodeType :: Term -> Flow Graph Type
coreDecodeType dat = case dat of
  TermAnnotated (Annotated term ann) -> (\t -> TypeAnnotated $ Annotated t ann) <$> coreDecodeType term
  TermApplication app -> TypeApplication <$> coreDecodeApplicationType app
  TermFunction (FunctionLambda (Lambda v _ body)) -> TypeLambda <$> (LambdaType <$> pure v <*> coreDecodeType body)
  TermTyped (TypedTerm _ term) -> coreDecodeType term
  TermVariable name -> pure $ TypeVariable name
  _ -> matchUnion _Type [
--    (_Type_annotated, fmap TypeAnnotated . coreDecodeAnnotated),
--    (_Type_application, fmap TypeApplication . coreDecodeApplicationType),
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
--    (_Type_variable, fmap TypeVariable . coreDecodeName),
--    (_Type_variable, fmap TypeVariable . Expect.variable),
    (_Type_wrap, fmap TypeWrap . (coreDecodeNominal coreDecodeType))] dat

getField :: M.Map FieldName Term -> FieldName -> (Term -> Flow Graph b) -> Flow Graph b
getField m fname decode = case M.lookup fname m of
  Nothing -> fail $ "expected field " ++ show fname ++ " not found"
  Just val -> decode val

matchEnum :: Name -> [(FieldName, a)] -> Term -> Flow Graph a
matchEnum tname = matchUnion tname . fmap (uncurry matchUnitField)

matchRecord :: (M.Map FieldName Term -> Flow Graph a) -> Term -> Flow Graph a
matchRecord decode term = case stripTerm term of
  TermRecord (Record _ fields) -> decode $ M.fromList $ fmap (\(Field fname val) -> (fname, val)) fields
  _ -> unexpected "record" $ show term

matchUnion :: Name -> [(FieldName, Term -> Flow Graph a)] -> Term -> Flow Graph a
matchUnion tname pairs term = case stripTerm term of
    TermVariable name -> do
      el <- requireElement name
      matchUnion tname pairs (elementData el)
    TermUnion (Injection tname' (Field fname val)) -> if tname' == tname
      then case M.lookup fname mapping of
        Nothing -> fail $ "no matching case for field " ++ show fname
        Just f -> f val
      else unexpected ("injection for type " ++ show tname) $ show term
    t -> unexpected ("union of type " ++ unName tname
      ++ " with one of {" ++ L.intercalate ", " (unFieldName . fst <$> pairs) ++ "}") $ show t
  where
    mapping = M.fromList pairs

matchUnitField :: FieldName -> b -> (FieldName, a -> Flow Graph b)
matchUnitField fname x = (fname, \_ -> pure x)
