-- | Mapping of hydra/core constructs in a host language like Haskell or Java  to their native Hydra counterparts as terms.  This includes an implementation of LambdaGraph's epsilon encoding (types to terms).

module Hydra.CoreEncoding where

import qualified Hydra.Core as Core
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Optionals as Optionals
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

coreEncodeAnnotatedTerm :: (Core.Annotated Core.Term -> Core.Term)
coreEncodeAnnotatedTerm a = (Core.TermAnnotated (Core.Annotated {
  Core.annotatedSubject = (coreEncodeTerm (Core.annotatedSubject a)),
  Core.annotatedAnnotation = (Core.annotatedAnnotation a)}))

coreEncodeAnnotatedType :: (Core.Annotated Core.Type -> Core.Term)
coreEncodeAnnotatedType at = (Core.TermAnnotated (Core.Annotated {
  Core.annotatedSubject = (coreEncodeType (Core.annotatedSubject at)),
  Core.annotatedAnnotation = (Core.annotatedAnnotation at)}))

coreEncodeApplication :: (Core.Application -> Core.Term)
coreEncodeApplication app = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Application"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "function"),
      Core.fieldTerm = (coreEncodeTerm (Core.applicationFunction app))},
    Core.Field {
      Core.fieldName = (Core.Name "argument"),
      Core.fieldTerm = (coreEncodeTerm (Core.applicationArgument app))}]}))

coreEncodeApplicationType :: (Core.ApplicationType -> Core.Term)
coreEncodeApplicationType at = (Core.TermApplication (Core.Application {
  Core.applicationFunction = (coreEncodeType (Core.applicationTypeFunction at)),
  Core.applicationArgument = (coreEncodeType (Core.applicationTypeArgument at))}))

coreEncodeCaseStatement :: (Core.CaseStatement -> Core.Term)
coreEncodeCaseStatement cs = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.CaseStatement"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.caseStatementTypeName cs))},
    Core.Field {
      Core.fieldName = (Core.Name "default"),
      Core.fieldTerm = (Core.TermOptional (Optionals.map coreEncodeTerm (Core.caseStatementDefault cs)))},
    Core.Field {
      Core.fieldName = (Core.Name "cases"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeField (Core.caseStatementCases cs)))}]}))

coreEncodeElimination :: (Core.Elimination -> Core.Term)
coreEncodeElimination x = case x of
  Core.EliminationList v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "list"),
      Core.fieldTerm = (coreEncodeTerm v)}}))
  Core.EliminationOptional v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "optional"),
      Core.fieldTerm = (coreEncodeOptionalCases v)}}))
  Core.EliminationProduct v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "product"),
      Core.fieldTerm = (coreEncodeTupleProjection v)}}))
  Core.EliminationRecord v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "record"),
      Core.fieldTerm = (coreEncodeProjection v)}}))
  Core.EliminationUnion v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "union"),
      Core.fieldTerm = (coreEncodeCaseStatement v)}}))
  Core.EliminationWrap v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Elimination"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "wrap"),
      Core.fieldTerm = (coreEncodeName v)}}))

coreEncodeField :: (Core.Field -> Core.Term)
coreEncodeField f = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Field"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "name"),
      Core.fieldTerm = (Core.TermWrap (Core.Nominal {
        Core.nominalTypeName = (Core.Name "hydra/core.Name"),
        Core.nominalObject = (Core.TermLiteral (Core.LiteralString (Core.unName (Core.fieldName f))))}))},
    Core.Field {
      Core.fieldName = (Core.Name "term"),
      Core.fieldTerm = (coreEncodeTerm (Core.fieldTerm f))}]}))

coreEncodeFieldType :: (Core.FieldType -> Core.Term)
coreEncodeFieldType ft = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.FieldType"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "name"),
      Core.fieldTerm = (coreEncodeName (Core.fieldTypeName ft))},
    Core.Field {
      Core.fieldName = (Core.Name "type"),
      Core.fieldTerm = (coreEncodeType (Core.fieldTypeType ft))}]}))

coreEncodeFloatType :: (Core.FloatType -> Core.Term)
coreEncodeFloatType x = case x of
  Core.FloatTypeBigfloat -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "bigfloat"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.FloatTypeFloat32 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float32"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.FloatTypeFloat64 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float64"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))

coreEncodeFloatValue :: (Core.FloatValue -> Core.Term)
coreEncodeFloatValue x = case x of
  Core.FloatValueBigfloat v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "bigfloat"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralFloat (Core.FloatValueBigfloat v)))}}))
  Core.FloatValueFloat32 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float32"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralFloat (Core.FloatValueFloat32 v)))}}))
  Core.FloatValueFloat64 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.FloatValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float64"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralFloat (Core.FloatValueFloat64 v)))}}))

coreEncodeFunction :: (Core.Function -> Core.Term)
coreEncodeFunction x = case x of
  Core.FunctionElimination v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Function"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "elimination"),
      Core.fieldTerm = (coreEncodeElimination v)}}))
  Core.FunctionLambda v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Function"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "lambda"),
      Core.fieldTerm = (coreEncodeLambda v)}}))
  Core.FunctionPrimitive v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Function"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "primitive"),
      Core.fieldTerm = (coreEncodeName v)}}))

coreEncodeFunctionType :: (Core.FunctionType -> Core.Term)
coreEncodeFunctionType ft = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.FunctionType"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "domain"),
      Core.fieldTerm = (coreEncodeType (Core.functionTypeDomain ft))},
    Core.Field {
      Core.fieldName = (Core.Name "codomain"),
      Core.fieldTerm = (coreEncodeType (Core.functionTypeCodomain ft))}]}))

coreEncodeInjection :: (Core.Injection -> Core.Term)
coreEncodeInjection i = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Injection"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.injectionTypeName i))},
    Core.Field {
      Core.fieldName = (Core.Name "field"),
      Core.fieldTerm = (coreEncodeField (Core.injectionField i))}]}))

coreEncodeIntegerType :: (Core.IntegerType -> Core.Term)
coreEncodeIntegerType x = case x of
  Core.IntegerTypeBigint -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "bigint"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeInt8 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int8"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeInt16 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int16"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeInt32 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int32"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeInt64 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int64"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeUint8 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint8"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeUint16 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint16"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeUint32 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint32"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.IntegerTypeUint64 -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint64"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))

coreEncodeIntegerValue :: (Core.IntegerValue -> Core.Term)
coreEncodeIntegerValue x = case x of
  Core.IntegerValueBigint v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "bigint"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueBigint v)))}}))
  Core.IntegerValueInt8 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int8"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt8 v)))}}))
  Core.IntegerValueInt16 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int16"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt16 v)))}}))
  Core.IntegerValueInt32 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int32"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 v)))}}))
  Core.IntegerValueInt64 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "int64"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt64 v)))}}))
  Core.IntegerValueUint8 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint8"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueUint8 v)))}}))
  Core.IntegerValueUint16 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint16"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueUint16 v)))}}))
  Core.IntegerValueUint32 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint32"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueUint32 v)))}}))
  Core.IntegerValueUint64 v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.IntegerValue"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "uint64"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueUint64 v)))}}))

coreEncodeLambda :: (Core.Lambda -> Core.Term)
coreEncodeLambda l = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Lambda"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "parameter"),
      Core.fieldTerm = (coreEncodeName (Core.lambdaParameter l))},
    Core.Field {
      Core.fieldName = (Core.Name "domain"),
      Core.fieldTerm = Core.TermOptional (Optionals.map coreEncodeType (Core.lambdaDomain l))},
    Core.Field {
      Core.fieldName = (Core.Name "body"),
      Core.fieldTerm = (coreEncodeTerm (Core.lambdaBody l))}]}))

coreEncodeLambdaType :: (Core.LambdaType -> Core.Term)
coreEncodeLambdaType lt = (Core.TermFunction (Core.FunctionLambda (Core.Lambda {
  Core.lambdaParameter = (Core.lambdaTypeParameter lt),
  Core.lambdaDomain = Nothing,
  Core.lambdaBody = (coreEncodeType (Core.lambdaTypeBody lt))})))

coreEncodeLet :: (Core.Let -> Core.Term)
coreEncodeLet l = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Let"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "bindings"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeField (Core.letBindings l)))},
    Core.Field {
      Core.fieldName = (Core.Name "environment"),
      Core.fieldTerm = (coreEncodeTerm (Core.letEnvironment l))}]}))

coreEncodeLiteral :: (Core.Literal -> Core.Term)
coreEncodeLiteral x = case x of
  Core.LiteralBinary v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Literal"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "binary"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralBinary v))}}))
  Core.LiteralBoolean v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Literal"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "boolean"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralBoolean v))}}))
  Core.LiteralFloat v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Literal"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float"),
      Core.fieldTerm = (coreEncodeFloatValue v)}}))
  Core.LiteralInteger v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Literal"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "integer"),
      Core.fieldTerm = (coreEncodeIntegerValue v)}}))
  Core.LiteralString v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Literal"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "string"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralString v))}}))

coreEncodeLiteralType :: (Core.LiteralType -> Core.Term)
coreEncodeLiteralType x = case x of
  Core.LiteralTypeBinary -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.LiteralType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "binary"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.LiteralTypeBoolean -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.LiteralType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "boolean"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))
  Core.LiteralTypeFloat v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.LiteralType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "float"),
      Core.fieldTerm = (coreEncodeFloatType v)}}))
  Core.LiteralTypeInteger v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.LiteralType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "integer"),
      Core.fieldTerm = (coreEncodeIntegerType v)}}))
  Core.LiteralTypeString -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.LiteralType"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "string"),
      Core.fieldTerm = (Core.TermRecord (Core.Record {
        Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
        Core.recordFields = []}))}}))

coreEncodeMapType :: (Core.MapType -> Core.Term)
coreEncodeMapType mt = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.MapType"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "keys"),
      Core.fieldTerm = (coreEncodeType (Core.mapTypeKeys mt))},
    Core.Field {
      Core.fieldName = (Core.Name "values"),
      Core.fieldTerm = (coreEncodeType (Core.mapTypeValues mt))}]}))

coreEncodeName :: (Core.Name -> Core.Term)
coreEncodeName fn = (Core.TermWrap (Core.Nominal {
  Core.nominalTypeName = (Core.Name "hydra/core.Name"),
  Core.nominalObject = (Core.TermLiteral (Core.LiteralString (Core.unName fn)))}))

coreEncodeNominalTerm :: (Core.Nominal Core.Term -> Core.Term)
coreEncodeNominalTerm n = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Nominal"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.nominalTypeName n))},
    Core.Field {
      Core.fieldName = (Core.Name "object"),
      Core.fieldTerm = (coreEncodeTerm (Core.nominalObject n))}]}))

coreEncodeNominalType :: (Core.Nominal Core.Type -> Core.Term)
coreEncodeNominalType nt = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Nominal"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.nominalTypeName nt))},
    Core.Field {
      Core.fieldName = (Core.Name "object"),
      Core.fieldTerm = (coreEncodeType (Core.nominalObject nt))}]}))

coreEncodeOptionalCases :: (Core.OptionalCases -> Core.Term)
coreEncodeOptionalCases oc = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.OptionalCases"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "nothing"),
      Core.fieldTerm = (coreEncodeTerm (Core.optionalCasesNothing oc))},
    Core.Field {
      Core.fieldName = (Core.Name "just"),
      Core.fieldTerm = (coreEncodeTerm (Core.optionalCasesJust oc))}]}))

coreEncodeProjection :: (Core.Projection -> Core.Term)
coreEncodeProjection p = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Projection"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.projectionTypeName p))},
    Core.Field {
      Core.fieldName = (Core.Name "field"),
      Core.fieldTerm = (coreEncodeName (Core.projectionField p))}]}))

coreEncodeRecord :: (Core.Record -> Core.Term)
coreEncodeRecord r = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Record"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.recordTypeName r))},
    Core.Field {
      Core.fieldName = (Core.Name "fields"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeField (Core.recordFields r)))}]}))

coreEncodeRowType :: (Core.RowType -> Core.Term)
coreEncodeRowType rt = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.RowType"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "typeName"),
      Core.fieldTerm = (coreEncodeName (Core.rowTypeTypeName rt))},
    Core.Field {
      Core.fieldName = (Core.Name "extends"),
      Core.fieldTerm = (Core.TermOptional (Optionals.map coreEncodeName (Core.rowTypeExtends rt)))},
    Core.Field {
      Core.fieldName = (Core.Name "fields"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeFieldType (Core.rowTypeFields rt)))}]}))

coreEncodeSum :: (Core.Sum -> Core.Term)
coreEncodeSum s = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.Sum"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "index"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (Core.sumIndex s))))},
    Core.Field {
      Core.fieldName = (Core.Name "size"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (Core.sumSize s))))},
    Core.Field {
      Core.fieldName = (Core.Name "term"),
      Core.fieldTerm = (coreEncodeTerm (Core.sumTerm s))}]}))

coreEncodeTerm :: (Core.Term -> Core.Term)
coreEncodeTerm x = case x of
  Core.TermAnnotated v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "annotated"),
      Core.fieldTerm = (coreEncodeAnnotatedTerm v)}}))
  Core.TermApplication v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "application"),
      Core.fieldTerm = (coreEncodeApplication v)}}))
  Core.TermFunction v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "function"),
      Core.fieldTerm = (coreEncodeFunction v)}}))
  Core.TermLet v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "let"),
      Core.fieldTerm = (coreEncodeLet v)}}))
  Core.TermLiteral v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "literal"),
      Core.fieldTerm = (coreEncodeLiteral v)}}))
  Core.TermList v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "list"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeTerm v))}}))
  Core.TermOptional v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "optional"),
      Core.fieldTerm = (Core.TermOptional (Optionals.map coreEncodeTerm v))}}))
  Core.TermProduct v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "product"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeTerm v))}}))
  Core.TermRecord v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "record"),
      Core.fieldTerm = (coreEncodeRecord v)}}))
  Core.TermSum v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "sum"),
      Core.fieldTerm = (coreEncodeSum v)}}))
  Core.TermTypeAbstraction v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "typeAbstraction"),
      Core.fieldTerm = (coreEncodeTypeAbstraction v)}}))
  Core.TermTypeApplication v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "typeApplication"),
      Core.fieldTerm = (coreEncodeTypedTerm v)}}))
  Core.TermTyped v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "typed"),
      Core.fieldTerm = (coreEncodeTypedTerm v)}}))
  Core.TermUnion v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "union"),
      Core.fieldTerm = (coreEncodeInjection v)}}))
  Core.TermVariable v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "variable"),
      Core.fieldTerm = (coreEncodeName v)}}))
  Core.TermWrap v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Term"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "wrap"),
      Core.fieldTerm = (coreEncodeNominalTerm v)}}))
  _ -> (Core.TermLiteral (Core.LiteralString "not implemented"))

coreEncodeTupleProjection :: (Core.TupleProjection -> Core.Term)
coreEncodeTupleProjection tp = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.TupleProjection"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "arity"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (Core.tupleProjectionArity tp))))},
    Core.Field {
      Core.fieldName = (Core.Name "index"),
      Core.fieldTerm = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (Core.tupleProjectionIndex tp))))}]}))

coreEncodeType :: (Core.Type -> Core.Term)
coreEncodeType x = case x of
  Core.TypeAnnotated v -> (Core.TermAnnotated (Core.Annotated {
    Core.annotatedSubject = (coreEncodeType (Core.annotatedSubject v)),
    Core.annotatedAnnotation = (Core.annotatedAnnotation v)}))
  Core.TypeApplication v -> (coreEncodeApplicationType v)
  Core.TypeFunction v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "function"),
      Core.fieldTerm = (coreEncodeFunctionType v)}}))
  Core.TypeLambda v -> (coreEncodeLambdaType v)
  Core.TypeList v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "list"),
      Core.fieldTerm = (coreEncodeType v)}}))
  Core.TypeLiteral v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "literal"),
      Core.fieldTerm = (coreEncodeLiteralType v)}}))
  Core.TypeMap v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "map"),
      Core.fieldTerm = (coreEncodeMapType v)}}))
  Core.TypeOptional v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "optional"),
      Core.fieldTerm = (coreEncodeType v)}}))
  Core.TypeProduct v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "product"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeType v))}}))
  Core.TypeRecord v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "record"),
      Core.fieldTerm = (coreEncodeRowType v)}}))
  Core.TypeSet v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "set"),
      Core.fieldTerm = (coreEncodeType v)}}))
  Core.TypeStream v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "stream"),
      Core.fieldTerm = (coreEncodeType v)}}))
  Core.TypeSum v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "sum"),
      Core.fieldTerm = (Core.TermList (Lists.map coreEncodeType v))}}))
  Core.TypeUnion v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "union"),
      Core.fieldTerm = (coreEncodeRowType v)}}))
  Core.TypeVariable v -> (Core.TermVariable v)
  Core.TypeWrap v -> (Core.TermUnion (Core.Injection {
    Core.injectionTypeName = (Core.Name "hydra/core.Type"),
    Core.injectionField = Core.Field {
      Core.fieldName = (Core.Name "wrap"),
      Core.fieldTerm = (coreEncodeNominalType v)}}))

coreEncodeTypeAbstraction :: (Core.TypeAbstraction -> Core.Term)
coreEncodeTypeAbstraction l = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.TypeAbstraction"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "parameter"),
      Core.fieldTerm = (coreEncodeName (Core.typeAbstractionParameter l))},
    Core.Field {
      Core.fieldName = (Core.Name "body"),
      Core.fieldTerm = (coreEncodeTerm (Core.typeAbstractionBody l))}]}))

coreEncodeTypedTerm :: (Core.TypedTerm -> Core.Term)
coreEncodeTypedTerm tt = (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.TypedTerm"),
  Core.recordFields = [
    Core.Field {
      Core.fieldName = (Core.Name "type"),
      Core.fieldTerm = (coreEncodeType (Core.typedTermType tt))},
    Core.Field {
      Core.fieldName = (Core.Name "term"),
      Core.fieldTerm = (coreEncodeTerm (Core.typedTermTerm tt))}]}))
