module Hydra.Dsl.Core where

import Hydra.Kernel
import Hydra.Dsl.Base as Base

import qualified Data.Map as M
import qualified Data.Maybe as Y


annotatedTerm :: TTerm Term -> TTerm (M.Map String Term) -> TTerm AnnotatedTerm
annotatedTerm subject annotation = Base.record _AnnotatedTerm [
    _AnnotatedTerm_subject>>: subject,
    _AnnotatedTerm_annotation>>: annotation]

annotatedTermSubject :: TTerm (AnnotatedTerm -> Term)
annotatedTermSubject = project _AnnotatedTerm _AnnotatedTerm_subject

annotatedTermAnnotation :: TTerm (AnnotatedTerm -> M.Map String Term)
annotatedTermAnnotation = project _AnnotatedTerm _AnnotatedTerm_annotation

annotatedType :: TTerm Type -> TTerm (M.Map String Term) -> TTerm AnnotatedType
annotatedType subject annotation = Base.record _AnnotatedType [
    _AnnotatedType_subject>>: subject,
    _AnnotatedType_annotation>>: annotation]

annotatedTypeSubject :: TTerm (AnnotatedType -> Type)
annotatedTypeSubject = project _AnnotatedType _AnnotatedType_subject

annotatedTypeAnnotation :: TTerm (AnnotatedType -> M.Map String Term)
annotatedTypeAnnotation = project _AnnotatedType _AnnotatedType_annotation

application :: TTerm Term -> TTerm Term -> TTerm (Application)
application function argument = Base.record _Application [
    _Application_function>>: function,
    _Application_argument>>: argument]

applicationFunction :: TTerm (Application -> Term)
applicationFunction = project _Application _Application_function

applicationArgument :: TTerm (Application -> Term)
applicationArgument = project _Application _Application_argument

applicationType :: TTerm Type -> TTerm Type -> TTerm (ApplicationType)
applicationType function argument = Base.record _ApplicationType [
    _ApplicationType_function>>: function,
    _ApplicationType_argument>>: argument]

applicationTypeFunction :: TTerm (ApplicationType -> Type)
applicationTypeFunction = project _ApplicationType _ApplicationType_function

applicationTypeArgument :: TTerm (ApplicationType -> Type)
applicationTypeArgument = project _ApplicationType _ApplicationType_argument

caseStatement :: TTerm Name -> TTerm (Maybe Term) -> TTerm [Field] -> TTerm (CaseStatement)
caseStatement typeName defaultTerm cases = Base.record _CaseStatement [
    _CaseStatement_typeName>>: typeName,
    _CaseStatement_default>>: defaultTerm,
    _CaseStatement_cases>>: cases]

caseStatementTypeName :: TTerm (CaseStatement -> Name)
caseStatementTypeName = project _CaseStatement _CaseStatement_typeName

caseStatementDefault :: TTerm (CaseStatement -> Maybe Term)
caseStatementDefault = project _CaseStatement _CaseStatement_default

caseStatementCases :: TTerm (CaseStatement -> [Field])
caseStatementCases = project _CaseStatement _CaseStatement_cases

field :: TTerm Name -> TTerm Term -> TTerm Field
field name term = Base.record _Field [
    _Field_name>>: name,
    _Field_term>>: term]

fieldName :: TTerm (Field -> Name)
fieldName = project _Field _Field_name

fieldTerm :: TTerm (Field -> Term)
fieldTerm = project _Field _Field_term

fieldType :: TTerm Name -> TTerm Type -> TTerm FieldType
fieldType name typ = Base.record _FieldType [
    _FieldType_name>>: name,
    _FieldType_type>>: typ]

fieldTypeName :: TTerm (FieldType -> Name)
fieldTypeName = project _FieldType _FieldType_name

fieldTypeType :: TTerm (FieldType -> Type)
fieldTypeType = project _FieldType _FieldType_type

floatType :: FloatType -> TTerm FloatType
floatType t = unitVariant _FloatType $ case t of
  FloatTypeBigfloat -> _FloatType_bigfloat
  FloatTypeFloat32 -> _FloatType_float32
  FloatTypeFloat64 -> _FloatType_float64

functionType :: TTerm Type -> TTerm Type -> TTerm FunctionType
functionType domain codomain = Base.record _FunctionType [
    _FunctionType_domain>>: domain,
    _FunctionType_codomain>>: codomain]

functionTypeDomain :: TTerm (FunctionType -> Type)
functionTypeDomain = project _FunctionType _FunctionType_domain

functionTypeCodomain :: TTerm (FunctionType -> Type)
functionTypeCodomain = project _FunctionType _FunctionType_codomain

injection :: TTerm Name -> TTerm Field -> TTerm Injection
injection typeName field = Base.record _Injection [
    _Injection_typeName>>: typeName,
    _Injection_field>>: field]

injectionTypeName :: TTerm (Injection -> Name)
injectionTypeName = project _Injection _Injection_typeName

injectionField :: TTerm (Injection -> Field)
injectionField = project _Injection _Injection_field

integerType :: IntegerType -> TTerm IntegerType
integerType t = unitVariant _IntegerType $ case t of
  IntegerTypeBigint -> _IntegerType_bigint
  IntegerTypeInt8 -> _IntegerType_int8
  IntegerTypeInt16 -> _IntegerType_int16
  IntegerTypeInt32 -> _IntegerType_int32
  IntegerTypeInt64 -> _IntegerType_int64
  IntegerTypeUint8 -> _IntegerType_uint8
  IntegerTypeUint16 -> _IntegerType_uint16
  IntegerTypeUint32 -> _IntegerType_uint32
  IntegerTypeUint64 -> _IntegerType_uint64

lambda :: TTerm Name -> TTerm Term -> TTerm Lambda
lambda parameter body = Base.record _Lambda [
    _Lambda_parameter>>: parameter,
    _Lambda_body>>: body]

lambdaParameter :: TTerm (Lambda -> Name)
lambdaParameter = project _Lambda _Lambda_parameter

lambdaBody :: TTerm (Lambda -> Term)
lambdaBody = project _Lambda _Lambda_body

lambdaDomain :: TTerm (Lambda -> Maybe Type)
lambdaDomain = project _Lambda _Lambda_domain

lambdaType :: TTerm Name -> TTerm Type -> TTerm LambdaType
lambdaType parameter body = Base.record _LambdaType [
    _LambdaType_parameter>>: parameter,
    _LambdaType_body>>: body]

lambdaTypeParameter :: TTerm (LambdaType -> Name)
lambdaTypeParameter = project _LambdaType _LambdaType_parameter

lambdaTypeBody :: TTerm (LambdaType -> Type)
lambdaTypeBody = project _LambdaType _LambdaType_body

letExpression :: TTerm [LetBinding] -> TTerm Term -> TTerm Let
letExpression bindings environment = Base.record _Let [
    _Let_bindings>>: bindings,
    _Let_environment>>: environment]

letBindings :: TTerm (Let -> [LetBinding])
letBindings = project _Let _Let_bindings

letBindingName :: TTerm (LetBinding -> Name)
letBindingName = project _LetBinding _LetBinding_name

letBindingTerm :: TTerm (LetBinding -> Term)
letBindingTerm = project _LetBinding _LetBinding_term

letBindingType :: TTerm (LetBinding -> Y.Maybe TypeScheme)
letBindingType = project _LetBinding _LetBinding_type

letEnvironment :: TTerm (Let -> Term)
letEnvironment = project _Let _Let_environment

literalBinary :: TTerm String -> TTerm Literal
literalBinary = variant _Literal _Literal_binary

literalBoolean :: TTerm Bool -> TTerm Literal
literalBoolean = variant _Literal _Literal_boolean

literalFloat :: TTerm FloatValue -> TTerm Literal
literalFloat = variant _Literal _Literal_float

literalInteger :: TTerm IntegerValue -> TTerm Literal
literalInteger = variant _Literal _Literal_integer

mapType :: TTerm Type -> TTerm Type -> TTerm MapType
mapType keys values = Base.record _MapType [
    _MapType_keys>>: keys,
    _MapType_values>>: values]

mapTypeKeys :: TTerm (MapType -> Type)
mapTypeKeys = project _MapType _MapType_keys

mapTypeValues :: TTerm (MapType -> Type)
mapTypeValues = project _MapType _MapType_values

name :: Name -> TTerm Name
name nm = TTerm $ coreEncodeName nm

optionalCases :: TTerm Term -> TTerm Term -> TTerm OptionalCases
optionalCases nothing just = Base.record _OptionalCases [
    _OptionalCases_nothing>>: nothing,
    _OptionalCases_just>>: just]

optionalCasesNothing :: TTerm (OptionalCases -> Term)
optionalCasesNothing = project _OptionalCases _OptionalCases_nothing

optionalCasesJust :: TTerm (OptionalCases -> Term)
optionalCasesJust = project _OptionalCases _OptionalCases_just

projectionTypeName :: TTerm (Projection -> Name)
projectionTypeName = project _Projection _Projection_typeName

projectionField :: TTerm (Projection -> Name)
projectionField = project _Projection _Projection_field

record :: TTerm Name -> TTerm [Field] -> TTerm Record
record typeName fields = Base.record _Record [
    _Record_typeName>>: typeName,
    _Record_fields>>: fields]

recordTypeName :: TTerm (Record -> Name)
recordTypeName = project _Record _Record_typeName

recordFields :: TTerm (Record -> [Field])
recordFields = project _Record _Record_fields

rowType :: TTerm Name -> TTerm [FieldType] -> TTerm (RowType)
rowType typeName fields = Base.record _RowType [
    _RowType_typeName>>: typeName,
    _RowType_fields>>: fields]

rowTypeTypeName :: TTerm (RowType -> Name)
rowTypeTypeName = project _RowType _RowType_typeName

rowTypeFields :: TTerm (RowType -> [FieldType])
rowTypeFields = project _RowType _RowType_fields

sum :: TTerm Int -> TTerm Int -> TTerm Term -> TTerm Sum
sum index size term = Base.record _Sum [
    _Sum_index>>: index,
    _Sum_size>>: size,
    _Sum_term>>: term]

sumIndex :: TTerm (Sum -> Int)
sumIndex = project _Sum _Sum_index

sumSize :: TTerm (Sum -> Int)
sumSize = project _Sum _Sum_size

sumTerm :: TTerm (Sum -> Term)
sumTerm = project _Sum _Sum_term

termAnnotated :: TTerm AnnotatedTerm -> TTerm Term
termAnnotated = variant _Term _Term_annotated

tupleProjectionArity :: TTerm (TupleProjection -> Int)
tupleProjectionArity = project _TupleProjection _TupleProjection_arity

tupleProjectionIndex :: TTerm (TupleProjection -> Int)
tupleProjectionIndex = project _TupleProjection _TupleProjection_index

typeAbstractionParameter :: TTerm (TypeAbstraction -> Name)
typeAbstractionParameter = project _TypeAbstraction _TypeAbstraction_parameter

typeAbstractionBody :: TTerm (TypeAbstraction -> Type)
typeAbstractionBody = project _TypeAbstraction _TypeAbstraction_body

typeSchemeVariables :: TTerm (TypeScheme -> [Name])
typeSchemeVariables = project _TypeScheme _TypeScheme_variables

typeSchemeType :: TTerm (TypeScheme -> Type)
typeSchemeType = project _TypeScheme _TypeScheme_type

typedTermTerm :: TTerm (TypedTerm -> Term)
typedTermTerm = project _TypedTerm _TypedTerm_term

unName :: TTerm (Name -> String)
unName = unwrap _Name

unNamespace :: TTerm (Namespace -> String)
unNamespace = unwrap _Namespace

wrappedTerm :: TTerm Name -> TTerm Term -> TTerm WrappedTerm
wrappedTerm typeName object = Base.record _WrappedTerm [
    _WrappedTerm_typeName>>: typeName,
    _WrappedTerm_object>>: object]

wrappedTermTypeName :: TTerm (WrappedTerm -> Name)
wrappedTermTypeName = project _WrappedTerm _WrappedTerm_typeName

wrappedTermObject :: TTerm (WrappedTerm -> Term)
wrappedTermObject = project _WrappedTerm _WrappedTerm_object

wrappedType :: TTerm Name -> TTerm Type -> TTerm WrappedType
wrappedType typeName object = Base.record _WrappedType [
    _WrappedType_typeName>>: typeName,
    _WrappedType_object>>: object]

wrappedTypeTypeName :: TTerm (WrappedType -> Name)
wrappedTypeTypeName = project _WrappedType _WrappedType_typeName

wrappedTypeObject :: TTerm (WrappedType -> Type)
wrappedTypeObject = project _WrappedType _WrappedType_object
