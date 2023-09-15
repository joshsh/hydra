module Hydra.Dsl.Core where

import Hydra.Kernel
import Hydra.Dsl.Base as Base

import qualified Data.Map as M


annotated :: Datum x -> Datum a -> Datum (Annotated x a)
annotated subject annotation = Base.record _Annotated [
    _Annotated_subject>>: subject,
    _Annotated_annotation>>: annotation]

annotatedSubject :: Datum (Annotated x a -> x)
annotatedSubject = project _Annotated _Annotated_subject

annotatedAnnotation :: Datum (Annotated x a -> a)
annotatedAnnotation = project _Annotated _Annotated_annotation

application :: Datum (Term) -> Datum (Term) -> Datum (Application Kv)
application function argument = Base.record _Application [
    _Application_function>>: function,
    _Application_argument>>: argument]

applicationFunction :: Datum (Application Kv -> Term)
applicationFunction = project _Application _Application_function

applicationArgument :: Datum (Application Kv -> Term)
applicationArgument = project _Application _Application_argument

applicationType :: Datum (Type Kv) -> Datum (Type Kv) -> Datum (ApplicationType Kv)
applicationType function argument = Base.record _ApplicationType [
    _ApplicationType_function>>: function,
    _ApplicationType_argument>>: argument]

applicationTypeFunction :: Datum (ApplicationType Kv -> Type Kv)
applicationTypeFunction = project _ApplicationType _ApplicationType_function

applicationTypeArgument :: Datum (ApplicationType Kv -> Type Kv)
applicationTypeArgument = project _ApplicationType _ApplicationType_argument

caseStatement :: Datum Name -> Datum (Maybe (Term)) -> Datum [Field Kv] -> Datum (CaseStatement Kv)
caseStatement typeName defaultTerm cases = Base.record _CaseStatement [
    _CaseStatement_typeName>>: typeName,
    _CaseStatement_default>>: defaultTerm,
    _CaseStatement_cases>>: cases]

caseStatementTypeName :: Datum (CaseStatement Kv -> Name)
caseStatementTypeName = project _CaseStatement _CaseStatement_typeName

caseStatementDefault :: Datum (CaseStatement Kv -> Maybe (Term))
caseStatementDefault = project _CaseStatement _CaseStatement_default

caseStatementCases :: Datum (CaseStatement Kv -> [Field Kv])
caseStatementCases = project _CaseStatement _CaseStatement_cases

field :: Datum Name -> Datum (Term) -> Datum (Field Kv)
field name term = Base.record _Field [
    _Field_name>>: name,
    _Field_term>>: term]

fieldName :: Datum (Field Kv -> Name)
fieldName = project _Field _Field_name

fieldTerm :: Datum (Field Kv -> Term)
fieldTerm = project _Field _Field_term

fieldType :: Datum Name -> Datum (Type Kv) -> Datum (FieldType Kv)
fieldType name typ = Base.record _FieldType [
    _FieldType_name>>: name,
    _FieldType_type>>: typ]

fieldTypeName :: Datum (FieldType Kv -> Name)
fieldTypeName = project _FieldType _FieldType_name

fieldTypeType :: Datum (FieldType Kv -> Type Kv)
fieldTypeType = project _FieldType _FieldType_type

functionType :: Datum (Type Kv) -> Datum (Type Kv) -> Datum (FunctionType Kv)
functionType domain codomain = Base.record _FunctionType [
    _FunctionType_domain>>: domain,
    _FunctionType_codomain>>: codomain]

functionTypeDomain :: Datum (FunctionType Kv -> Type Kv)
functionTypeDomain = project _FunctionType _FunctionType_domain

functionTypeCodomain :: Datum (FunctionType Kv -> Type Kv)
functionTypeCodomain = project _FunctionType _FunctionType_codomain

injection :: Datum Name -> Datum (Field Kv) -> Datum (Injection a)
injection typeName field = Base.record _Injection [
    _Injection_typeName>>: typeName,
    _Injection_field>>: field]

injectionTypeName :: Datum (Injection a -> Name)
injectionTypeName = project _Injection _Injection_typeName

injectionField :: Datum (Injection a -> Field Kv)
injectionField = project _Injection _Injection_field

lambda :: Datum Name -> Datum (Term) -> Datum (Lambda Kv)
lambda parameter body = Base.record _Lambda [
    _Lambda_parameter>>: parameter,
    _Lambda_body>>: body]

lambdaParameter :: Datum (Lambda Kv -> Name)
lambdaParameter = project _Lambda _Lambda_parameter

lambdaBody :: Datum (Lambda Kv -> Term)
lambdaBody = project _Lambda _Lambda_body

lambdaType :: Datum Name -> Datum (Type Kv) -> Datum (LambdaType Kv)
lambdaType parameter body = Base.record _LambdaType [
    _LambdaType_parameter>>: parameter,
    _LambdaType_body>>: body]

lambdaTypeParameter :: Datum (LambdaType Kv -> Name)
lambdaTypeParameter = project _LambdaType _LambdaType_parameter

lambdaTypeBody :: Datum (LambdaType Kv -> Type Kv)
lambdaTypeBody = project _LambdaType _LambdaType_body

letExpression :: Datum (M.Map Name (Term)) -> Datum (Term) -> Datum (Let Kv)
letExpression bindings environment = Base.record _Let [
    _Let_bindings>>: bindings,
    _Let_environment>>: environment]

letBindings :: Datum (Let Kv -> M.Map Name (Term))
letBindings = project _Let _Let_bindings

letEnvironment :: Datum (Let Kv -> Term)
letEnvironment = project _Let _Let_environment

mapType :: Datum (Type Kv) -> Datum (Type Kv) -> Datum (MapType Kv)
mapType keys values = Base.record _MapType [
    _MapType_keys>>: keys,
    _MapType_values>>: values]

mapTypeKeys :: Datum (MapType Kv -> Type Kv)
mapTypeKeys = project _MapType _MapType_keys

mapTypeValues :: Datum (MapType Kv -> Type Kv)
mapTypeValues = project _MapType _MapType_values

nominal :: Datum Name -> Datum x -> Datum (Nominal x)
nominal typeName object = Base.record _Nominal [
    _Nominal_typeName>>: typeName,
    _Nominal_object>>: object]

nominalTypeName :: Datum (Nominal x -> Name)
nominalTypeName = project _Nominal _Nominal_typeName

nominalObject :: Datum (Nominal x -> x)
nominalObject = project _Nominal _Nominal_object

optionalCases :: Datum (Term) -> Datum (Term) -> Datum (OptionalCases Kv)
optionalCases nothing just = Base.record _OptionalCases [
    _OptionalCases_nothing>>: nothing,
    _OptionalCases_just>>: just]

optionalCasesNothing :: Datum (OptionalCases Kv -> Term)
optionalCasesNothing = project _OptionalCases _OptionalCases_nothing

optionalCasesJust :: Datum (OptionalCases Kv -> Term)
optionalCasesJust = project _OptionalCases _OptionalCases_just

record :: Datum Name -> Datum [Field Kv] -> Datum (Record a)
record typeName fields = Base.record _Record [
    _Record_typeName>>: typeName,
    _Record_fields>>: fields]

recordTypeName :: Datum (Record a -> Name)
recordTypeName = project _Record _Record_typeName

recordFields :: Datum (Record a -> [Field Kv])
recordFields = project _Record _Record_fields

rowType :: Datum Name -> Datum (Maybe Name) -> Datum [FieldType Kv] -> Datum (RowType Kv)
rowType typeName extends fields = Base.record _RowType [
    _RowType_typeName>>: typeName,
    _RowType_extends>>: extends,
    _RowType_fields>>: fields]

rowTypeTypeName :: Datum (RowType Kv -> Name)
rowTypeTypeName = project _RowType _RowType_typeName

rowTypeExtends :: Datum (RowType Kv -> Maybe Name)
rowTypeExtends = project _RowType _RowType_extends

rowTypeFields :: Datum (RowType Kv -> [FieldType Kv])
rowTypeFields = project _RowType _RowType_fields

sum :: Datum Int -> Datum Int -> Datum (Term) -> Datum (Sum a)
sum index size term = Base.record _Sum [
    _Sum_index>>: index,
    _Sum_size>>: size,
    _Sum_term>>: term]

sumIndex :: Datum (Sum a -> Int)
sumIndex = project _Sum _Sum_index

sumSize :: Datum (Sum a -> Int)
sumSize = project _Sum _Sum_size

sumTerm :: Datum (Sum a -> Term)
sumTerm = project _Sum _Sum_term
