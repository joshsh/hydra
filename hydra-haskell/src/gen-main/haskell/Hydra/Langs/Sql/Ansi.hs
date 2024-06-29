-- | A subset of ANSI SQL:2003, capturing selected productions of the BNF grammar provided at https://ronsavage.github.io/SQL/sql-2003-2.bnf.html, which is based on the Final Committee Draft (FCD) of ISO/IEC 9075-2:2003

module Hydra.Langs.Sql.Ansi where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype ApproximateNumericLiteral = 
  ApproximateNumericLiteral {
    unApproximateNumericLiteral :: String}
  deriving (Eq, Ord, Read, Show)

_ApproximateNumericLiteral = (Core.Name "hydra/langs/sql/ansi.ApproximateNumericLiteral")

data BinaryStringLiteral = 
  BinaryStringLiteral {}
  deriving (Eq, Ord, Read, Show)

_BinaryStringLiteral = (Core.Name "hydra/langs/sql/ansi.BinaryStringLiteral")

newtype CharacterStringLiteral = 
  CharacterStringLiteral {
    unCharacterStringLiteral :: String}
  deriving (Eq, Ord, Read, Show)

_CharacterStringLiteral = (Core.Name "hydra/langs/sql/ansi.CharacterStringLiteral")

newtype ColumnName = 
  ColumnName {
    unColumnName :: String}
  deriving (Eq, Ord, Read, Show)

_ColumnName = (Core.Name "hydra/langs/sql/ansi.ColumnName")

data DateString = 
  DateString {}
  deriving (Eq, Ord, Read, Show)

_DateString = (Core.Name "hydra/langs/sql/ansi.DateString")

newtype DomainName = 
  DomainName {
    unDomainName :: String}
  deriving (Eq, Ord, Read, Show)

_DomainName = (Core.Name "hydra/langs/sql/ansi.DomainName")

newtype ExactNumericLiteral = 
  ExactNumericLiteral {
    unExactNumericLiteral :: String}
  deriving (Eq, Ord, Read, Show)

_ExactNumericLiteral = (Core.Name "hydra/langs/sql/ansi.ExactNumericLiteral")

newtype LeftBracketOrTrigraph = 
  LeftBracketOrTrigraph {
    unLeftBracketOrTrigraph :: String}
  deriving (Eq, Ord, Read, Show)

_LeftBracketOrTrigraph = (Core.Name "hydra/langs/sql/ansi.LeftBracketOrTrigraph")

newtype RightBracketOrTrigraph = 
  RightBracketOrTrigraph {
    unRightBracketOrTrigraph :: String}
  deriving (Eq, Ord, Read, Show)

_RightBracketOrTrigraph = (Core.Name "hydra/langs/sql/ansi.RightBracketOrTrigraph")

data NationalCharacterStringLiteral = 
  NationalCharacterStringLiteral {}
  deriving (Eq, Ord, Read, Show)

_NationalCharacterStringLiteral = (Core.Name "hydra/langs/sql/ansi.NationalCharacterStringLiteral")

newtype PathResolvedUserDefinedTypeName = 
  PathResolvedUserDefinedTypeName {
    unPathResolvedUserDefinedTypeName :: String}
  deriving (Eq, Ord, Read, Show)

_PathResolvedUserDefinedTypeName = (Core.Name "hydra/langs/sql/ansi.PathResolvedUserDefinedTypeName")

newtype TableName = 
  TableName {
    unTableName :: String}
  deriving (Eq, Ord, Read, Show)

_TableName = (Core.Name "hydra/langs/sql/ansi.TableName")

data TimeString = 
  TimeString {}
  deriving (Eq, Ord, Read, Show)

_TimeString = (Core.Name "hydra/langs/sql/ansi.TimeString")

data TimestampLiteral = 
  TimestampLiteral {}
  deriving (Eq, Ord, Read, Show)

_TimestampLiteral = (Core.Name "hydra/langs/sql/ansi.TimestampLiteral")

data UnicodeCharacterStringLiteral = 
  UnicodeCharacterStringLiteral {}
  deriving (Eq, Ord, Read, Show)

_UnicodeCharacterStringLiteral = (Core.Name "hydra/langs/sql/ansi.UnicodeCharacterStringLiteral")

newtype UnsignedInteger = 
  UnsignedInteger {
    unUnsignedInteger :: String}
  deriving (Eq, Ord, Read, Show)

_UnsignedInteger = (Core.Name "hydra/langs/sql/ansi.UnsignedInteger")

data ApproximateNumericType = 
  ApproximateNumericTypeFloat (Maybe Precision) |
  ApproximateNumericTypeReal  |
  ApproximateNumericTypeDouble 
  deriving (Eq, Ord, Read, Show)

_ApproximateNumericType = (Core.Name "hydra/langs/sql/ansi.ApproximateNumericType")

_ApproximateNumericType_float = (Core.Name "float")

_ApproximateNumericType_real = (Core.Name "real")

_ApproximateNumericType_double = (Core.Name "double")

newtype ArrayElement = 
  ArrayElement {
    unArrayElement :: ValueExpression}
  deriving (Eq, Ord, Read, Show)

_ArrayElement = (Core.Name "hydra/langs/sql/ansi.ArrayElement")

data ArrayElementList = 
  ArrayElementList {
    arrayElementListFirst :: ArrayElement,
    arrayElementListRest :: [ArrayElement]}
  deriving (Eq, Ord, Read, Show)

_ArrayElementList = (Core.Name "hydra/langs/sql/ansi.ArrayElementList")

_ArrayElementList_first = (Core.Name "first")

_ArrayElementList_rest = (Core.Name "rest")

data ArrayElementReference = 
  ArrayElementReference {}
  deriving (Eq, Ord, Read, Show)

_ArrayElementReference = (Core.Name "hydra/langs/sql/ansi.ArrayElementReference")

data ArrayType = 
  ArrayType {}
  deriving (Eq, Ord, Read, Show)

_ArrayType = (Core.Name "hydra/langs/sql/ansi.ArrayType")

data ArrayValueConstructor = 
  ArrayValueConstructorEnumeration ArrayValueConstructorByEnumeration |
  ArrayValueConstructorQuery ArrayValueConstructorByQuery
  deriving (Eq, Ord, Read, Show)

_ArrayValueConstructor = (Core.Name "hydra/langs/sql/ansi.ArrayValueConstructor")

_ArrayValueConstructor_enumeration = (Core.Name "enumeration")

_ArrayValueConstructor_query = (Core.Name "query")

data ArrayValueConstructorByQuery = 
  ArrayValueConstructorByQuery {}
  deriving (Eq, Ord, Read, Show)

_ArrayValueConstructorByQuery = (Core.Name "hydra/langs/sql/ansi.ArrayValueConstructorByQuery")

data ArrayValueConstructorByEnumeration = 
  ArrayValueConstructorByEnumeration {
    arrayValueConstructorByEnumerationLeftBracketOrTrigraph :: LeftBracketOrTrigraph,
    arrayValueConstructorByEnumerationArrayElementList :: ArrayElementList,
    arrayValueConstructorByEnumerationRightBracketOrTrigraph :: RightBracketOrTrigraph}
  deriving (Eq, Ord, Read, Show)

_ArrayValueConstructorByEnumeration = (Core.Name "hydra/langs/sql/ansi.ArrayValueConstructorByEnumeration")

_ArrayValueConstructorByEnumeration_leftBracketOrTrigraph = (Core.Name "leftBracketOrTrigraph")

_ArrayValueConstructorByEnumeration_arrayElementList = (Core.Name "arrayElementList")

_ArrayValueConstructorByEnumeration_rightBracketOrTrigraph = (Core.Name "rightBracketOrTrigraph")

data ArrayValueExpression = 
  ArrayValueExpression {}
  deriving (Eq, Ord, Read, Show)

_ArrayValueExpression = (Core.Name "hydra/langs/sql/ansi.ArrayValueExpression")

data AsSubqueryClause = 
  AsSubqueryClause {}
  deriving (Eq, Ord, Read, Show)

_AsSubqueryClause = (Core.Name "hydra/langs/sql/ansi.AsSubqueryClause")

data AttributeOrMethodReference = 
  AttributeOrMethodReference {}
  deriving (Eq, Ord, Read, Show)

_AttributeOrMethodReference = (Core.Name "hydra/langs/sql/ansi.AttributeOrMethodReference")

data BinaryLargeObjectStringType = 
  BinaryLargeObjectStringTypeBinary (Maybe LargeObjectLength) |
  BinaryLargeObjectStringTypeBlob (Maybe LargeObjectLength)
  deriving (Eq, Ord, Read, Show)

_BinaryLargeObjectStringType = (Core.Name "hydra/langs/sql/ansi.BinaryLargeObjectStringType")

_BinaryLargeObjectStringType_binary = (Core.Name "binary")

_BinaryLargeObjectStringType_blob = (Core.Name "blob")

data BooleanFactor = 
  BooleanFactor {
    booleanFactorNOT :: (Maybe ()),
    booleanFactorBooleanTest :: BooleanTest}
  deriving (Eq, Ord, Read, Show)

_BooleanFactor = (Core.Name "hydra/langs/sql/ansi.BooleanFactor")

_BooleanFactor_nOT = (Core.Name "nOT")

_BooleanFactor_booleanTest = (Core.Name "booleanTest")

data BooleanLiteral = 
  BooleanLiteralTRUE  |
  BooleanLiteralFALSE  |
  BooleanLiteralUNKNOWN 
  deriving (Eq, Ord, Read, Show)

_BooleanLiteral = (Core.Name "hydra/langs/sql/ansi.BooleanLiteral")

_BooleanLiteral_tRUE = (Core.Name "tRUE")

_BooleanLiteral_fALSE = (Core.Name "fALSE")

_BooleanLiteral_uNKNOWN = (Core.Name "uNKNOWN")

data BooleanPredicand = 
  BooleanPredicand {}
  deriving (Eq, Ord, Read, Show)

_BooleanPredicand = (Core.Name "hydra/langs/sql/ansi.BooleanPredicand")

data BooleanPrimary = 
  BooleanPrimaryPredicate Predicate |
  BooleanPrimaryPredicand BooleanPredicand
  deriving (Eq, Ord, Read, Show)

_BooleanPrimary = (Core.Name "hydra/langs/sql/ansi.BooleanPrimary")

_BooleanPrimary_predicate = (Core.Name "predicate")

_BooleanPrimary_predicand = (Core.Name "predicand")

data BooleanTerm = 
  BooleanTermFactor BooleanFactor |
  BooleanTermAnd BooleanTerm_And
  deriving (Eq, Ord, Read, Show)

_BooleanTerm = (Core.Name "hydra/langs/sql/ansi.BooleanTerm")

_BooleanTerm_factor = (Core.Name "factor")

_BooleanTerm_and = (Core.Name "and")

data BooleanTerm_And = 
  BooleanTerm_And {
    booleanTerm_AndLhs :: BooleanTerm,
    booleanTerm_AndRhs :: BooleanFactor}
  deriving (Eq, Ord, Read, Show)

_BooleanTerm_And = (Core.Name "hydra/langs/sql/ansi.BooleanTerm.And")

_BooleanTerm_And_lhs = (Core.Name "lhs")

_BooleanTerm_And_rhs = (Core.Name "rhs")

data BooleanTest = 
  BooleanTest {
    booleanTestBooleanPrimary :: BooleanPrimary,
    booleanTestSequence :: (Maybe BooleanTest_Sequence_Option)}
  deriving (Eq, Ord, Read, Show)

_BooleanTest = (Core.Name "hydra/langs/sql/ansi.BooleanTest")

_BooleanTest_booleanPrimary = (Core.Name "booleanPrimary")

_BooleanTest_sequence = (Core.Name "sequence")

data BooleanTest_Sequence_Option = 
  BooleanTest_Sequence_Option {
    booleanTest_Sequence_OptionNOT :: (Maybe ()),
    booleanTest_Sequence_OptionTruthValue :: TruthValue}
  deriving (Eq, Ord, Read, Show)

_BooleanTest_Sequence_Option = (Core.Name "hydra/langs/sql/ansi.BooleanTest.Sequence.Option")

_BooleanTest_Sequence_Option_nOT = (Core.Name "nOT")

_BooleanTest_Sequence_Option_truthValue = (Core.Name "truthValue")

data BooleanType = 
  BooleanType {}
  deriving (Eq, Ord, Read, Show)

_BooleanType = (Core.Name "hydra/langs/sql/ansi.BooleanType")

data BooleanValueExpression = 
  BooleanValueExpressionTerm BooleanTerm |
  BooleanValueExpressionOr BooleanValueExpression_Or
  deriving (Eq, Ord, Read, Show)

_BooleanValueExpression = (Core.Name "hydra/langs/sql/ansi.BooleanValueExpression")

_BooleanValueExpression_term = (Core.Name "term")

_BooleanValueExpression_or = (Core.Name "or")

data BooleanValueExpression_Or = 
  BooleanValueExpression_Or {
    booleanValueExpression_OrLhs :: BooleanValueExpression,
    booleanValueExpression_OrRhs :: BooleanTerm}
  deriving (Eq, Ord, Read, Show)

_BooleanValueExpression_Or = (Core.Name "hydra/langs/sql/ansi.BooleanValueExpression.Or")

_BooleanValueExpression_Or_lhs = (Core.Name "lhs")

_BooleanValueExpression_Or_rhs = (Core.Name "rhs")

data CaseExpression = 
  CaseExpression {}
  deriving (Eq, Ord, Read, Show)

_CaseExpression = (Core.Name "hydra/langs/sql/ansi.CaseExpression")

data CastSpecification = 
  CastSpecification {}
  deriving (Eq, Ord, Read, Show)

_CastSpecification = (Core.Name "hydra/langs/sql/ansi.CastSpecification")

data CharacterSetSpecification = 
  CharacterSetSpecification {}
  deriving (Eq, Ord, Read, Show)

_CharacterSetSpecification = (Core.Name "hydra/langs/sql/ansi.CharacterSetSpecification")

data CharacterStringType = 
  CharacterStringTypeCharacter (Maybe Length) |
  CharacterStringTypeChar (Maybe Length) |
  CharacterStringTypeCharacterVarying Length |
  CharacterStringTypeCharVarying Length |
  CharacterStringTypeVarchar Length |
  CharacterStringTypeCharacterLargeObject (Maybe LargeObjectLength) |
  CharacterStringTypeCharLargeObject (Maybe LargeObjectLength) |
  CharacterStringTypeClob (Maybe LargeObjectLength)
  deriving (Eq, Ord, Read, Show)

_CharacterStringType = (Core.Name "hydra/langs/sql/ansi.CharacterStringType")

_CharacterStringType_character = (Core.Name "character")

_CharacterStringType_char = (Core.Name "char")

_CharacterStringType_characterVarying = (Core.Name "characterVarying")

_CharacterStringType_charVarying = (Core.Name "charVarying")

_CharacterStringType_varchar = (Core.Name "varchar")

_CharacterStringType_characterLargeObject = (Core.Name "characterLargeObject")

_CharacterStringType_charLargeObject = (Core.Name "charLargeObject")

_CharacterStringType_clob = (Core.Name "clob")

data CollateClause = 
  CollateClause {}
  deriving (Eq, Ord, Read, Show)

_CollateClause = (Core.Name "hydra/langs/sql/ansi.CollateClause")

data CollectionType = 
  CollectionTypeArray ArrayType |
  CollectionTypeMultiset MultisetType
  deriving (Eq, Ord, Read, Show)

_CollectionType = (Core.Name "hydra/langs/sql/ansi.CollectionType")

_CollectionType_array = (Core.Name "array")

_CollectionType_multiset = (Core.Name "multiset")

data CollectionValueConstructor = 
  CollectionValueConstructorArray ArrayValueConstructor |
  CollectionValueConstructorMultiset MultisetValueConstructor
  deriving (Eq, Ord, Read, Show)

_CollectionValueConstructor = (Core.Name "hydra/langs/sql/ansi.CollectionValueConstructor")

_CollectionValueConstructor_array = (Core.Name "array")

_CollectionValueConstructor_multiset = (Core.Name "multiset")

data CollectionValueExpression = 
  CollectionValueExpressionArray ArrayValueExpression |
  CollectionValueExpressionMultiset MultisetValueExpression
  deriving (Eq, Ord, Read, Show)

_CollectionValueExpression = (Core.Name "hydra/langs/sql/ansi.CollectionValueExpression")

_CollectionValueExpression_array = (Core.Name "array")

_CollectionValueExpression_multiset = (Core.Name "multiset")

data ColumnConstraintDefinition = 
  ColumnConstraintDefinition {}
  deriving (Eq, Ord, Read, Show)

_ColumnConstraintDefinition = (Core.Name "hydra/langs/sql/ansi.ColumnConstraintDefinition")

data ColumnDefinition = 
  ColumnDefinition {
    columnDefinitionName :: ColumnName,
    columnDefinitionTypeOrDomain :: (Maybe ColumnDefinition_TypeOrDomain_Option),
    columnDefinitionRefScope :: (Maybe ReferenceScopeCheck),
    columnDefinitionDefaultOrIdentityOrGeneration :: (Maybe ColumnDefinition_DefaultOrIdentityOrGeneration_Option),
    columnDefinitionConstraints :: [ColumnConstraintDefinition],
    columnDefinitionCollate :: (Maybe CollateClause)}
  deriving (Eq, Ord, Read, Show)

_ColumnDefinition = (Core.Name "hydra/langs/sql/ansi.ColumnDefinition")

_ColumnDefinition_name = (Core.Name "name")

_ColumnDefinition_typeOrDomain = (Core.Name "typeOrDomain")

_ColumnDefinition_refScope = (Core.Name "refScope")

_ColumnDefinition_defaultOrIdentityOrGeneration = (Core.Name "defaultOrIdentityOrGeneration")

_ColumnDefinition_constraints = (Core.Name "constraints")

_ColumnDefinition_collate = (Core.Name "collate")

data ColumnDefinition_TypeOrDomain_Option = 
  ColumnDefinition_TypeOrDomain_OptionDataType DataType |
  ColumnDefinition_TypeOrDomain_OptionDomainName DomainName
  deriving (Eq, Ord, Read, Show)

_ColumnDefinition_TypeOrDomain_Option = (Core.Name "hydra/langs/sql/ansi.ColumnDefinition.TypeOrDomain.Option")

_ColumnDefinition_TypeOrDomain_Option_dataType = (Core.Name "dataType")

_ColumnDefinition_TypeOrDomain_Option_domainName = (Core.Name "domainName")

data ColumnDefinition_DefaultOrIdentityOrGeneration_Option = 
  ColumnDefinition_DefaultOrIdentityOrGeneration_OptionDefaultClause DefaultClause |
  ColumnDefinition_DefaultOrIdentityOrGeneration_OptionIdentityColumnSpecification IdentityColumnSpecification |
  ColumnDefinition_DefaultOrIdentityOrGeneration_OptionGenerationClause GenerationClause
  deriving (Eq, Ord, Read, Show)

_ColumnDefinition_DefaultOrIdentityOrGeneration_Option = (Core.Name "hydra/langs/sql/ansi.ColumnDefinition.DefaultOrIdentityOrGeneration.Option")

_ColumnDefinition_DefaultOrIdentityOrGeneration_Option_defaultClause = (Core.Name "defaultClause")

_ColumnDefinition_DefaultOrIdentityOrGeneration_Option_identityColumnSpecification = (Core.Name "identityColumnSpecification")

_ColumnDefinition_DefaultOrIdentityOrGeneration_Option_generationClause = (Core.Name "generationClause")

data ColumnNameList = 
  ColumnNameList {
    columnNameListFirst :: ColumnName,
    columnNameListRest :: [ColumnName]}
  deriving (Eq, Ord, Read, Show)

_ColumnNameList = (Core.Name "hydra/langs/sql/ansi.ColumnNameList")

_ColumnNameList_first = (Core.Name "first")

_ColumnNameList_rest = (Core.Name "rest")

data ColumnOptions = 
  ColumnOptions {}
  deriving (Eq, Ord, Read, Show)

_ColumnOptions = (Core.Name "hydra/langs/sql/ansi.ColumnOptions")

data ColumnReference = 
  ColumnReference {}
  deriving (Eq, Ord, Read, Show)

_ColumnReference = (Core.Name "hydra/langs/sql/ansi.ColumnReference")

data CommonValueExpression = 
  CommonValueExpressionNumeric NumericValueExpression |
  CommonValueExpressionString StringValueExpression |
  CommonValueExpressionDatetime DatetimeValueExpression |
  CommonValueExpressionInterval IntervalValueExpression |
  CommonValueExpressionUserDefined UserDefinedTypeValueExpression |
  CommonValueExpressionReference ReferenceValueExpression |
  CommonValueExpressionCollection CollectionValueExpression
  deriving (Eq, Ord, Read, Show)

_CommonValueExpression = (Core.Name "hydra/langs/sql/ansi.CommonValueExpression")

_CommonValueExpression_numeric = (Core.Name "numeric")

_CommonValueExpression_string = (Core.Name "string")

_CommonValueExpression_datetime = (Core.Name "datetime")

_CommonValueExpression_interval = (Core.Name "interval")

_CommonValueExpression_userDefined = (Core.Name "userDefined")

_CommonValueExpression_reference = (Core.Name "reference")

_CommonValueExpression_collection = (Core.Name "collection")

data ContextuallyTypedRowValueExpression = 
  ContextuallyTypedRowValueExpressionSpecialCase RowValueSpecialCase |
  ContextuallyTypedRowValueExpressionConstructor ContextuallyTypedRowValueConstructor
  deriving (Eq, Ord, Read, Show)

_ContextuallyTypedRowValueExpression = (Core.Name "hydra/langs/sql/ansi.ContextuallyTypedRowValueExpression")

_ContextuallyTypedRowValueExpression_specialCase = (Core.Name "specialCase")

_ContextuallyTypedRowValueExpression_constructor = (Core.Name "constructor")

data ContextuallyTypedRowValueConstructor = 
  ContextuallyTypedRowValueConstructor {}
  deriving (Eq, Ord, Read, Show)

_ContextuallyTypedRowValueConstructor = (Core.Name "hydra/langs/sql/ansi.ContextuallyTypedRowValueConstructor")

data ContextuallyTypedRowValueExpressionList = 
  ContextuallyTypedRowValueExpressionList {
    contextuallyTypedRowValueExpressionListFirst :: ContextuallyTypedRowValueExpression,
    contextuallyTypedRowValueExpressionListRest :: [ContextuallyTypedRowValueExpression]}
  deriving (Eq, Ord, Read, Show)

_ContextuallyTypedRowValueExpressionList = (Core.Name "hydra/langs/sql/ansi.ContextuallyTypedRowValueExpressionList")

_ContextuallyTypedRowValueExpressionList_first = (Core.Name "first")

_ContextuallyTypedRowValueExpressionList_rest = (Core.Name "rest")

newtype ContextuallyTypedTableValueConstructor = 
  ContextuallyTypedTableValueConstructor {
    unContextuallyTypedTableValueConstructor :: ContextuallyTypedRowValueExpressionList}
  deriving (Eq, Ord, Read, Show)

_ContextuallyTypedTableValueConstructor = (Core.Name "hydra/langs/sql/ansi.ContextuallyTypedTableValueConstructor")

data DataType = 
  DataTypePredefined PredefinedType |
  DataTypeRow RowType |
  DataTypeNamed PathResolvedUserDefinedTypeName |
  DataTypeReference ReferenceType |
  DataTypeCollection CollectionType
  deriving (Eq, Ord, Read, Show)

_DataType = (Core.Name "hydra/langs/sql/ansi.DataType")

_DataType_predefined = (Core.Name "predefined")

_DataType_row = (Core.Name "row")

_DataType_named = (Core.Name "named")

_DataType_reference = (Core.Name "reference")

_DataType_collection = (Core.Name "collection")

newtype DateLiteral = 
  DateLiteral {
    unDateLiteral :: DateString}
  deriving (Eq, Ord, Read, Show)

_DateLiteral = (Core.Name "hydra/langs/sql/ansi.DateLiteral")

data DatetimeLiteral = 
  DatetimeLiteralDate DateLiteral |
  DatetimeLiteralTime TimeLiteral |
  DatetimeLiteralTimestamp TimestampLiteral
  deriving (Eq, Ord, Read, Show)

_DatetimeLiteral = (Core.Name "hydra/langs/sql/ansi.DatetimeLiteral")

_DatetimeLiteral_date = (Core.Name "date")

_DatetimeLiteral_time = (Core.Name "time")

_DatetimeLiteral_timestamp = (Core.Name "timestamp")

data DatetimeType = 
  DatetimeType {}
  deriving (Eq, Ord, Read, Show)

_DatetimeType = (Core.Name "hydra/langs/sql/ansi.DatetimeType")

data DatetimeValueExpression = 
  DatetimeValueExpression {}
  deriving (Eq, Ord, Read, Show)

_DatetimeValueExpression = (Core.Name "hydra/langs/sql/ansi.DatetimeValueExpression")

data DefaultClause = 
  DefaultClause {}
  deriving (Eq, Ord, Read, Show)

_DefaultClause = (Core.Name "hydra/langs/sql/ansi.DefaultClause")

data ExactNumericType = 
  ExactNumericTypeNumeric (Maybe ExactNumericType_Numeric_Option) |
  ExactNumericTypeDecimal (Maybe ExactNumericType_Decimal_Option) |
  ExactNumericTypeDec (Maybe ExactNumericType_Dec_Option) |
  ExactNumericTypeSmallint  |
  ExactNumericTypeInteger  |
  ExactNumericTypeInt  |
  ExactNumericTypeBigint 
  deriving (Eq, Ord, Read, Show)

_ExactNumericType = (Core.Name "hydra/langs/sql/ansi.ExactNumericType")

_ExactNumericType_numeric = (Core.Name "numeric")

_ExactNumericType_decimal = (Core.Name "decimal")

_ExactNumericType_dec = (Core.Name "dec")

_ExactNumericType_smallint = (Core.Name "smallint")

_ExactNumericType_integer = (Core.Name "integer")

_ExactNumericType_int = (Core.Name "int")

_ExactNumericType_bigint = (Core.Name "bigint")

data ExactNumericType_Numeric_Option = 
  ExactNumericType_Numeric_Option {
    exactNumericType_Numeric_OptionPrecision :: Precision,
    exactNumericType_Numeric_OptionSequence :: (Maybe Scale)}
  deriving (Eq, Ord, Read, Show)

_ExactNumericType_Numeric_Option = (Core.Name "hydra/langs/sql/ansi.ExactNumericType.Numeric.Option")

_ExactNumericType_Numeric_Option_precision = (Core.Name "precision")

_ExactNumericType_Numeric_Option_sequence = (Core.Name "sequence")

data ExactNumericType_Decimal_Option = 
  ExactNumericType_Decimal_Option {
    exactNumericType_Decimal_OptionPrecision :: Precision,
    exactNumericType_Decimal_OptionSequence :: (Maybe Scale)}
  deriving (Eq, Ord, Read, Show)

_ExactNumericType_Decimal_Option = (Core.Name "hydra/langs/sql/ansi.ExactNumericType.Decimal.Option")

_ExactNumericType_Decimal_Option_precision = (Core.Name "precision")

_ExactNumericType_Decimal_Option_sequence = (Core.Name "sequence")

data ExactNumericType_Dec_Option = 
  ExactNumericType_Dec_Option {
    exactNumericType_Dec_OptionPrecision :: Precision,
    exactNumericType_Dec_OptionSequence :: (Maybe Scale)}
  deriving (Eq, Ord, Read, Show)

_ExactNumericType_Dec_Option = (Core.Name "hydra/langs/sql/ansi.ExactNumericType.Dec.Option")

_ExactNumericType_Dec_Option_precision = (Core.Name "precision")

_ExactNumericType_Dec_Option_sequence = (Core.Name "sequence")

data FieldReference = 
  FieldReference {}
  deriving (Eq, Ord, Read, Show)

_FieldReference = (Core.Name "hydra/langs/sql/ansi.FieldReference")

data FromConstructor = 
  FromConstructor {
    fromConstructorColumns :: (Maybe InsertColumnList),
    fromConstructorOverride :: (Maybe OverrideClause),
    fromConstructorValues :: ContextuallyTypedTableValueConstructor}
  deriving (Eq, Ord, Read, Show)

_FromConstructor = (Core.Name "hydra/langs/sql/ansi.FromConstructor")

_FromConstructor_columns = (Core.Name "columns")

_FromConstructor_override = (Core.Name "override")

_FromConstructor_values = (Core.Name "values")

data FromDefault = 
  FromDefault {}
  deriving (Eq, Ord, Read, Show)

_FromDefault = (Core.Name "hydra/langs/sql/ansi.FromDefault")

data FromSubquery = 
  FromSubquery {}
  deriving (Eq, Ord, Read, Show)

_FromSubquery = (Core.Name "hydra/langs/sql/ansi.FromSubquery")

data GeneralLiteral = 
  GeneralLiteralString CharacterStringLiteral |
  GeneralLiteralNationalString NationalCharacterStringLiteral |
  GeneralLiteralUnicode UnicodeCharacterStringLiteral |
  GeneralLiteralBinary BinaryStringLiteral |
  GeneralLiteralDateTime DatetimeLiteral |
  GeneralLiteralInterval IntervalLiteral |
  GeneralLiteralBoolean BooleanLiteral
  deriving (Eq, Ord, Read, Show)

_GeneralLiteral = (Core.Name "hydra/langs/sql/ansi.GeneralLiteral")

_GeneralLiteral_string = (Core.Name "string")

_GeneralLiteral_nationalString = (Core.Name "nationalString")

_GeneralLiteral_unicode = (Core.Name "unicode")

_GeneralLiteral_binary = (Core.Name "binary")

_GeneralLiteral_dateTime = (Core.Name "dateTime")

_GeneralLiteral_interval = (Core.Name "interval")

_GeneralLiteral_boolean = (Core.Name "boolean")

data GeneralValueSpecification = 
  GeneralValueSpecification {}
  deriving (Eq, Ord, Read, Show)

_GeneralValueSpecification = (Core.Name "hydra/langs/sql/ansi.GeneralValueSpecification")

data GenerationClause = 
  GenerationClause {}
  deriving (Eq, Ord, Read, Show)

_GenerationClause = (Core.Name "hydra/langs/sql/ansi.GenerationClause")

data GlobalOrLocal = 
  GlobalOrLocalGlobal  |
  GlobalOrLocalLocal 
  deriving (Eq, Ord, Read, Show)

_GlobalOrLocal = (Core.Name "hydra/langs/sql/ansi.GlobalOrLocal")

_GlobalOrLocal_global = (Core.Name "global")

_GlobalOrLocal_local = (Core.Name "local")

data IdentityColumnSpecification = 
  IdentityColumnSpecification {}
  deriving (Eq, Ord, Read, Show)

_IdentityColumnSpecification = (Core.Name "hydra/langs/sql/ansi.IdentityColumnSpecification")

newtype InsertColumnList = 
  InsertColumnList {
    unInsertColumnList :: ColumnNameList}
  deriving (Eq, Ord, Read, Show)

_InsertColumnList = (Core.Name "hydra/langs/sql/ansi.InsertColumnList")

data InsertColumnsAndSource = 
  InsertColumnsAndSourceSubquery FromSubquery |
  InsertColumnsAndSourceConstructor FromConstructor |
  InsertColumnsAndSourceDefault FromDefault
  deriving (Eq, Ord, Read, Show)

_InsertColumnsAndSource = (Core.Name "hydra/langs/sql/ansi.InsertColumnsAndSource")

_InsertColumnsAndSource_subquery = (Core.Name "subquery")

_InsertColumnsAndSource_constructor = (Core.Name "constructor")

_InsertColumnsAndSource_default = (Core.Name "default")

data InsertStatement = 
  InsertStatement {
    insertStatementTarget :: InsertionTarget,
    insertStatementColumnsAndSource :: InsertColumnsAndSource}
  deriving (Eq, Ord, Read, Show)

_InsertStatement = (Core.Name "hydra/langs/sql/ansi.InsertStatement")

_InsertStatement_target = (Core.Name "target")

_InsertStatement_columnsAndSource = (Core.Name "columnsAndSource")

newtype InsertionTarget = 
  InsertionTarget {
    unInsertionTarget :: TableName}
  deriving (Eq, Ord, Read, Show)

_InsertionTarget = (Core.Name "hydra/langs/sql/ansi.InsertionTarget")

data IntervalLiteral = 
  IntervalLiteral {}
  deriving (Eq, Ord, Read, Show)

_IntervalLiteral = (Core.Name "hydra/langs/sql/ansi.IntervalLiteral")

data IntervalType = 
  IntervalType {}
  deriving (Eq, Ord, Read, Show)

_IntervalType = (Core.Name "hydra/langs/sql/ansi.IntervalType")

data IntervalValueExpression = 
  IntervalValueExpression {}
  deriving (Eq, Ord, Read, Show)

_IntervalValueExpression = (Core.Name "hydra/langs/sql/ansi.IntervalValueExpression")

data LargeObjectLength = 
  LargeObjectLength {}
  deriving (Eq, Ord, Read, Show)

_LargeObjectLength = (Core.Name "hydra/langs/sql/ansi.LargeObjectLength")

newtype Length = 
  Length {
    unLength :: UnsignedInteger}
  deriving (Eq, Ord, Read, Show)

_Length = (Core.Name "hydra/langs/sql/ansi.Length")

data LikeClause = 
  LikeClause {}
  deriving (Eq, Ord, Read, Show)

_LikeClause = (Core.Name "hydra/langs/sql/ansi.LikeClause")

data MethodInvocation = 
  MethodInvocation {}
  deriving (Eq, Ord, Read, Show)

_MethodInvocation = (Core.Name "hydra/langs/sql/ansi.MethodInvocation")

data MultisetElementReference = 
  MultisetElementReference {}
  deriving (Eq, Ord, Read, Show)

_MultisetElementReference = (Core.Name "hydra/langs/sql/ansi.MultisetElementReference")

newtype MultisetType = 
  MultisetType {
    unMultisetType :: DataType}
  deriving (Eq, Ord, Read, Show)

_MultisetType = (Core.Name "hydra/langs/sql/ansi.MultisetType")

data MultisetValueConstructor = 
  MultisetValueConstructor {}
  deriving (Eq, Ord, Read, Show)

_MultisetValueConstructor = (Core.Name "hydra/langs/sql/ansi.MultisetValueConstructor")

data MultisetValueExpression = 
  MultisetValueExpression {}
  deriving (Eq, Ord, Read, Show)

_MultisetValueExpression = (Core.Name "hydra/langs/sql/ansi.MultisetValueExpression")

data NationalCharacterStringType = 
  NationalCharacterStringType {}
  deriving (Eq, Ord, Read, Show)

_NationalCharacterStringType = (Core.Name "hydra/langs/sql/ansi.NationalCharacterStringType")

data NewSpecification = 
  NewSpecification {}
  deriving (Eq, Ord, Read, Show)

_NewSpecification = (Core.Name "hydra/langs/sql/ansi.NewSpecification")

data NextValueExpression = 
  NextValueExpression {}
  deriving (Eq, Ord, Read, Show)

_NextValueExpression = (Core.Name "hydra/langs/sql/ansi.NextValueExpression")

data NumericType = 
  NumericTypeExact ExactNumericType |
  NumericTypeApproximate ApproximateNumericType
  deriving (Eq, Ord, Read, Show)

_NumericType = (Core.Name "hydra/langs/sql/ansi.NumericType")

_NumericType_exact = (Core.Name "exact")

_NumericType_approximate = (Core.Name "approximate")

data NumericValueExpression = 
  NumericValueExpression {}
  deriving (Eq, Ord, Read, Show)

_NumericValueExpression = (Core.Name "hydra/langs/sql/ansi.NumericValueExpression")

data OverrideClause = 
  OverrideClauseOVERRIDINGSpUSERSpVALUE  |
  OverrideClauseOVERRIDINGSpSYSTEMSpVALUE 
  deriving (Eq, Ord, Read, Show)

_OverrideClause = (Core.Name "hydra/langs/sql/ansi.OverrideClause")

_OverrideClause_oVERRIDINGSpUSERSpVALUE = (Core.Name "oVERRIDINGSpUSERSpVALUE")

_OverrideClause_oVERRIDINGSpSYSTEMSpVALUE = (Core.Name "oVERRIDINGSpSYSTEMSpVALUE")

newtype ParenthesizedValueExpression = 
  ParenthesizedValueExpression {
    unParenthesizedValueExpression :: ValueExpression}
  deriving (Eq, Ord, Read, Show)

_ParenthesizedValueExpression = (Core.Name "hydra/langs/sql/ansi.ParenthesizedValueExpression")

newtype Precision = 
  Precision {
    unPrecision :: UnsignedInteger}
  deriving (Eq, Ord, Read, Show)

_Precision = (Core.Name "hydra/langs/sql/ansi.Precision")

data PredefinedType = 
  PredefinedTypeString PredefinedType_String |
  PredefinedTypeNationalString PredefinedType_NationalString |
  PredefinedTypeBlob BinaryLargeObjectStringType |
  PredefinedTypeNumeric NumericType |
  PredefinedTypeBoolean BooleanType |
  PredefinedTypeDatetime DatetimeType |
  PredefinedTypeInterval IntervalType
  deriving (Eq, Ord, Read, Show)

_PredefinedType = (Core.Name "hydra/langs/sql/ansi.PredefinedType")

_PredefinedType_string = (Core.Name "string")

_PredefinedType_nationalString = (Core.Name "nationalString")

_PredefinedType_blob = (Core.Name "blob")

_PredefinedType_numeric = (Core.Name "numeric")

_PredefinedType_boolean = (Core.Name "boolean")

_PredefinedType_datetime = (Core.Name "datetime")

_PredefinedType_interval = (Core.Name "interval")

data PredefinedType_String = 
  PredefinedType_String {
    predefinedType_StringType :: CharacterStringType,
    predefinedType_StringCharacters :: (Maybe CharacterSetSpecification),
    predefinedType_StringCollate :: (Maybe CollateClause)}
  deriving (Eq, Ord, Read, Show)

_PredefinedType_String = (Core.Name "hydra/langs/sql/ansi.PredefinedType.String")

_PredefinedType_String_type = (Core.Name "type")

_PredefinedType_String_characters = (Core.Name "characters")

_PredefinedType_String_collate = (Core.Name "collate")

data PredefinedType_NationalString = 
  PredefinedType_NationalString {
    predefinedType_NationalStringType :: NationalCharacterStringType,
    predefinedType_NationalStringCollate :: (Maybe CollateClause)}
  deriving (Eq, Ord, Read, Show)

_PredefinedType_NationalString = (Core.Name "hydra/langs/sql/ansi.PredefinedType.NationalString")

_PredefinedType_NationalString_type = (Core.Name "type")

_PredefinedType_NationalString_collate = (Core.Name "collate")

data Predicate = 
  Predicate {}
  deriving (Eq, Ord, Read, Show)

_Predicate = (Core.Name "hydra/langs/sql/ansi.Predicate")

data QueryExpression = 
  QueryExpression {}
  deriving (Eq, Ord, Read, Show)

_QueryExpression = (Core.Name "hydra/langs/sql/ansi.QueryExpression")

data ReferenceScopeCheck = 
  ReferenceScopeCheck {}
  deriving (Eq, Ord, Read, Show)

_ReferenceScopeCheck = (Core.Name "hydra/langs/sql/ansi.ReferenceScopeCheck")

data ReferenceType = 
  ReferenceType {}
  deriving (Eq, Ord, Read, Show)

_ReferenceType = (Core.Name "hydra/langs/sql/ansi.ReferenceType")

data RowType = 
  RowType {}
  deriving (Eq, Ord, Read, Show)

_RowType = (Core.Name "hydra/langs/sql/ansi.RowType")

newtype RowValueSpecialCase = 
  RowValueSpecialCase {
    unRowValueSpecialCase :: NonparenthesizedValueExpressionPrimary}
  deriving (Eq, Ord, Read, Show)

_RowValueSpecialCase = (Core.Name "hydra/langs/sql/ansi.RowValueSpecialCase")

data NonparenthesizedValueExpressionPrimary = 
  NonparenthesizedValueExpressionPrimaryUnsigned UnsignedValueSpecification |
  NonparenthesizedValueExpressionPrimaryColumn ColumnReference |
  NonparenthesizedValueExpressionPrimarySetFunction SetFunctionSpecification |
  NonparenthesizedValueExpressionPrimaryWindowFunction WindowFunction |
  NonparenthesizedValueExpressionPrimaryScalarSubquery ScalarSubquery |
  NonparenthesizedValueExpressionPrimaryCases CaseExpression |
  NonparenthesizedValueExpressionPrimaryCast CastSpecification |
  NonparenthesizedValueExpressionPrimaryField FieldReference |
  NonparenthesizedValueExpressionPrimarySubtype SubtypeTreatment |
  NonparenthesizedValueExpressionPrimaryMethod MethodInvocation |
  NonparenthesizedValueExpressionPrimaryStaticMethod StaticMethodInvocation |
  NonparenthesizedValueExpressionPrimaryNew NewSpecification |
  NonparenthesizedValueExpressionPrimaryAttributeOrMethod AttributeOrMethodReference |
  NonparenthesizedValueExpressionPrimaryReference ReferenceResolution |
  NonparenthesizedValueExpressionPrimaryCollection CollectionValueConstructor |
  NonparenthesizedValueExpressionPrimaryArrayElement ArrayElementReference |
  NonparenthesizedValueExpressionPrimaryMultisetElement MultisetElementReference |
  NonparenthesizedValueExpressionPrimaryRoutine RoutineInvocation |
  NonparenthesizedValueExpressionPrimaryNext NextValueExpression
  deriving (Eq, Ord, Read, Show)

_NonparenthesizedValueExpressionPrimary = (Core.Name "hydra/langs/sql/ansi.NonparenthesizedValueExpressionPrimary")

_NonparenthesizedValueExpressionPrimary_unsigned = (Core.Name "unsigned")

_NonparenthesizedValueExpressionPrimary_column = (Core.Name "column")

_NonparenthesizedValueExpressionPrimary_setFunction = (Core.Name "setFunction")

_NonparenthesizedValueExpressionPrimary_windowFunction = (Core.Name "windowFunction")

_NonparenthesizedValueExpressionPrimary_scalarSubquery = (Core.Name "scalarSubquery")

_NonparenthesizedValueExpressionPrimary_cases = (Core.Name "cases")

_NonparenthesizedValueExpressionPrimary_cast = (Core.Name "cast")

_NonparenthesizedValueExpressionPrimary_field = (Core.Name "field")

_NonparenthesizedValueExpressionPrimary_subtype = (Core.Name "subtype")

_NonparenthesizedValueExpressionPrimary_method = (Core.Name "method")

_NonparenthesizedValueExpressionPrimary_staticMethod = (Core.Name "staticMethod")

_NonparenthesizedValueExpressionPrimary_new = (Core.Name "new")

_NonparenthesizedValueExpressionPrimary_attributeOrMethod = (Core.Name "attributeOrMethod")

_NonparenthesizedValueExpressionPrimary_reference = (Core.Name "reference")

_NonparenthesizedValueExpressionPrimary_collection = (Core.Name "collection")

_NonparenthesizedValueExpressionPrimary_arrayElement = (Core.Name "arrayElement")

_NonparenthesizedValueExpressionPrimary_multisetElement = (Core.Name "multisetElement")

_NonparenthesizedValueExpressionPrimary_routine = (Core.Name "routine")

_NonparenthesizedValueExpressionPrimary_next = (Core.Name "next")

data ReferenceResolution = 
  ReferenceResolution {}
  deriving (Eq, Ord, Read, Show)

_ReferenceResolution = (Core.Name "hydra/langs/sql/ansi.ReferenceResolution")

newtype ReferenceValueExpression = 
  ReferenceValueExpression {
    unReferenceValueExpression :: ValueExpressionPrimary}
  deriving (Eq, Ord, Read, Show)

_ReferenceValueExpression = (Core.Name "hydra/langs/sql/ansi.ReferenceValueExpression")

data RowValueExpression = 
  RowValueExpression {}
  deriving (Eq, Ord, Read, Show)

_RowValueExpression = (Core.Name "hydra/langs/sql/ansi.RowValueExpression")

data RoutineInvocation = 
  RoutineInvocation {}
  deriving (Eq, Ord, Read, Show)

_RoutineInvocation = (Core.Name "hydra/langs/sql/ansi.RoutineInvocation")

newtype ScalarSubquery = 
  ScalarSubquery {
    unScalarSubquery :: Subquery}
  deriving (Eq, Ord, Read, Show)

_ScalarSubquery = (Core.Name "hydra/langs/sql/ansi.ScalarSubquery")

newtype Scale = 
  Scale {
    unScale :: UnsignedInteger}
  deriving (Eq, Ord, Read, Show)

_Scale = (Core.Name "hydra/langs/sql/ansi.Scale")

data SelfReferencingColumnSpecification = 
  SelfReferencingColumnSpecification {}
  deriving (Eq, Ord, Read, Show)

_SelfReferencingColumnSpecification = (Core.Name "hydra/langs/sql/ansi.SelfReferencingColumnSpecification")

data SetFunctionSpecification = 
  SetFunctionSpecification {}
  deriving (Eq, Ord, Read, Show)

_SetFunctionSpecification = (Core.Name "hydra/langs/sql/ansi.SetFunctionSpecification")

data StaticMethodInvocation = 
  StaticMethodInvocation {}
  deriving (Eq, Ord, Read, Show)

_StaticMethodInvocation = (Core.Name "hydra/langs/sql/ansi.StaticMethodInvocation")

data StringValueExpression = 
  StringValueExpression {}
  deriving (Eq, Ord, Read, Show)

_StringValueExpression = (Core.Name "hydra/langs/sql/ansi.StringValueExpression")

newtype Subquery = 
  Subquery {
    unSubquery :: QueryExpression}
  deriving (Eq, Ord, Read, Show)

_Subquery = (Core.Name "hydra/langs/sql/ansi.Subquery")

data SubtableClause = 
  SubtableClause {}
  deriving (Eq, Ord, Read, Show)

_SubtableClause = (Core.Name "hydra/langs/sql/ansi.SubtableClause")

data SubtypeTreatment = 
  SubtypeTreatment {}
  deriving (Eq, Ord, Read, Show)

_SubtypeTreatment = (Core.Name "hydra/langs/sql/ansi.SubtypeTreatment")

data TableCommitAction = 
  TableCommitActionPreserve  |
  TableCommitActionDelete 
  deriving (Eq, Ord, Read, Show)

_TableCommitAction = (Core.Name "hydra/langs/sql/ansi.TableCommitAction")

_TableCommitAction_preserve = (Core.Name "preserve")

_TableCommitAction_delete = (Core.Name "delete")

data TableConstraintDefinition = 
  TableConstraintDefinition {}
  deriving (Eq, Ord, Read, Show)

_TableConstraintDefinition = (Core.Name "hydra/langs/sql/ansi.TableConstraintDefinition")

data TableContentsSource = 
  TableContentsSourceList TableElementList |
  TableContentsSourceSubtable TableContentsSource_Subtable |
  TableContentsSourceSubquery AsSubqueryClause
  deriving (Eq, Ord, Read, Show)

_TableContentsSource = (Core.Name "hydra/langs/sql/ansi.TableContentsSource")

_TableContentsSource_list = (Core.Name "list")

_TableContentsSource_subtable = (Core.Name "subtable")

_TableContentsSource_subquery = (Core.Name "subquery")

data TableContentsSource_Subtable = 
  TableContentsSource_Subtable {
    tableContentsSource_SubtableType :: PathResolvedUserDefinedTypeName,
    tableContentsSource_SubtableSubtable :: (Maybe SubtableClause),
    tableContentsSource_SubtableElements :: (Maybe TableElementList)}
  deriving (Eq, Ord, Read, Show)

_TableContentsSource_Subtable = (Core.Name "hydra/langs/sql/ansi.TableContentsSource.Subtable")

_TableContentsSource_Subtable_type = (Core.Name "type")

_TableContentsSource_Subtable_subtable = (Core.Name "subtable")

_TableContentsSource_Subtable_elements = (Core.Name "elements")

data TableDefinition = 
  TableDefinition {
    tableDefinitionScope :: (Maybe TableScope),
    tableDefinitionName :: TableName,
    tableDefinitionSource :: TableContentsSource,
    tableDefinitionCommitActions :: (Maybe TableCommitAction)}
  deriving (Eq, Ord, Read, Show)

_TableDefinition = (Core.Name "hydra/langs/sql/ansi.TableDefinition")

_TableDefinition_scope = (Core.Name "scope")

_TableDefinition_name = (Core.Name "name")

_TableDefinition_source = (Core.Name "source")

_TableDefinition_commitActions = (Core.Name "commitActions")

data TableElement = 
  TableElementColumn ColumnDefinition |
  TableElementTableConstraint TableConstraintDefinition |
  TableElementLike LikeClause |
  TableElementSelfReferencingColumn SelfReferencingColumnSpecification |
  TableElementColumOptions ColumnOptions
  deriving (Eq, Ord, Read, Show)

_TableElement = (Core.Name "hydra/langs/sql/ansi.TableElement")

_TableElement_column = (Core.Name "column")

_TableElement_tableConstraint = (Core.Name "tableConstraint")

_TableElement_like = (Core.Name "like")

_TableElement_selfReferencingColumn = (Core.Name "selfReferencingColumn")

_TableElement_columOptions = (Core.Name "columOptions")

data TableElementList = 
  TableElementList {
    tableElementListFirst :: TableElement,
    tableElementListRest :: [TableElement]}
  deriving (Eq, Ord, Read, Show)

_TableElementList = (Core.Name "hydra/langs/sql/ansi.TableElementList")

_TableElementList_first = (Core.Name "first")

_TableElementList_rest = (Core.Name "rest")

newtype TableScope = 
  TableScope {
    unTableScope :: GlobalOrLocal}
  deriving (Eq, Ord, Read, Show)

_TableScope = (Core.Name "hydra/langs/sql/ansi.TableScope")

newtype TimeLiteral = 
  TimeLiteral {
    unTimeLiteral :: TimeString}
  deriving (Eq, Ord, Read, Show)

_TimeLiteral = (Core.Name "hydra/langs/sql/ansi.TimeLiteral")

data TruthValue = 
  TruthValueTRUE  |
  TruthValueFALSE  |
  TruthValueUNKNOWN 
  deriving (Eq, Ord, Read, Show)

_TruthValue = (Core.Name "hydra/langs/sql/ansi.TruthValue")

_TruthValue_tRUE = (Core.Name "tRUE")

_TruthValue_fALSE = (Core.Name "fALSE")

_TruthValue_uNKNOWN = (Core.Name "uNKNOWN")

data UnsignedLiteral = 
  UnsignedLiteralNumeric UnsignedNumericLiteral |
  UnsignedLiteralGeneral GeneralLiteral
  deriving (Eq, Ord, Read, Show)

_UnsignedLiteral = (Core.Name "hydra/langs/sql/ansi.UnsignedLiteral")

_UnsignedLiteral_numeric = (Core.Name "numeric")

_UnsignedLiteral_general = (Core.Name "general")

data UnsignedNumericLiteral = 
  UnsignedNumericLiteralExact ExactNumericLiteral |
  UnsignedNumericLiteralApproximate ApproximateNumericLiteral
  deriving (Eq, Ord, Read, Show)

_UnsignedNumericLiteral = (Core.Name "hydra/langs/sql/ansi.UnsignedNumericLiteral")

_UnsignedNumericLiteral_exact = (Core.Name "exact")

_UnsignedNumericLiteral_approximate = (Core.Name "approximate")

data UnsignedValueSpecification = 
  UnsignedValueSpecificationLiteral UnsignedLiteral |
  UnsignedValueSpecificationGeneral GeneralValueSpecification
  deriving (Eq, Ord, Read, Show)

_UnsignedValueSpecification = (Core.Name "hydra/langs/sql/ansi.UnsignedValueSpecification")

_UnsignedValueSpecification_literal = (Core.Name "literal")

_UnsignedValueSpecification_general = (Core.Name "general")

newtype UserDefinedTypeValueExpression = 
  UserDefinedTypeValueExpression {
    unUserDefinedTypeValueExpression :: ValueExpressionPrimary}
  deriving (Eq, Ord, Read, Show)

_UserDefinedTypeValueExpression = (Core.Name "hydra/langs/sql/ansi.UserDefinedTypeValueExpression")

data ValueExpression = 
  ValueExpressionCommon CommonValueExpression |
  ValueExpressionBoolean BooleanValueExpression |
  ValueExpressionRow RowValueExpression
  deriving (Eq, Ord, Read, Show)

_ValueExpression = (Core.Name "hydra/langs/sql/ansi.ValueExpression")

_ValueExpression_common = (Core.Name "common")

_ValueExpression_boolean = (Core.Name "boolean")

_ValueExpression_row = (Core.Name "row")

data ValueExpressionPrimary = 
  ValueExpressionPrimaryParens ParenthesizedValueExpression |
  ValueExpressionPrimaryNoparens NonparenthesizedValueExpressionPrimary
  deriving (Eq, Ord, Read, Show)

_ValueExpressionPrimary = (Core.Name "hydra/langs/sql/ansi.ValueExpressionPrimary")

_ValueExpressionPrimary_parens = (Core.Name "parens")

_ValueExpressionPrimary_noparens = (Core.Name "noparens")

data WindowFunction = 
  WindowFunction {}
  deriving (Eq, Ord, Read, Show)

_WindowFunction = (Core.Name "hydra/langs/sql/ansi.WindowFunction")
