-- | Hydra's core data model, defining types, terms, and their dependencies

module Hydra.Core where

import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An object, such as a type or term, together with an annotation
data Annotated x a = 
  Annotated {
    annotatedSubject :: x,
    annotatedAnnotation :: a}
  deriving (Eq, Ord, Read, Show)

_Annotated = (Name "hydra/core.Annotated")

_Annotated_subject = (FieldName "subject")

_Annotated_annotation = (FieldName "annotation")

-- | A term which applies a function to an argument
data Application a = 
  Application {
    -- | The left-hand side of the application
    applicationFunction :: (Term),
    -- | The right-hand side of the application
    applicationArgument :: (Term)}
  deriving (Eq, Ord, Read, Show)

_Application = (Name "hydra/core.Application")

_Application_function = (FieldName "function")

_Application_argument = (FieldName "argument")

-- | The type-level analog of an application term
data ApplicationType =
  ApplicationType {
    -- | The left-hand side of the application
    applicationTypeFunction :: (Type),
    -- | The right-hand side of the application
    applicationTypeArgument :: (Type)}
  deriving (Eq, Ord, Read, Show)

_ApplicationType = (Name "hydra/core.ApplicationType")

_ApplicationType_function = (FieldName "function")

_ApplicationType_argument = (FieldName "argument")

-- | A union elimination; a case statement
data CaseStatement a = 
  CaseStatement {
    caseStatementTypeName :: Name,
    caseStatementDefault :: (Maybe (Term)),
    caseStatementCases :: [Field Kv]}
  deriving (Eq, Ord, Read, Show)

_CaseStatement = (Name "hydra/core.CaseStatement")

_CaseStatement_typeName = (FieldName "typeName")

_CaseStatement_default = (FieldName "default")

_CaseStatement_cases = (FieldName "cases")

-- | A corresponding elimination for an introduction term
data Elimination a = 
  -- | Eliminates a list using a fold function; this function has the signature b -> [a] -> b
  EliminationList (Term) |
  -- | Eliminates an optional term by matching over the two possible cases
  EliminationOptional (OptionalCases Kv) |
  -- | Eliminates a tuple by projecting the component at a given 0-indexed offset
  EliminationProduct TupleProjection |
  -- | Eliminates a record by projecting a given field
  EliminationRecord Projection |
  -- | Eliminates a union term by matching over the fields of the union. This is a case statement.
  EliminationUnion (CaseStatement Kv) |
  -- | Unwrap a wrapped term
  EliminationWrap Name
  deriving (Eq, Ord, Read, Show)

_Elimination = (Name "hydra/core.Elimination")

_Elimination_list = (FieldName "list")

_Elimination_optional = (FieldName "optional")

_Elimination_product = (FieldName "product")

_Elimination_record = (FieldName "record")

_Elimination_union = (FieldName "union")

_Elimination_wrap = (FieldName "wrap")

-- | A labeled term
data Field a = 
  Field {
    fieldName :: FieldName,
    fieldTerm :: (Term)}
  deriving (Eq, Ord, Read, Show)

_Field = (Name "hydra/core.Field")

_Field_name = (FieldName "name")

_Field_term = (FieldName "term")

-- | The name of a field, unique within a record or union type
newtype FieldName = 
  FieldName {
    unFieldName :: String}
  deriving (Eq, Ord, Read, Show)

_FieldName = (Name "hydra/core.FieldName")

-- | The name and type of a field
data FieldType =
  FieldType {
    fieldTypeName :: FieldName,
    fieldTypeType :: (Type)}
  deriving (Eq, Ord, Read, Show)

_FieldType = (Name "hydra/core.FieldType")

_FieldType_name = (FieldName "name")

_FieldType_type = (FieldName "type")

-- | A floating-point type
data FloatType = 
  FloatTypeBigfloat  |
  FloatTypeFloat32  |
  FloatTypeFloat64 
  deriving (Eq, Ord, Read, Show)

_FloatType = (Name "hydra/core.FloatType")

_FloatType_bigfloat = (FieldName "bigfloat")

_FloatType_float32 = (FieldName "float32")

_FloatType_float64 = (FieldName "float64")

-- | A floating-point literal value
data FloatValue = 
  -- | An arbitrary-precision floating-point value
  FloatValueBigfloat Double |
  -- | A 32-bit floating-point value
  FloatValueFloat32 Float |
  -- | A 64-bit floating-point value
  FloatValueFloat64 Double
  deriving (Eq, Ord, Read, Show)

_FloatValue = (Name "hydra/core.FloatValue")

_FloatValue_bigfloat = (FieldName "bigfloat")

_FloatValue_float32 = (FieldName "float32")

_FloatValue_float64 = (FieldName "float64")

-- | A function
data Function a = 
  -- | An elimination for any of a few term variants
  FunctionElimination (Elimination Kv) |
  -- | A function abstraction (lambda)
  FunctionLambda (Lambda Kv) |
  -- | A reference to a built-in (primitive) function
  FunctionPrimitive Name
  deriving (Eq, Ord, Read, Show)

_Function = (Name "hydra/core.Function")

_Function_elimination = (FieldName "elimination")

_Function_lambda = (FieldName "lambda")

_Function_primitive = (FieldName "primitive")

-- | A function type, also known as an arrow type
data FunctionType =
  FunctionType {
    functionTypeDomain :: (Type),
    functionTypeCodomain :: (Type)}
  deriving (Eq, Ord, Read, Show)

_FunctionType = (Name "hydra/core.FunctionType")

_FunctionType_domain = (FieldName "domain")

_FunctionType_codomain = (FieldName "codomain")

-- | An instance of a union type; i.e. a string-indexed generalization of inl() or inr()
data Injection a = 
  Injection {
    injectionTypeName :: Name,
    injectionField :: (Field Kv)}
  deriving (Eq, Ord, Read, Show)

_Injection = (Name "hydra/core.Injection")

_Injection_typeName = (FieldName "typeName")

_Injection_field = (FieldName "field")

-- | An integer type
data IntegerType = 
  IntegerTypeBigint  |
  IntegerTypeInt8  |
  IntegerTypeInt16  |
  IntegerTypeInt32  |
  IntegerTypeInt64  |
  IntegerTypeUint8  |
  IntegerTypeUint16  |
  IntegerTypeUint32  |
  IntegerTypeUint64 
  deriving (Eq, Ord, Read, Show)

_IntegerType = (Name "hydra/core.IntegerType")

_IntegerType_bigint = (FieldName "bigint")

_IntegerType_int8 = (FieldName "int8")

_IntegerType_int16 = (FieldName "int16")

_IntegerType_int32 = (FieldName "int32")

_IntegerType_int64 = (FieldName "int64")

_IntegerType_uint8 = (FieldName "uint8")

_IntegerType_uint16 = (FieldName "uint16")

_IntegerType_uint32 = (FieldName "uint32")

_IntegerType_uint64 = (FieldName "uint64")

-- | An integer literal value
data IntegerValue = 
  -- | An arbitrary-precision integer value
  IntegerValueBigint Integer |
  -- | An 8-bit signed integer value
  IntegerValueInt8 Int8 |
  -- | A 16-bit signed integer value (short value)
  IntegerValueInt16 Int16 |
  -- | A 32-bit signed integer value (int value)
  IntegerValueInt32 Int |
  -- | A 64-bit signed integer value (long value)
  IntegerValueInt64 Int64 |
  -- | An 8-bit unsigned integer value (byte)
  IntegerValueUint8 Int16 |
  -- | A 16-bit unsigned integer value
  IntegerValueUint16 Int |
  -- | A 32-bit unsigned integer value (unsigned int)
  IntegerValueUint32 Int64 |
  -- | A 64-bit unsigned integer value (unsigned long)
  IntegerValueUint64 Integer
  deriving (Eq, Ord, Read, Show)

_IntegerValue = (Name "hydra/core.IntegerValue")

_IntegerValue_bigint = (FieldName "bigint")

_IntegerValue_int8 = (FieldName "int8")

_IntegerValue_int16 = (FieldName "int16")

_IntegerValue_int32 = (FieldName "int32")

_IntegerValue_int64 = (FieldName "int64")

_IntegerValue_uint8 = (FieldName "uint8")

_IntegerValue_uint16 = (FieldName "uint16")

_IntegerValue_uint32 = (FieldName "uint32")

_IntegerValue_uint64 = (FieldName "uint64")

-- | A key/value map which serves as a built-in metadata container for terms
data Kv = 
  Kv {
    -- | A map of annotation names to annotation values
    kvAnnotations :: (Map String (Term))}
  deriving (Eq, Ord, Read, Show)

_Kv = (Name "hydra/core.Kv")

_Kv_annotations = (FieldName "annotations")

-- | A function abstraction (lambda)
data Lambda a = 
  Lambda {
    -- | The parameter of the lambda
    lambdaParameter :: Name,
    -- | The body of the lambda
    lambdaBody :: (Term)}
  deriving (Eq, Ord, Read, Show)

_Lambda = (Name "hydra/core.Lambda")

_Lambda_parameter = (FieldName "parameter")

_Lambda_body = (FieldName "body")

-- | A type abstraction; the type-level analog of a lambda term
data LambdaType =
  LambdaType {
    -- | The variable which is bound by the lambda
    lambdaTypeParameter :: Name,
    -- | The body of the lambda
    lambdaTypeBody :: (Type)}
  deriving (Eq, Ord, Read, Show)

_LambdaType = (Name "hydra/core.LambdaType")

_LambdaType_parameter = (FieldName "parameter")

_LambdaType_body = (FieldName "body")

-- | A set of (possibly recursive) 'let' bindings
data Let a = 
  Let {
    letBindings :: (Map Name (Term)),
    letEnvironment :: (Term)}
  deriving (Eq, Ord, Read, Show)

_Let = (Name "hydra/core.Let")

_Let_bindings = (FieldName "bindings")

_Let_environment = (FieldName "environment")

-- | A term constant; an instance of a literal type
data Literal = 
  -- | A binary literal
  LiteralBinary String |
  -- | A boolean literal
  LiteralBoolean Bool |
  -- | A floating-point literal
  LiteralFloat FloatValue |
  -- | An integer literal
  LiteralInteger IntegerValue |
  -- | A string literal
  LiteralString String
  deriving (Eq, Ord, Read, Show)

_Literal = (Name "hydra/core.Literal")

_Literal_binary = (FieldName "binary")

_Literal_boolean = (FieldName "boolean")

_Literal_float = (FieldName "float")

_Literal_integer = (FieldName "integer")

_Literal_string = (FieldName "string")

-- | Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants
data LiteralType = 
  LiteralTypeBinary  |
  LiteralTypeBoolean  |
  LiteralTypeFloat FloatType |
  LiteralTypeInteger IntegerType |
  LiteralTypeString 
  deriving (Eq, Ord, Read, Show)

_LiteralType = (Name "hydra/core.LiteralType")

_LiteralType_binary = (FieldName "binary")

_LiteralType_boolean = (FieldName "boolean")

_LiteralType_float = (FieldName "float")

_LiteralType_integer = (FieldName "integer")

_LiteralType_string = (FieldName "string")

-- | A map type
data MapType =
  MapType {
    mapTypeKeys :: (Type),
    mapTypeValues :: (Type)}
  deriving (Eq, Ord, Read, Show)

_MapType = (Name "hydra/core.MapType")

_MapType_keys = (FieldName "keys")

_MapType_values = (FieldName "values")

-- | A symbol which stands for a term, type, or element
newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Name "hydra/core.Name")

-- | An object wrapped in a type name
data Nominal x = 
  Nominal {
    nominalTypeName :: Name,
    nominalObject :: x}
  deriving (Eq, Ord, Read, Show)

_Nominal = (Name "hydra/core.Nominal")

_Nominal_typeName = (FieldName "typeName")

_Nominal_object = (FieldName "object")

-- | A case statement for matching optional terms
data OptionalCases a = 
  OptionalCases {
    -- | A term provided if the optional value is nothing
    optionalCasesNothing :: (Term),
    -- | A function which is applied if the optional value is non-nothing
    optionalCasesJust :: (Term)}
  deriving (Eq, Ord, Read, Show)

_OptionalCases = (Name "hydra/core.OptionalCases")

_OptionalCases_nothing = (FieldName "nothing")

_OptionalCases_just = (FieldName "just")

-- | A record elimination; a projection
data Projection = 
  Projection {
    projectionTypeName :: Name,
    projectionField :: FieldName}
  deriving (Eq, Ord, Read, Show)

_Projection = (Name "hydra/core.Projection")

_Projection_typeName = (FieldName "typeName")

_Projection_field = (FieldName "field")

-- | A record, or labeled tuple; a map of field names to terms
data Record a = 
  Record {
    recordTypeName :: Name,
    recordFields :: [Field Kv]}
  deriving (Eq, Ord, Read, Show)

_Record = (Name "hydra/core.Record")

_Record_typeName = (FieldName "typeName")

_Record_fields = (FieldName "fields")

-- | A labeled record or union type
data RowType =
  RowType {
    -- | The name of the row type, which must correspond to the name of a Type element
    rowTypeTypeName :: Name,
    -- | Optionally, the name of another row type which this one extends. If/when field order is preserved, the inherited fields of the extended type precede those of the extension.
    rowTypeExtends :: (Maybe Name),
    -- | The fields of this row type, excluding any inherited fields
    rowTypeFields :: [FieldType]}
  deriving (Eq, Ord, Read, Show)

_RowType = (Name "hydra/core.RowType")

_RowType_typeName = (FieldName "typeName")

_RowType_extends = (FieldName "extends")

_RowType_fields = (FieldName "fields")

-- | An infinite stream of terms
data Stream a = 
  Stream {
    streamFirst :: (Term),
    streamRest :: (Stream a)}
  deriving (Eq, Ord, Read, Show)

_Stream = (Name "hydra/core.Stream")

_Stream_first = (FieldName "first")

_Stream_rest = (FieldName "rest")

-- | The unlabeled equivalent of an Injection term
data Sum a = 
  Sum {
    sumIndex :: Int,
    sumSize :: Int,
    sumTerm :: (Term)}
  deriving (Eq, Ord, Read, Show)

_Sum = (Name "hydra/core.Sum")

_Sum_index = (FieldName "index")

_Sum_size = (FieldName "size")

_Sum_term = (FieldName "term")

-- | A data term
data Term =
  -- | A term annotated with metadata
  TermAnnotated (Annotated (Term) Kv) |
  -- | A function application
  TermApplication (Application Kv) |
  -- | A function term
  TermFunction (Function Kv) |
  TermLet (Let Kv) |
  -- | A list
  TermList [Term] |
  -- | A literal value
  TermLiteral Literal |
  -- | A map of keys to values
  TermMap (Map (Term) (Term)) |
  -- | An optional value
  TermOptional (Maybe (Term)) |
  -- | A tuple
  TermProduct [Term] |
  -- | A record term
  TermRecord (Record Kv) |
  -- | A set of values
  TermSet (Set (Term)) |
  -- | An infinite stream of terms
  TermStream (Stream Kv) |
  -- | A variant tuple
  TermSum (Sum Kv) |
  -- | An injection; an instance of a union type
  TermUnion (Injection Kv) |
  -- | A variable reference
  TermVariable Name |
  TermWrap (Nominal (Term))
  deriving (Eq, Ord, Read, Show)

_Term = (Name "hydra/core.Term")

_Term_annotated = (FieldName "annotated")

_Term_application = (FieldName "application")

_Term_function = (FieldName "function")

_Term_let = (FieldName "let")

_Term_list = (FieldName "list")

_Term_literal = (FieldName "literal")

_Term_map = (FieldName "map")

_Term_optional = (FieldName "optional")

_Term_product = (FieldName "product")

_Term_record = (FieldName "record")

_Term_set = (FieldName "set")

_Term_stream = (FieldName "stream")

_Term_sum = (FieldName "sum")

_Term_union = (FieldName "union")

_Term_variable = (FieldName "variable")

_Term_wrap = (FieldName "wrap")

-- | A tuple elimination; a projection from an integer-indexed product
data TupleProjection = 
  TupleProjection {
    -- | The arity of the tuple
    tupleProjectionArity :: Int,
    -- | The 0-indexed offset from the beginning of the tuple
    tupleProjectionIndex :: Int}
  deriving (Eq, Ord, Read, Show)

_TupleProjection = (Name "hydra/core.TupleProjection")

_TupleProjection_arity = (FieldName "arity")

_TupleProjection_index = (FieldName "index")

-- | A data type
data Type =
  -- | A type annotated with metadata
  TypeAnnotated (Annotated (Type) Kv) |
  TypeApplication (ApplicationType) |
  TypeFunction (FunctionType) |
  TypeLambda (LambdaType) |
  TypeList (Type) |
  TypeLiteral LiteralType |
  TypeMap (MapType) |
  TypeOptional (Type) |
  TypeProduct [Type] |
  TypeRecord (RowType) |
  TypeSet (Type) |
  TypeStream (Type) |
  TypeSum [Type] |
  TypeUnion (RowType) |
  TypeVariable Name |
  TypeWrap (Nominal (Type))
  deriving (Eq, Ord, Read, Show)

_Type = (Name "hydra/core.Type")

_Type_annotated = (FieldName "annotated")

_Type_application = (FieldName "application")

_Type_function = (FieldName "function")

_Type_lambda = (FieldName "lambda")

_Type_list = (FieldName "list")

_Type_literal = (FieldName "literal")

_Type_map = (FieldName "map")

_Type_optional = (FieldName "optional")

_Type_product = (FieldName "product")

_Type_record = (FieldName "record")

_Type_set = (FieldName "set")

_Type_stream = (FieldName "stream")

_Type_sum = (FieldName "sum")

_Type_union = (FieldName "union")

_Type_variable = (FieldName "variable")

_Type_wrap = (FieldName "wrap")

-- | An empty record type as a canonical unit type
data UnitType = 
  UnitType {}
  deriving (Eq, Ord, Read, Show)

_UnitType = (Name "hydra/core.UnitType")
