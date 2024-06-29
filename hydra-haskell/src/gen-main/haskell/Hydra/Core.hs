-- | Hydra's core data model, defining types, terms, and their dependencies

module Hydra.Core where

import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An object, such as a type or term, together with an annotation
data Annotated a = 
  Annotated {
    annotatedSubject :: a,
    annotatedAnnotation :: Map String Term}
  deriving (Eq, Ord, Read, Show)

_Annotated = (Name "hydra/core.Annotated")

_Annotated_subject = (Name "subject")

_Annotated_annotation = (Name "annotation")

-- | A term which applies a function to an argument
data Application = 
  Application {
    -- | The left-hand side of the application
    applicationFunction :: Term,
    -- | The right-hand side of the application
    applicationArgument :: Term}
  deriving (Eq, Ord, Read, Show)

_Application = (Name "hydra/core.Application")

_Application_function = (Name "function")

_Application_argument = (Name "argument")

-- | The type-level analog of an application term
data ApplicationType = 
  ApplicationType {
    -- | The left-hand side of the application
    applicationTypeFunction :: Type,
    -- | The right-hand side of the application
    applicationTypeArgument :: Type}
  deriving (Eq, Ord, Read, Show)

_ApplicationType = (Name "hydra/core.ApplicationType")

_ApplicationType_function = (Name "function")

_ApplicationType_argument = (Name "argument")

-- | A union elimination; a case statement
data CaseStatement = 
  CaseStatement {
    caseStatementTypeName :: Name,
    caseStatementDefault :: (Maybe Term),
    caseStatementCases :: [Field]}
  deriving (Eq, Ord, Read, Show)

_CaseStatement = (Name "hydra/core.CaseStatement")

_CaseStatement_typeName = (Name "typeName")

_CaseStatement_default = (Name "default")

_CaseStatement_cases = (Name "cases")

-- | A corresponding elimination for an introduction term
data Elimination = 
  -- | Eliminates a list using a fold function; this function has the signature b -> [a] -> b
  EliminationList Term |
  -- | Eliminates an optional term by matching over the two possible cases
  EliminationOptional OptionalCases |
  -- | Eliminates a tuple by projecting the component at a given 0-indexed offset
  EliminationProduct TupleProjection |
  -- | Eliminates a record by projecting a given field
  EliminationRecord Projection |
  -- | Eliminates a union term by matching over the fields of the union. This is a case statement.
  EliminationUnion CaseStatement |
  -- | Unwrap a wrapped term
  EliminationWrap Name
  deriving (Eq, Ord, Read, Show)

_Elimination = (Name "hydra/core.Elimination")

_Elimination_list = (Name "list")

_Elimination_optional = (Name "optional")

_Elimination_product = (Name "product")

_Elimination_record = (Name "record")

_Elimination_union = (Name "union")

_Elimination_wrap = (Name "wrap")

-- | A labeled term
data Field = 
  Field {
    fieldName :: Name,
    fieldTerm :: Term}
  deriving (Eq, Ord, Read, Show)

_Field = (Name "hydra/core.Field")

_Field_name = (Name "name")

_Field_term = (Name "term")

-- | The name and type of a field
data FieldType = 
  FieldType {
    fieldTypeName :: Name,
    fieldTypeType :: Type}
  deriving (Eq, Ord, Read, Show)

_FieldType = (Name "hydra/core.FieldType")

_FieldType_name = (Name "name")

_FieldType_type = (Name "type")

-- | A floating-point type
data FloatType = 
  FloatTypeBigfloat  |
  FloatTypeFloat32  |
  FloatTypeFloat64 
  deriving (Eq, Ord, Read, Show)

_FloatType = (Name "hydra/core.FloatType")

_FloatType_bigfloat = (Name "bigfloat")

_FloatType_float32 = (Name "float32")

_FloatType_float64 = (Name "float64")

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

_FloatValue_bigfloat = (Name "bigfloat")

_FloatValue_float32 = (Name "float32")

_FloatValue_float64 = (Name "float64")

-- | A function
data Function = 
  -- | An elimination for any of a few term variants
  FunctionElimination Elimination |
  -- | A function abstraction (lambda)
  FunctionLambda Lambda |
  -- | A reference to a built-in (primitive) function
  FunctionPrimitive Name
  deriving (Eq, Ord, Read, Show)

_Function = (Name "hydra/core.Function")

_Function_elimination = (Name "elimination")

_Function_lambda = (Name "lambda")

_Function_primitive = (Name "primitive")

-- | A function type, also known as an arrow type
data FunctionType = 
  FunctionType {
    functionTypeDomain :: Type,
    functionTypeCodomain :: Type}
  deriving (Eq, Ord, Read, Show)

_FunctionType = (Name "hydra/core.FunctionType")

_FunctionType_domain = (Name "domain")

_FunctionType_codomain = (Name "codomain")

-- | An instance of a union type; i.e. a string-indexed generalization of inl() or inr()
data Injection = 
  Injection {
    injectionTypeName :: Name,
    injectionField :: Field}
  deriving (Eq, Ord, Read, Show)

_Injection = (Name "hydra/core.Injection")

_Injection_typeName = (Name "typeName")

_Injection_field = (Name "field")

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

_IntegerType_bigint = (Name "bigint")

_IntegerType_int8 = (Name "int8")

_IntegerType_int16 = (Name "int16")

_IntegerType_int32 = (Name "int32")

_IntegerType_int64 = (Name "int64")

_IntegerType_uint8 = (Name "uint8")

_IntegerType_uint16 = (Name "uint16")

_IntegerType_uint32 = (Name "uint32")

_IntegerType_uint64 = (Name "uint64")

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

_IntegerValue_bigint = (Name "bigint")

_IntegerValue_int8 = (Name "int8")

_IntegerValue_int16 = (Name "int16")

_IntegerValue_int32 = (Name "int32")

_IntegerValue_int64 = (Name "int64")

_IntegerValue_uint8 = (Name "uint8")

_IntegerValue_uint16 = (Name "uint16")

_IntegerValue_uint32 = (Name "uint32")

_IntegerValue_uint64 = (Name "uint64")

-- | A function abstraction (lambda)
data Lambda = 
  Lambda {
    -- | The term variable introduced by the lambda
    lambdaParameter :: Name,
    -- | An optional domain type for the lambda (required for System F lambdas)
    lambdaDomain :: (Maybe Type),
    -- | The body of the lambda
    lambdaBody :: Term}
  deriving (Eq, Ord, Read, Show)

_Lambda = (Name "hydra/core.Lambda")

_Lambda_parameter = (Name "parameter")

_Lambda_domain = (Name "domain")

_Lambda_body = (Name "body")

-- | A type abstraction; the type-level analog of a lambda term
data LambdaType = 
  LambdaType {
    -- | The variable which is bound by the lambda
    lambdaTypeParameter :: Name,
    -- | The body of the lambda
    lambdaTypeBody :: Type}
  deriving (Eq, Ord, Read, Show)

_LambdaType = (Name "hydra/core.LambdaType")

_LambdaType_parameter = (Name "parameter")

_LambdaType_body = (Name "body")

-- | A set of (possibly recursive) 'let' bindings; a multi-let expression
data Let = 
  Let {
    letBindings :: [Field],
    letEnvironment :: Term}
  deriving (Eq, Ord, Read, Show)

_Let = (Name "hydra/core.Let")

_Let_bindings = (Name "bindings")

_Let_environment = (Name "environment")

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

_Literal_binary = (Name "binary")

_Literal_boolean = (Name "boolean")

_Literal_float = (Name "float")

_Literal_integer = (Name "integer")

_Literal_string = (Name "string")

-- | Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants
data LiteralType = 
  LiteralTypeBinary  |
  LiteralTypeBoolean  |
  LiteralTypeFloat FloatType |
  LiteralTypeInteger IntegerType |
  LiteralTypeString 
  deriving (Eq, Ord, Read, Show)

_LiteralType = (Name "hydra/core.LiteralType")

_LiteralType_binary = (Name "binary")

_LiteralType_boolean = (Name "boolean")

_LiteralType_float = (Name "float")

_LiteralType_integer = (Name "integer")

_LiteralType_string = (Name "string")

-- | A map type
data MapType = 
  MapType {
    mapTypeKeys :: Type,
    mapTypeValues :: Type}
  deriving (Eq, Ord, Read, Show)

_MapType = (Name "hydra/core.MapType")

_MapType_keys = (Name "keys")

_MapType_values = (Name "values")

-- | A symbol which stands for a term, type, or element
newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Name "hydra/core.Name")

-- | An object wrapped in a type name
data Nominal a = 
  Nominal {
    nominalTypeName :: Name,
    nominalObject :: a}
  deriving (Eq, Ord, Read, Show)

_Nominal = (Name "hydra/core.Nominal")

_Nominal_typeName = (Name "typeName")

_Nominal_object = (Name "object")

-- | A case statement for matching optional terms
data OptionalCases = 
  OptionalCases {
    -- | A term provided if the optional value is nothing
    optionalCasesNothing :: Term,
    -- | A function which is applied if the optional value is non-nothing
    optionalCasesJust :: Term}
  deriving (Eq, Ord, Read, Show)

_OptionalCases = (Name "hydra/core.OptionalCases")

_OptionalCases_nothing = (Name "nothing")

_OptionalCases_just = (Name "just")

-- | A record elimination; a projection
data Projection = 
  Projection {
    projectionTypeName :: Name,
    projectionField :: Name}
  deriving (Eq, Ord, Read, Show)

_Projection = (Name "hydra/core.Projection")

_Projection_typeName = (Name "typeName")

_Projection_field = (Name "field")

-- | A record, or labeled tuple; a map of field names to terms
data Record = 
  Record {
    recordTypeName :: Name,
    recordFields :: [Field]}
  deriving (Eq, Ord, Read, Show)

_Record = (Name "hydra/core.Record")

_Record_typeName = (Name "typeName")

_Record_fields = (Name "fields")

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

_RowType_typeName = (Name "typeName")

_RowType_extends = (Name "extends")

_RowType_fields = (Name "fields")

-- | An infinite stream of terms
data Stream = 
  Stream {
    streamFirst :: Term,
    streamRest :: Stream}
  deriving (Eq, Ord, Read, Show)

_Stream = (Name "hydra/core.Stream")

_Stream_first = (Name "first")

_Stream_rest = (Name "rest")

-- | The unlabeled equivalent of an Injection term
data Sum = 
  Sum {
    sumIndex :: Int,
    sumSize :: Int,
    sumTerm :: Term}
  deriving (Eq, Ord, Read, Show)

_Sum = (Name "hydra/core.Sum")

_Sum_index = (Name "index")

_Sum_size = (Name "size")

_Sum_term = (Name "term")

-- | A data term
data Term = 
  -- | A term annotated with metadata
  TermAnnotated (Annotated Term) |
  -- | A function application
  TermApplication Application |
  -- | A function term
  TermFunction Function |
  TermLet Let |
  -- | A list
  TermList [Term] |
  -- | A literal value
  TermLiteral Literal |
  -- | A map of keys to values
  TermMap (Map Term Term) |
  -- | An optional value
  TermOptional (Maybe Term) |
  -- | A tuple
  TermProduct [Term] |
  -- | A record term
  TermRecord Record |
  -- | A set of values
  TermSet (Set Term) |
  -- | An infinite stream of terms
  TermStream Stream |
  -- | A variant tuple
  TermSum Sum |
  -- | A System F type abstraction term
  TermTypeAbstraction TypeAbstraction |
  -- | A System F type application term
  TermTypeApplication TypedTerm |
  -- | A term annotated with a type
  TermTyped TypedTerm |
  -- | An injection; an instance of a union type
  TermUnion Injection |
  -- | A variable reference
  TermVariable Name |
  TermWrap (Nominal Term)
  deriving (Eq, Ord, Read, Show)

_Term = (Name "hydra/core.Term")

_Term_annotated = (Name "annotated")

_Term_application = (Name "application")

_Term_function = (Name "function")

_Term_let = (Name "let")

_Term_list = (Name "list")

_Term_literal = (Name "literal")

_Term_map = (Name "map")

_Term_optional = (Name "optional")

_Term_product = (Name "product")

_Term_record = (Name "record")

_Term_set = (Name "set")

_Term_stream = (Name "stream")

_Term_sum = (Name "sum")

_Term_typeAbstraction = (Name "typeAbstraction")

_Term_typeApplication = (Name "typeApplication")

_Term_typed = (Name "typed")

_Term_union = (Name "union")

_Term_variable = (Name "variable")

_Term_wrap = (Name "wrap")

-- | A tuple elimination; a projection from an integer-indexed product
data TupleProjection = 
  TupleProjection {
    -- | The arity of the tuple
    tupleProjectionArity :: Int,
    -- | The 0-indexed offset from the beginning of the tuple
    tupleProjectionIndex :: Int}
  deriving (Eq, Ord, Read, Show)

_TupleProjection = (Name "hydra/core.TupleProjection")

_TupleProjection_arity = (Name "arity")

_TupleProjection_index = (Name "index")

-- | A data type
data Type = 
  -- | A type annotated with metadata
  TypeAnnotated (Annotated Type) |
  TypeApplication ApplicationType |
  TypeFunction FunctionType |
  TypeLambda LambdaType |
  TypeList Type |
  TypeLiteral LiteralType |
  TypeMap MapType |
  TypeOptional Type |
  TypeProduct [Type] |
  TypeRecord RowType |
  TypeSet Type |
  TypeStream Type |
  TypeSum [Type] |
  TypeUnion RowType |
  TypeVariable Name |
  TypeWrap (Nominal Type)
  deriving (Eq, Ord, Read, Show)

_Type = (Name "hydra/core.Type")

_Type_annotated = (Name "annotated")

_Type_application = (Name "application")

_Type_function = (Name "function")

_Type_lambda = (Name "lambda")

_Type_list = (Name "list")

_Type_literal = (Name "literal")

_Type_map = (Name "map")

_Type_optional = (Name "optional")

_Type_product = (Name "product")

_Type_record = (Name "record")

_Type_set = (Name "set")

_Type_stream = (Name "stream")

_Type_sum = (Name "sum")

_Type_union = (Name "union")

_Type_variable = (Name "variable")

_Type_wrap = (Name "wrap")

-- | A System F type abstraction term
data TypeAbstraction = 
  TypeAbstraction {
    -- | The type variable introduced by the abstraction
    typeAbstractionParameter :: Name,
    -- | The body of the abstraction
    typeAbstractionBody :: Term}
  deriving (Eq, Ord, Read, Show)

_TypeAbstraction = (Name "hydra/core.TypeAbstraction")

_TypeAbstraction_parameter = (Name "parameter")

_TypeAbstraction_body = (Name "body")

-- | A type paired with a term. Typed terms are used for type annotations on terms, as well as for System F type applications
data TypedTerm = 
  TypedTerm {
    typedTermType :: Type,
    typedTermTerm :: Term}
  deriving (Eq, Ord, Read, Show)

_TypedTerm = (Name "hydra/core.TypedTerm")

_TypedTerm_type = (Name "type")

_TypedTerm_term = (Name "term")

-- | An empty record type as a canonical unit type
data UnitType = 
  UnitType {}
  deriving (Eq, Ord, Read, Show)

_UnitType = (Name "hydra/core.UnitType")
