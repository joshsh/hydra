-- | A set of types which supplement hydra/core with type variants, graphs, and elements

module Hydra.Mantle where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A disjoint union between a 'left' type and a 'right' type
data Either_ a b = 
  EitherLeft a |
  EitherRight b
  deriving (Eq, Ord, Read, Show)

_Either = (Core.Name "hydra/mantle.Either")

_Either_left = (Core.FieldName "left")

_Either_right = (Core.FieldName "right")

-- | The identifier of an elimination constructor
data EliminationVariant = 
  EliminationVariantList  |
  EliminationVariantOptional  |
  EliminationVariantProduct  |
  EliminationVariantRecord  |
  EliminationVariantUnion  |
  EliminationVariantWrap 
  deriving (Eq, Ord, Read, Show)

_EliminationVariant = (Core.Name "hydra/mantle.EliminationVariant")

_EliminationVariant_list = (Core.FieldName "list")

_EliminationVariant_optional = (Core.FieldName "optional")

_EliminationVariant_product = (Core.FieldName "product")

_EliminationVariant_record = (Core.FieldName "record")

_EliminationVariant_union = (Core.FieldName "union")

_EliminationVariant_wrap = (Core.FieldName "wrap")

-- | The identifier of a function constructor
data FunctionVariant = 
  FunctionVariantElimination  |
  FunctionVariantLambda  |
  FunctionVariantPrimitive 
  deriving (Eq, Ord, Read, Show)

_FunctionVariant = (Core.Name "hydra/mantle.FunctionVariant")

_FunctionVariant_elimination = (Core.FieldName "elimination")

_FunctionVariant_lambda = (Core.FieldName "lambda")

_FunctionVariant_primitive = (Core.FieldName "primitive")

-- | The identifier of a literal constructor
data LiteralVariant = 
  LiteralVariantBinary  |
  LiteralVariantBoolean  |
  LiteralVariantFloat  |
  LiteralVariantInteger  |
  LiteralVariantString 
  deriving (Eq, Ord, Read, Show)

_LiteralVariant = (Core.Name "hydra/mantle.LiteralVariant")

_LiteralVariant_binary = (Core.FieldName "binary")

_LiteralVariant_boolean = (Core.FieldName "boolean")

_LiteralVariant_float = (Core.FieldName "float")

_LiteralVariant_integer = (Core.FieldName "integer")

_LiteralVariant_string = (Core.FieldName "string")

-- | Numeric precision: arbitrary precision, or precision to a specified number of bits
data Precision = 
  PrecisionArbitrary  |
  PrecisionBits Int
  deriving (Eq, Ord, Read, Show)

_Precision = (Core.Name "hydra/mantle.Precision")

_Precision_arbitrary = (Core.FieldName "arbitrary")

_Precision_bits = (Core.FieldName "bits")

-- | The identifier of a term expression constructor
data TermVariant = 
  TermVariantAnnotated  |
  TermVariantApplication  |
  TermVariantFunction  |
  TermVariantLet  |
  TermVariantList  |
  TermVariantLiteral  |
  TermVariantMap  |
  TermVariantOptional  |
  TermVariantProduct  |
  TermVariantRecord  |
  TermVariantSet  |
  TermVariantStream  |
  TermVariantSum  |
  TermVariantUnion  |
  TermVariantVariable  |
  TermVariantWrap 
  deriving (Eq, Ord, Read, Show)

_TermVariant = (Core.Name "hydra/mantle.TermVariant")

_TermVariant_annotated = (Core.FieldName "annotated")

_TermVariant_application = (Core.FieldName "application")

_TermVariant_function = (Core.FieldName "function")

_TermVariant_let = (Core.FieldName "let")

_TermVariant_list = (Core.FieldName "list")

_TermVariant_literal = (Core.FieldName "literal")

_TermVariant_map = (Core.FieldName "map")

_TermVariant_optional = (Core.FieldName "optional")

_TermVariant_product = (Core.FieldName "product")

_TermVariant_record = (Core.FieldName "record")

_TermVariant_set = (Core.FieldName "set")

_TermVariant_stream = (Core.FieldName "stream")

_TermVariant_sum = (Core.FieldName "sum")

_TermVariant_union = (Core.FieldName "union")

_TermVariant_variable = (Core.FieldName "variable")

_TermVariant_wrap = (Core.FieldName "wrap")

-- | A type expression together with free type variables occurring in the expression
data TypeScheme a = 
  TypeScheme {
    typeSchemeVariables :: [Core.Name],
    typeSchemeType :: (Core.Type Core.Kv)}
  deriving (Eq, Ord, Read, Show)

_TypeScheme = (Core.Name "hydra/mantle.TypeScheme")

_TypeScheme_variables = (Core.FieldName "variables")

_TypeScheme_type = (Core.FieldName "type")

-- | The identifier of a type constructor
data TypeVariant = 
  TypeVariantAnnotated  |
  TypeVariantApplication  |
  TypeVariantFunction  |
  TypeVariantLambda  |
  TypeVariantList  |
  TypeVariantLiteral  |
  TypeVariantMap  |
  TypeVariantOptional  |
  TypeVariantProduct  |
  TypeVariantRecord  |
  TypeVariantSet  |
  TypeVariantStream  |
  TypeVariantSum  |
  TypeVariantUnion  |
  TypeVariantVariable  |
  TypeVariantWrap 
  deriving (Eq, Ord, Read, Show)

_TypeVariant = (Core.Name "hydra/mantle.TypeVariant")

_TypeVariant_annotated = (Core.FieldName "annotated")

_TypeVariant_application = (Core.FieldName "application")

_TypeVariant_function = (Core.FieldName "function")

_TypeVariant_lambda = (Core.FieldName "lambda")

_TypeVariant_list = (Core.FieldName "list")

_TypeVariant_literal = (Core.FieldName "literal")

_TypeVariant_map = (Core.FieldName "map")

_TypeVariant_optional = (Core.FieldName "optional")

_TypeVariant_product = (Core.FieldName "product")

_TypeVariant_record = (Core.FieldName "record")

_TypeVariant_set = (Core.FieldName "set")

_TypeVariant_stream = (Core.FieldName "stream")

_TypeVariant_sum = (Core.FieldName "sum")

_TypeVariant_union = (Core.FieldName "union")

_TypeVariant_variable = (Core.FieldName "variable")

_TypeVariant_wrap = (Core.FieldName "wrap")

-- | A type together with an instance of the type
data TypedTerm =
  TypedTerm {
    typedTermType :: (Core.Type Core.Kv),
    typedTermTerm :: (Core.Term)}
  deriving (Eq, Ord, Read, Show)

_TypedTerm = (Core.Name "hydra/mantle.TypedTerm")

_TypedTerm_type = (Core.FieldName "type")

_TypedTerm_term = (Core.FieldName "term")
