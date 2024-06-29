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

_Either_left = (Core.Name "left")

_Either_right = (Core.Name "right")

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

_EliminationVariant_list = (Core.Name "list")

_EliminationVariant_optional = (Core.Name "optional")

_EliminationVariant_product = (Core.Name "product")

_EliminationVariant_record = (Core.Name "record")

_EliminationVariant_union = (Core.Name "union")

_EliminationVariant_wrap = (Core.Name "wrap")

-- | The identifier of a function constructor
data FunctionVariant = 
  FunctionVariantElimination  |
  FunctionVariantLambda  |
  FunctionVariantPrimitive 
  deriving (Eq, Ord, Read, Show)

_FunctionVariant = (Core.Name "hydra/mantle.FunctionVariant")

_FunctionVariant_elimination = (Core.Name "elimination")

_FunctionVariant_lambda = (Core.Name "lambda")

_FunctionVariant_primitive = (Core.Name "primitive")

-- | The identifier of a literal constructor
data LiteralVariant = 
  LiteralVariantBinary  |
  LiteralVariantBoolean  |
  LiteralVariantFloat  |
  LiteralVariantInteger  |
  LiteralVariantString 
  deriving (Eq, Ord, Read, Show)

_LiteralVariant = (Core.Name "hydra/mantle.LiteralVariant")

_LiteralVariant_binary = (Core.Name "binary")

_LiteralVariant_boolean = (Core.Name "boolean")

_LiteralVariant_float = (Core.Name "float")

_LiteralVariant_integer = (Core.Name "integer")

_LiteralVariant_string = (Core.Name "string")

-- | Numeric precision: arbitrary precision, or precision to a specified number of bits
data Precision = 
  PrecisionArbitrary  |
  PrecisionBits Int
  deriving (Eq, Ord, Read, Show)

_Precision = (Core.Name "hydra/mantle.Precision")

_Precision_arbitrary = (Core.Name "arbitrary")

_Precision_bits = (Core.Name "bits")

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
  TermVariantTypeAbstraction  |
  TermVariantTypeApplication  |
  TermVariantTyped  |
  TermVariantUnion  |
  TermVariantVariable  |
  TermVariantWrap 
  deriving (Eq, Ord, Read, Show)

_TermVariant = (Core.Name "hydra/mantle.TermVariant")

_TermVariant_annotated = (Core.Name "annotated")

_TermVariant_application = (Core.Name "application")

_TermVariant_function = (Core.Name "function")

_TermVariant_let = (Core.Name "let")

_TermVariant_list = (Core.Name "list")

_TermVariant_literal = (Core.Name "literal")

_TermVariant_map = (Core.Name "map")

_TermVariant_optional = (Core.Name "optional")

_TermVariant_product = (Core.Name "product")

_TermVariant_record = (Core.Name "record")

_TermVariant_set = (Core.Name "set")

_TermVariant_stream = (Core.Name "stream")

_TermVariant_sum = (Core.Name "sum")

_TermVariant_typeAbstraction = (Core.Name "typeAbstraction")

_TermVariant_typeApplication = (Core.Name "typeApplication")

_TermVariant_typed = (Core.Name "typed")

_TermVariant_union = (Core.Name "union")

_TermVariant_variable = (Core.Name "variable")

_TermVariant_wrap = (Core.Name "wrap")

-- | An assertion that two types can be unified into a single type
data TypeConstraint =
  TypeConstraint {
    typeConstraintLeft :: Core.Type,
    typeConstraintRight :: Core.Type,
    typeConstraintContext :: Maybe String}
  deriving (Eq, Ord, Read, Show)

_TypeConstraint = (Core.Name "hydra/mantle.TypeConstraint")

_TypeConstraint_left = (Core.Name "left")

_TypeConstraint_right = (Core.Name "right")

_TypeConstraint_context = (Core.Name "context")

-- | A type expression together with free type variables occurring in the expression
data TypeScheme = 
  TypeScheme {
    typeSchemeVariables :: [Core.Name],
    typeSchemeType :: Core.Type}
  deriving (Eq, Ord, Read, Show)

_TypeScheme = (Core.Name "hydra/mantle.TypeScheme")

_TypeScheme_variables = (Core.Name "variables")

_TypeScheme_type = (Core.Name "type")

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

_TypeVariant_annotated = (Core.Name "annotated")

_TypeVariant_application = (Core.Name "application")

_TypeVariant_function = (Core.Name "function")

_TypeVariant_lambda = (Core.Name "lambda")

_TypeVariant_list = (Core.Name "list")

_TypeVariant_literal = (Core.Name "literal")

_TypeVariant_map = (Core.Name "map")

_TypeVariant_optional = (Core.Name "optional")

_TypeVariant_product = (Core.Name "product")

_TypeVariant_record = (Core.Name "record")

_TypeVariant_set = (Core.Name "set")

_TypeVariant_stream = (Core.Name "stream")

_TypeVariant_sum = (Core.Name "sum")

_TypeVariant_union = (Core.Name "union")

_TypeVariant_variable = (Core.Name "variable")

_TypeVariant_wrap = (Core.Name "wrap")
