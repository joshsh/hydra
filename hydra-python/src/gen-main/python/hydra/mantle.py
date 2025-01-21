"""A set of types which supplement hydra/core with variants and accessors."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.types import Variant
from typing import Generic, NewType, TypeVar
import hydra.core

A = TypeVar("A")
B = TypeVar("B")

class EitherLeft(Variant[A]): ...

class EitherRight(Variant[B]): ...

# A disjoint union between a 'left' type and a 'right' type.
type Either = EitherLeft | EitherRight

class EliminationVariant(Enum):
    """The identifier of an elimination constructor."""
    
    ELIMINATION_VARIANT_LIST = "list"
    ELIMINATION_VARIANT_OPTIONAL = "optional"
    ELIMINATION_VARIANT_PRODUCT = "product"
    ELIMINATION_VARIANT_RECORD = "record"
    ELIMINATION_VARIANT_UNION = "union"
    ELIMINATION_VARIANT_WRAP = "wrap"

class FunctionVariant(Enum):
    """The identifier of a function constructor."""
    
    FUNCTION_VARIANT_ELIMINATION = "elimination"
    FUNCTION_VARIANT_LAMBDA = "lambda"
    FUNCTION_VARIANT_PRIMITIVE = "primitive"

class LiteralVariant(Enum):
    """The identifier of a literal constructor."""
    
    LITERAL_VARIANT_BINARY = "binary"
    LITERAL_VARIANT_BOOLEAN = "boolean"
    LITERAL_VARIANT_FLOAT = "float"
    LITERAL_VARIANT_INTEGER = "integer"
    LITERAL_VARIANT_STRING = "string"

class PrecisionArbitrary(Variant[None]): ...

class PrecisionBits(Variant[int]): ...

# Numeric precision: arbitrary precision, or precision to a specified number of bits.
type Precision = PrecisionArbitrary | PrecisionBits

class TermAccessorAnnotatedSubject(Variant[None]): ...

class TermAccessorApplicationFunction(Variant[None]): ...

class TermAccessorApplicationArgument(Variant[None]): ...

class TermAccessorLambdaBody(Variant[None]): ...

class TermAccessorListFold(Variant[None]): ...

class TermAccessorOptionalCasesNothing(Variant[None]): ...

class TermAccessorOptionalCasesJust(Variant[None]): ...

class TermAccessorUnionCasesDefault(Variant[None]): ...

class TermAccessorUnionCasesBranch(Variant[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorLetEnvironment(Variant[None]): ...

class TermAccessorLetBinding(Variant[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorListElement(Variant[int]): ...

class TermAccessorMapKey(Variant[int]): ...

class TermAccessorMapValue(Variant[int]): ...

class TermAccessorOptionalTerm(Variant[None]): ...

class TermAccessorProductTerm(Variant[int]): ...

class TermAccessorRecordField(Variant[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorSetElement(Variant[int]): ...

class TermAccessorSumTerm(Variant[None]): ...

class TermAccessorTypeAbstractionBody(Variant[None]): ...

class TermAccessorTypeApplicationTerm(Variant[None]): ...

class TermAccessorTypedTerm(Variant[None]): ...

class TermAccessorInjectionTerm(Variant[None]): ...

class TermAccessorWrappedTerm(Variant[None]): ...

# A function which maps from a term to a particular immediate subterm.
type TermAccessor = TermAccessorAnnotatedSubject | TermAccessorApplicationFunction | TermAccessorApplicationArgument | TermAccessorLambdaBody | TermAccessorListFold | TermAccessorOptionalCasesNothing | TermAccessorOptionalCasesJust | TermAccessorUnionCasesDefault | TermAccessorUnionCasesBranch | TermAccessorLetEnvironment | TermAccessorLetBinding | TermAccessorListElement | TermAccessorMapKey | TermAccessorMapValue | TermAccessorOptionalTerm | TermAccessorProductTerm | TermAccessorRecordField | TermAccessorSetElement | TermAccessorSumTerm | TermAccessorTypeAbstractionBody | TermAccessorTypeApplicationTerm | TermAccessorTypedTerm | TermAccessorInjectionTerm | TermAccessorWrappedTerm

class TermVariant(Enum):
    """The identifier of a term expression constructor."""
    
    TERM_VARIANT_ANNOTATED = "annotated"
    TERM_VARIANT_APPLICATION = "application"
    TERM_VARIANT_FUNCTION = "function"
    TERM_VARIANT_LET = "let"
    TERM_VARIANT_LIST = "list"
    TERM_VARIANT_LITERAL = "literal"
    TERM_VARIANT_MAP = "map"
    TERM_VARIANT_OPTIONAL = "optional"
    TERM_VARIANT_PRODUCT = "product"
    TERM_VARIANT_RECORD = "record"
    TERM_VARIANT_SET = "set"
    TERM_VARIANT_SUM = "sum"
    TERM_VARIANT_TYPE_ABSTRACTION = "typeAbstraction"
    TERM_VARIANT_TYPE_APPLICATION = "typeApplication"
    TERM_VARIANT_TYPED = "typed"
    TERM_VARIANT_UNION = "union"
    TERM_VARIANT_VARIABLE = "variable"
    TERM_VARIANT_WRAP = "wrap"

@dataclass
class TypeConstraint:
    """An assertion that two types can be unified into a single type."""
    
    left: hydra.core.Type
    right: hydra.core.Type
    context: str | None

class TypeVariant(Enum):
    """The identifier of a type constructor."""
    
    TYPE_VARIANT_ANNOTATED = "annotated"
    TYPE_VARIANT_APPLICATION = "application"
    TYPE_VARIANT_FUNCTION = "function"
    TYPE_VARIANT_LAMBDA = "lambda"
    TYPE_VARIANT_LIST = "list"
    TYPE_VARIANT_LITERAL = "literal"
    TYPE_VARIANT_MAP = "map"
    TYPE_VARIANT_OPTIONAL = "optional"
    TYPE_VARIANT_PRODUCT = "product"
    TYPE_VARIANT_RECORD = "record"
    TYPE_VARIANT_SET = "set"
    TYPE_VARIANT_SUM = "sum"
    TYPE_VARIANT_UNION = "union"
    TYPE_VARIANT_VARIABLE = "variable"
    TYPE_VARIANT_WRAP = "wrap"