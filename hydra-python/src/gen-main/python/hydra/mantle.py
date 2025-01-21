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
    
    LIST = "list"
    
    OPTIONAL = "optional"
    
    PRODUCT = "product"
    
    RECORD = "record"
    
    UNION = "union"
    
    WRAP = "wrap"

class FunctionVariant(Enum):
    """The identifier of a function constructor."""
    
    ELIMINATION = "elimination"
    
    LAMBDA = "lambda"
    
    PRIMITIVE = "primitive"

class LiteralVariant(Enum):
    """The identifier of a literal constructor."""
    
    BINARY = "binary"
    
    BOOLEAN = "boolean"
    
    FLOAT = "float"
    
    INTEGER = "integer"
    
    STRING = "string"

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
    
    ANNOTATED = "annotated"
    
    APPLICATION = "application"
    
    FUNCTION = "function"
    
    LET = "let"
    
    LIST = "list"
    
    LITERAL = "literal"
    
    MAP = "map"
    
    OPTIONAL = "optional"
    
    PRODUCT = "product"
    
    RECORD = "record"
    
    SET = "set"
    
    SUM = "sum"
    
    TYPE_ABSTRACTION = "typeAbstraction"
    
    TYPE_APPLICATION = "typeApplication"
    
    TYPED = "typed"
    
    UNION = "union"
    
    VARIABLE = "variable"
    
    WRAP = "wrap"

@dataclass
class TypeConstraint:
    """An assertion that two types can be unified into a single type."""
    
    left: hydra.core.Type
    right: hydra.core.Type
    context: str | None

class TypeVariant(Enum):
    """The identifier of a type constructor."""
    
    ANNOTATED = "annotated"
    
    APPLICATION = "application"
    
    FUNCTION = "function"
    
    LAMBDA = "lambda"
    
    LIST = "list"
    
    LITERAL = "literal"
    
    MAP = "map"
    
    OPTIONAL = "optional"
    
    PRODUCT = "product"
    
    RECORD = "record"
    
    SET = "set"
    
    SUM = "sum"
    
    UNION = "union"
    
    VARIABLE = "variable"
    
    WRAP = "wrap"