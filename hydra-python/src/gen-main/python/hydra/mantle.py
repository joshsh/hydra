"""A set of types which supplement hydra/core with variants and accessors."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.python import Node
from typing import TypeVar
import hydra.core

A = TypeVar("A")
B = TypeVar("B")

class EitherLeft(Node["A"]): ...

class EitherRight(Node["B"]): ...

# A disjoint union between a 'left' type and a 'right' type.
type Either[A, B] = EitherLeft[A] | EitherRight[B]

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

class PrecisionArbitrary(Node[None]): ...

class PrecisionBits(Node[int]): ...

# Numeric precision: arbitrary precision, or precision to a specified number of bits.
type Precision = PrecisionArbitrary | PrecisionBits

class TermAccessorAnnotatedSubject(Node[None]): ...

class TermAccessorApplicationFunction(Node[None]): ...

class TermAccessorApplicationArgument(Node[None]): ...

class TermAccessorLambdaBody(Node[None]): ...

class TermAccessorListFold(Node[None]): ...

class TermAccessorOptionalCasesNothing(Node[None]): ...

class TermAccessorOptionalCasesJust(Node[None]): ...

class TermAccessorUnionCasesDefault(Node[None]): ...

class TermAccessorUnionCasesBranch(Node[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorLetEnvironment(Node[None]): ...

class TermAccessorLetBinding(Node[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorListElement(Node[int]): ...

class TermAccessorMapKey(Node[int]): ...

class TermAccessorMapValue(Node[int]): ...

class TermAccessorOptionalTerm(Node[None]): ...

class TermAccessorProductTerm(Node[int]): ...

class TermAccessorRecordField(Node[hydra.core.Name]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorSetElement(Node[int]): ...

class TermAccessorSumTerm(Node[None]): ...

class TermAccessorTypeAbstractionBody(Node[None]): ...

class TermAccessorTypeApplicationTerm(Node[None]): ...

class TermAccessorTypedTerm(Node[None]): ...

class TermAccessorInjectionTerm(Node[None]): ...

class TermAccessorWrappedTerm(Node[None]): ...

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