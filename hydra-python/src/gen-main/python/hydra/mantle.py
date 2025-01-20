"""A set of types which supplement hydra/core with variants and accessors."""

from __future__ import annotations
from dataclasses import dataclass
from hydra.dsl.types import Variant
from typing import Generic, NewType, TypeVar
import hydra.core

A = TypeVar("A")

B = TypeVar("B")

class EitherLeft(Variant[A]):
    pass

class EitherRight(Variant[B]):
    pass

# A disjoint union between a 'left' type and a 'right' type.
type Either = EitherLeft | EitherRight

class EliminationVariantList(Variant[None]):
    pass

class EliminationVariantOptional(Variant[None]):
    pass

class EliminationVariantProduct(Variant[None]):
    pass

class EliminationVariantRecord(Variant[None]):
    pass

class EliminationVariantUnion(Variant[None]):
    pass

class EliminationVariantWrap(Variant[None]):
    pass

# The identifier of an elimination constructor.
type EliminationVariant = EliminationVariantList | EliminationVariantOptional | EliminationVariantProduct | EliminationVariantRecord | EliminationVariantUnion | EliminationVariantWrap

class FunctionVariantElimination(Variant[None]):
    pass

class FunctionVariantLambda(Variant[None]):
    pass

class FunctionVariantPrimitive(Variant[None]):
    pass

# The identifier of a function constructor.
type FunctionVariant = FunctionVariantElimination | FunctionVariantLambda | FunctionVariantPrimitive

class LiteralVariantBinary(Variant[None]):
    pass

class LiteralVariantBoolean(Variant[None]):
    pass

class LiteralVariantFloat(Variant[None]):
    pass

class LiteralVariantInteger(Variant[None]):
    pass

class LiteralVariantString(Variant[None]):
    pass

# The identifier of a literal constructor.
type LiteralVariant = LiteralVariantBinary | LiteralVariantBoolean | LiteralVariantFloat | LiteralVariantInteger | LiteralVariantString

class PrecisionArbitrary(Variant[None]):
    pass

class PrecisionBits(Variant[int]):
    pass

# Numeric precision: arbitrary precision, or precision to a specified number of bits.
type Precision = PrecisionArbitrary | PrecisionBits

class TermAccessorAnnotatedSubject(Variant[None]):
    pass

class TermAccessorApplicationFunction(Variant[None]):
    pass

class TermAccessorApplicationArgument(Variant[None]):
    pass

class TermAccessorLambdaBody(Variant[None]):
    pass

class TermAccessorListFold(Variant[None]):
    pass

class TermAccessorOptionalCasesNothing(Variant[None]):
    pass

class TermAccessorOptionalCasesJust(Variant[None]):
    pass

class TermAccessorUnionCasesDefault(Variant[None]):
    pass

class TermAccessorUnionCasesBranch(Variant["type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = \"hydra/core.Name\"}, wrappedTypeObject = TypeLiteral LiteralTypeString})"]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorLetEnvironment(Variant[None]):
    pass

class TermAccessorLetBinding(Variant["type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = \"hydra/core.Name\"}, wrappedTypeObject = TypeLiteral LiteralTypeString})"]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorListElement(Variant[int]):
    pass

class TermAccessorMapKey(Variant[int]):
    pass

class TermAccessorMapValue(Variant[int]):
    pass

class TermAccessorOptionalTerm(Variant[None]):
    pass

class TermAccessorProductTerm(Variant[int]):
    pass

class TermAccessorRecordField(Variant["type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = \"hydra/core.Name\"}, wrappedTypeObject = TypeLiteral LiteralTypeString})"]):
    """A unique identifier in some context; a string-valued key."""

class TermAccessorSetElement(Variant[int]):
    pass

class TermAccessorSumTerm(Variant[None]):
    pass

class TermAccessorTypeAbstractionBody(Variant[None]):
    pass

class TermAccessorTypeApplicationTerm(Variant[None]):
    pass

class TermAccessorTypedTerm(Variant[None]):
    pass

class TermAccessorInjectionTerm(Variant[None]):
    pass

class TermAccessorWrappedTerm(Variant[None]):
    pass

# A function which maps from a term to a particular immediate subterm.
type TermAccessor = TermAccessorAnnotatedSubject | TermAccessorApplicationFunction | TermAccessorApplicationArgument | TermAccessorLambdaBody | TermAccessorListFold | TermAccessorOptionalCasesNothing | TermAccessorOptionalCasesJust | TermAccessorUnionCasesDefault | TermAccessorUnionCasesBranch | TermAccessorLetEnvironment | TermAccessorLetBinding | TermAccessorListElement | TermAccessorMapKey | TermAccessorMapValue | TermAccessorOptionalTerm | TermAccessorProductTerm | TermAccessorRecordField | TermAccessorSetElement | TermAccessorSumTerm | TermAccessorTypeAbstractionBody | TermAccessorTypeApplicationTerm | TermAccessorTypedTerm | TermAccessorInjectionTerm | TermAccessorWrappedTerm

class TermVariantAnnotated(Variant[None]):
    pass

class TermVariantApplication(Variant[None]):
    pass

class TermVariantFunction(Variant[None]):
    pass

class TermVariantLet(Variant[None]):
    pass

class TermVariantList(Variant[None]):
    pass

class TermVariantLiteral(Variant[None]):
    pass

class TermVariantMap(Variant[None]):
    pass

class TermVariantOptional(Variant[None]):
    pass

class TermVariantProduct(Variant[None]):
    pass

class TermVariantRecord(Variant[None]):
    pass

class TermVariantSet(Variant[None]):
    pass

class TermVariantSum(Variant[None]):
    pass

class TermVariantTypeAbstraction(Variant[None]):
    pass

class TermVariantTypeApplication(Variant[None]):
    pass

class TermVariantTyped(Variant[None]):
    pass

class TermVariantUnion(Variant[None]):
    pass

class TermVariantVariable(Variant[None]):
    pass

class TermVariantWrap(Variant[None]):
    pass

# The identifier of a term expression constructor.
type TermVariant = TermVariantAnnotated | TermVariantApplication | TermVariantFunction | TermVariantLet | TermVariantList | TermVariantLiteral | TermVariantMap | TermVariantOptional | TermVariantProduct | TermVariantRecord | TermVariantSet | TermVariantSum | TermVariantTypeAbstraction | TermVariantTypeApplication | TermVariantTyped | TermVariantUnion | TermVariantVariable | TermVariantWrap

@dataclass
class TypeConstraint:
    """An assertion that two types can be unified into a single type."""
    left: hydra.core.Type
    right: hydra.core.Type
    context: str | None

class TypeVariantAnnotated(Variant[None]):
    pass

class TypeVariantApplication(Variant[None]):
    pass

class TypeVariantFunction(Variant[None]):
    pass

class TypeVariantLambda(Variant[None]):
    pass

class TypeVariantList(Variant[None]):
    pass

class TypeVariantLiteral(Variant[None]):
    pass

class TypeVariantMap(Variant[None]):
    pass

class TypeVariantOptional(Variant[None]):
    pass

class TypeVariantProduct(Variant[None]):
    pass

class TypeVariantRecord(Variant[None]):
    pass

class TypeVariantSet(Variant[None]):
    pass

class TypeVariantSum(Variant[None]):
    pass

class TypeVariantUnion(Variant[None]):
    pass

class TypeVariantVariable(Variant[None]):
    pass

class TypeVariantWrap(Variant[None]):
    pass

# The identifier of a type constructor.
type TypeVariant = TypeVariantAnnotated | TypeVariantApplication | TypeVariantFunction | TypeVariantLambda | TypeVariantList | TypeVariantLiteral | TypeVariantMap | TypeVariantOptional | TypeVariantProduct | TypeVariantRecord | TypeVariantSet | TypeVariantSum | TypeVariantUnion | TypeVariantVariable | TypeVariantWrap