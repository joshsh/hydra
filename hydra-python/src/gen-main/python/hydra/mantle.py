"""A set of types which supplement hydra/core with variants and accessors"""

from __future__ import annotations
from typing import Annotated, Literal, NewType, TypeVar
from dataclasses import dataclass
import hydra.core

A = TypeVar("A")

B = TypeVar("B")

EitherLeft = NewType("EitherLeft", A)

EitherRight = NewType("EitherRight", B)

Either = Annotated[
    EitherLeft | EitherRight,
    "A disjoint union between a 'left' type and a 'right' type",
]

EliminationVariantList = Literal["list"]

EliminationVariantOptional = Literal["optional"]

EliminationVariantProduct = Literal["product"]

EliminationVariantRecord = Literal["record"]

EliminationVariantUnion = Literal["union"]

EliminationVariantWrap = Literal["wrap"]

EliminationVariant = Annotated[
    EliminationVariantList
    | EliminationVariantOptional
    | EliminationVariantProduct
    | EliminationVariantRecord
    | EliminationVariantUnion
    | EliminationVariantWrap,
    "The identifier of an elimination constructor",
]

FunctionVariantElimination = Literal["elimination"]

FunctionVariantLambda = Literal["lambda"]

FunctionVariantPrimitive = Literal["primitive"]

FunctionVariant = Annotated[
    FunctionVariantElimination | FunctionVariantLambda | FunctionVariantPrimitive,
    "The identifier of a function constructor",
]

LiteralVariantBinary = Literal["binary"]

LiteralVariantBoolean = Literal["boolean"]

LiteralVariantFloat = Literal["float"]

LiteralVariantInteger = Literal["integer"]

LiteralVariantString = Literal["string"]

LiteralVariant = Annotated[
    LiteralVariantBinary
    | LiteralVariantBoolean
    | LiteralVariantFloat
    | LiteralVariantInteger
    | LiteralVariantString,
    "The identifier of a literal constructor",
]

PrecisionArbitrary = Literal["arbitrary"]

PrecisionBits = NewType("PrecisionBits", int)

Precision = Annotated[
    PrecisionArbitrary | PrecisionBits,
    "Numeric precision: arbitrary precision, or precision to a specified number of bits",
]

TermAccessorAnnotatedSubject = Literal["annotatedSubject"]

TermAccessorApplicationFunction = Literal["applicationFunction"]

TermAccessorApplicationArgument = Literal["applicationArgument"]

TermAccessorLambdaBody = Literal["lambdaBody"]

TermAccessorListFold = Literal["listFold"]

TermAccessorOptionalCasesNothing = Literal["optionalCasesNothing"]

TermAccessorOptionalCasesJust = Literal["optionalCasesJust"]

TermAccessorUnionCasesDefault = Literal["unionCasesDefault"]

TermAccessorUnionCasesBranch = Annotated[
    NewType(
        "TermAccessorUnionCasesBranch",
        'type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = "hydra/core.Name"}, wrappedTypeObject = TypeLiteral LiteralTypeString})',
    ),
    "A unique identifier in some context; a string-valued key",
]

TermAccessorLetEnvironment = Literal["letEnvironment"]

TermAccessorLetBinding = Annotated[
    NewType(
        "TermAccessorLetBinding",
        'type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = "hydra/core.Name"}, wrappedTypeObject = TypeLiteral LiteralTypeString})',
    ),
    "A unique identifier in some context; a string-valued key",
]

TermAccessorListElement = NewType("TermAccessorListElement", int)

TermAccessorMapKey = NewType("TermAccessorMapKey", int)

TermAccessorMapValue = NewType("TermAccessorMapValue", int)

TermAccessorOptionalTerm = Literal["optionalTerm"]

TermAccessorProductTerm = NewType("TermAccessorProductTerm", int)

TermAccessorRecordField = Annotated[
    NewType(
        "TermAccessorRecordField",
        'type = TypeWrap (WrappedType {wrappedTypeTypeName = Name {unName = "hydra/core.Name"}, wrappedTypeObject = TypeLiteral LiteralTypeString})',
    ),
    "A unique identifier in some context; a string-valued key",
]

TermAccessorSetElement = NewType("TermAccessorSetElement", int)

TermAccessorSumTerm = Literal["sumTerm"]

TermAccessorTypeAbstractionBody = Literal["typeAbstractionBody"]

TermAccessorTypeApplicationTerm = Literal["typeApplicationTerm"]

TermAccessorTypedTerm = Literal["typedTerm"]

TermAccessorInjectionTerm = Literal["injectionTerm"]

TermAccessorWrappedTerm = Literal["wrappedTerm"]

TermAccessor = Annotated[
    TermAccessorAnnotatedSubject
    | TermAccessorApplicationFunction
    | TermAccessorApplicationArgument
    | TermAccessorLambdaBody
    | TermAccessorListFold
    | TermAccessorOptionalCasesNothing
    | TermAccessorOptionalCasesJust
    | TermAccessorUnionCasesDefault
    | TermAccessorUnionCasesBranch
    | TermAccessorLetEnvironment
    | TermAccessorLetBinding
    | TermAccessorListElement
    | TermAccessorMapKey
    | TermAccessorMapValue
    | TermAccessorOptionalTerm
    | TermAccessorProductTerm
    | TermAccessorRecordField
    | TermAccessorSetElement
    | TermAccessorSumTerm
    | TermAccessorTypeAbstractionBody
    | TermAccessorTypeApplicationTerm
    | TermAccessorTypedTerm
    | TermAccessorInjectionTerm
    | TermAccessorWrappedTerm,
    "A function which maps from a term to a particular immediate subterm",
]

TermVariantAnnotated = Literal["annotated"]

TermVariantApplication = Literal["application"]

TermVariantFunction = Literal["function"]

TermVariantLet = Literal["let"]

TermVariantList = Literal["list"]

TermVariantLiteral = Literal["literal"]

TermVariantMap = Literal["map"]

TermVariantOptional = Literal["optional"]

TermVariantProduct = Literal["product"]

TermVariantRecord = Literal["record"]

TermVariantSet = Literal["set"]

TermVariantSum = Literal["sum"]

TermVariantTypeAbstraction = Literal["typeAbstraction"]

TermVariantTypeApplication = Literal["typeApplication"]

TermVariantTyped = Literal["typed"]

TermVariantUnion = Literal["union"]

TermVariantVariable = Literal["variable"]

TermVariantWrap = Literal["wrap"]

TermVariant = Annotated[
    TermVariantAnnotated
    | TermVariantApplication
    | TermVariantFunction
    | TermVariantLet
    | TermVariantList
    | TermVariantLiteral
    | TermVariantMap
    | TermVariantOptional
    | TermVariantProduct
    | TermVariantRecord
    | TermVariantSet
    | TermVariantSum
    | TermVariantTypeAbstraction
    | TermVariantTypeApplication
    | TermVariantTyped
    | TermVariantUnion
    | TermVariantVariable
    | TermVariantWrap,
    "The identifier of a term expression constructor",
]


@dataclass
class TypeConstraint:
    """An assertion that two types can be unified into a single type"""

    left: hydra.core.Type

    right: hydra.core.Type

    context: str | None


TypeVariantAnnotated = Literal["annotated"]

TypeVariantApplication = Literal["application"]

TypeVariantFunction = Literal["function"]

TypeVariantLambda = Literal["lambda"]

TypeVariantList = Literal["list"]

TypeVariantLiteral = Literal["literal"]

TypeVariantMap = Literal["map"]

TypeVariantOptional = Literal["optional"]

TypeVariantProduct = Literal["product"]

TypeVariantRecord = Literal["record"]

TypeVariantSet = Literal["set"]

TypeVariantSum = Literal["sum"]

TypeVariantUnion = Literal["union"]

TypeVariantVariable = Literal["variable"]

TypeVariantWrap = Literal["wrap"]

TypeVariant = Annotated[
    TypeVariantAnnotated
    | TypeVariantApplication
    | TypeVariantFunction
    | TypeVariantLambda
    | TypeVariantList
    | TypeVariantLiteral
    | TypeVariantMap
    | TypeVariantOptional
    | TypeVariantProduct
    | TypeVariantRecord
    | TypeVariantSet
    | TypeVariantSum
    | TypeVariantUnion
    | TypeVariantVariable
    | TypeVariantWrap,
    "The identifier of a type constructor",
]
