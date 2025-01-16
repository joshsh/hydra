"""Hydra's core data model of type and term expressions"""

from __future__ import annotations
from typing import Annotated, Callable, Literal, NewType, TypeVar
from dataclasses import dataclass, field


@dataclass
class AnnotatedTerm:
    """A term together with an annotation"""

    subject: Term

    annotation: dict[Name, Term]


@dataclass
class AnnotatedType:
    """A type together with an annotation"""

    subject: Type

    annotation: dict[Name, Term]


@dataclass
class Application:
    """A term which applies a function to an argument"""

    function: Annotated[Term, "The left-hand side of the application"]

    argument: Annotated[Term, "The right-hand side of the application"]


@dataclass
class ApplicationType:
    """The type-level analog of an application term"""

    function: Annotated[Type, "The left-hand side of the application"]

    argument: Annotated[Type, "The right-hand side of the application"]


@dataclass
class CaseStatement:
    """A union elimination; a case statement"""

    type_name: Name

    default: Term | None

    cases: list[Field]


EliminationList = Annotated[
    NewType("EliminationList", Term),
    "Eliminates a list using a fold function; this function has the signature b -> [a] -> b",
]

EliminationOptional = Annotated[
    NewType("EliminationOptional", OptionalCases),
    "Eliminates an optional term by matching over the two possible cases",
]

EliminationProduct = Annotated[
    NewType("EliminationProduct", TupleProjection),
    "Eliminates a tuple by projecting the component at a given 0-indexed offset",
]

EliminationRecord = Annotated[
    NewType("EliminationRecord", Projection),
    "Eliminates a record by projecting a given field",
]

EliminationUnion = Annotated[
    NewType("EliminationUnion", CaseStatement),
    "Eliminates a union term by matching over the fields of the union. This is a case statement.",
]

EliminationWrap = Annotated[NewType("EliminationWrap", Name), "Unwrap a wrapped term"]

Elimination = Annotated[
    EliminationList
    | EliminationOptional
    | EliminationProduct
    | EliminationRecord
    | EliminationUnion
    | EliminationWrap,
    "A corresponding elimination for an introduction term",
]


@dataclass
class Field:
    """A name/term pair"""

    name: Name

    term: Term


@dataclass
class FieldType:
    """A name/type pair"""

    name: Name

    type: Type


FloatTypeBigfloat = Literal["bigfloat"]

FloatTypeFloat32 = Literal["float32"]

FloatTypeFloat64 = Literal["float64"]

FloatType = Annotated[
    FloatTypeBigfloat | FloatTypeFloat32 | FloatTypeFloat64, "A floating-point type"
]

FloatValueBigfloat = Annotated[
    NewType("FloatValueBigfloat", float), "An arbitrary-precision floating-point value"
]

FloatValueFloat32 = Annotated[
    NewType("FloatValueFloat32", float), "A 32-bit floating-point value"
]

FloatValueFloat64 = Annotated[
    NewType("FloatValueFloat64", float), "A 64-bit floating-point value"
]

FloatValue = Annotated[
    FloatValueBigfloat | FloatValueFloat32 | FloatValueFloat64,
    "A floating-point literal value",
]

FunctionElimination = Annotated[
    NewType("FunctionElimination", Elimination),
    "An elimination for any of a few term variants",
]

FunctionLambda = Annotated[
    NewType("FunctionLambda", Lambda), "A function abstraction (lambda)"
]

FunctionPrimitive = Annotated[
    NewType("FunctionPrimitive", Name), "A reference to a built-in (primitive) function"
]

Function = Annotated[
    FunctionElimination | FunctionLambda | FunctionPrimitive, "A function"
]


@dataclass
class FunctionType:
    """A function type, also known as an arrow type"""

    domain: Type

    codomain: Type


@dataclass
class Injection:
    """An instance of a union type; i.e. a string-indexed generalization of inl() or inr()"""

    type_name: Name

    field: Field


IntegerTypeBigint = Literal["bigint"]

IntegerTypeInt8 = Literal["int8"]

IntegerTypeInt16 = Literal["int16"]

IntegerTypeInt32 = Literal["int32"]

IntegerTypeInt64 = Literal["int64"]

IntegerTypeUint8 = Literal["uint8"]

IntegerTypeUint16 = Literal["uint16"]

IntegerTypeUint32 = Literal["uint32"]

IntegerTypeUint64 = Literal["uint64"]

IntegerType = Annotated[
    IntegerTypeBigint
    | IntegerTypeInt8
    | IntegerTypeInt16
    | IntegerTypeInt32
    | IntegerTypeInt64
    | IntegerTypeUint8
    | IntegerTypeUint16
    | IntegerTypeUint32
    | IntegerTypeUint64,
    "An integer type",
]

IntegerValueBigint = Annotated[
    NewType("IntegerValueBigint", int), "An arbitrary-precision integer value"
]

IntegerValueInt8 = Annotated[
    NewType("IntegerValueInt8", int), "An 8-bit signed integer value"
]

IntegerValueInt16 = Annotated[
    NewType("IntegerValueInt16", int), "A 16-bit signed integer value (short value)"
]

IntegerValueInt32 = Annotated[
    NewType("IntegerValueInt32", int), "A 32-bit signed integer value (int value)"
]

IntegerValueInt64 = Annotated[
    NewType("IntegerValueInt64", int), "A 64-bit signed integer value (long value)"
]

IntegerValueUint8 = Annotated[
    NewType("IntegerValueUint8", int), "An 8-bit unsigned integer value (byte)"
]

IntegerValueUint16 = Annotated[
    NewType("IntegerValueUint16", int), "A 16-bit unsigned integer value"
]

IntegerValueUint32 = Annotated[
    NewType("IntegerValueUint32", int), "A 32-bit unsigned integer value (unsigned int)"
]

IntegerValueUint64 = Annotated[
    NewType("IntegerValueUint64", int),
    "A 64-bit unsigned integer value (unsigned long)",
]

IntegerValue = Annotated[
    IntegerValueBigint
    | IntegerValueInt8
    | IntegerValueInt16
    | IntegerValueInt32
    | IntegerValueInt64
    | IntegerValueUint8
    | IntegerValueUint16
    | IntegerValueUint32
    | IntegerValueUint64,
    "An integer literal value",
]


@dataclass
class Lambda:
    """A function abstraction (lambda)"""

    parameter: Annotated[Name, "The parameter of the lambda"]

    domain: Annotated[Type | None, "An optional domain type for the lambda"]

    body: Annotated[Term, "The body of the lambda"]


@dataclass
class LambdaType:
    """A type abstraction; the type-level analog of a lambda term"""

    parameter: Annotated[Name, "The variable which is bound by the lambda"]

    body: Annotated[Type, "The body of the lambda"]


@dataclass
class Let:
    """A set of (possibly recursive) 'let' bindings together with an environment in which they are bound"""

    bindings: list[LetBinding]

    environment: Term


@dataclass
class LetBinding:
    """A field with an optional type scheme, used to bind variables to terms in a 'let' expression"""

    name: Name

    term: Term

    type: TypeScheme | None


LiteralBinary = Annotated[NewType("LiteralBinary", bytes), "A binary literal"]

LiteralBoolean = Annotated[NewType("LiteralBoolean", bool), "A boolean literal"]

LiteralFloat = Annotated[
    NewType("LiteralFloat", FloatValue), "A floating-point literal"
]

LiteralInteger = Annotated[
    NewType("LiteralInteger", IntegerValue), "An integer literal"
]

LiteralString = Annotated[NewType("LiteralString", str), "A string literal"]

Literal = Annotated[
    LiteralBinary | LiteralBoolean | LiteralFloat | LiteralInteger | LiteralString,
    "A term constant; an instance of a literal type",
]

LiteralTypeBinary = Literal["binary"]

LiteralTypeBoolean = Literal["boolean"]

LiteralTypeFloat = Annotated[
    NewType("LiteralTypeFloat", FloatType), "The type of a floating-point value"
]

LiteralTypeInteger = Annotated[
    NewType("LiteralTypeInteger", IntegerType), "The type of an integer value"
]

LiteralTypeString = Literal["string"]

LiteralType = Annotated[
    LiteralTypeBinary
    | LiteralTypeBoolean
    | LiteralTypeFloat
    | LiteralTypeInteger
    | LiteralTypeString,
    "Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants",
]


@dataclass
class MapType:
    """A map type"""

    keys: Type

    values: Type


Name = Annotated[
    NewType("Name", str), "A unique identifier in some context; a string-valued key"
]


@dataclass
class OptionalCases:
    """A case statement for matching optional terms"""

    nothing: Annotated[Term, "A term provided if the optional value is nothing"]

    just: Annotated[
        Term, "A function which is applied if the optional value is non-nothing"
    ]


@dataclass
class Projection:
    """A record elimination; a projection"""

    type_name: Annotated[Name, "The name of the record type"]

    field: Annotated[Name, "The name of the projected field"]


@dataclass
class Record:
    """A record, or labeled tuple; a map of field names to terms"""

    type_name: Name

    fields: list[Field]


@dataclass
class RowType:
    """A labeled record or union type"""

    type_name: Annotated[
        Name,
        "The name of the row type, which must correspond to the name of a Type element",
    ]

    fields: Annotated[
        list[FieldType], "The fields of this row type, excluding any inherited fields"
    ]


@dataclass
class Sum:
    """The unlabeled equivalent of an Injection term"""

    index: int

    size: int

    term: Annotated[Term, "A data term"]


TermAnnotated = Annotated[
    NewType("TermAnnotated", AnnotatedTerm), "A term annotated with metadata"
]

TermApplication = Annotated[
    NewType("TermApplication", Application), "A function application"
]

TermFunction = Annotated[NewType("TermFunction", Function), "A function term"]

TermLet = NewType("TermLet", Let)

TermList = Annotated[NewType("TermList", list[Term]), "A list"]

TermLiteral = Annotated[NewType("TermLiteral", Literal), "A literal value"]

TermMap = Annotated[NewType("TermMap", dict[Term, Term]), "A map of keys to values"]

TermOptional = Annotated[NewType("TermOptional", Term | None), "An optional value"]

TermProduct = Annotated[NewType("TermProduct", list[Term]), "A tuple"]

TermRecord = Annotated[NewType("TermRecord", Record), "A record term"]

TermSet = Annotated[NewType("TermSet", set[Term]), "A set of values"]

TermSum = Annotated[NewType("TermSum", Sum), "A variant tuple"]

TermTypeAbstraction = Annotated[
    NewType("TermTypeAbstraction", TypeAbstraction), "A System F type abstraction term"
]

TermTypeApplication = Annotated[
    NewType("TermTypeApplication", TypedTerm), "A System F type application term"
]

TermTyped = Annotated[NewType("TermTyped", TypedTerm), "A term annotated with its type"]

TermUnion = Annotated[
    NewType("TermUnion", Injection), "An injection; an instance of a union type"
]

TermVariable = Annotated[NewType("TermVariable", Name), "A variable reference"]

TermWrap = NewType("TermWrap", WrappedTerm)

Term = Annotated[
    TermAnnotated
    | TermApplication
    | TermFunction
    | TermLet
    | TermList
    | TermLiteral
    | TermMap
    | TermOptional
    | TermProduct
    | TermRecord
    | TermSet
    | TermSum
    | TermTypeAbstraction
    | TermTypeApplication
    | TermTyped
    | TermUnion
    | TermVariable
    | TermWrap,
    "A data term",
]


@dataclass
class TupleProjection:
    """A tuple elimination; a projection from an integer-indexed product"""

    arity: Annotated[int, "The arity of the tuple"]

    index: Annotated[int, "The 0-indexed offset from the beginning of the tuple"]


TypeAnnotated = NewType("TypeAnnotated", AnnotatedType)

TypeApplication = NewType("TypeApplication", ApplicationType)

TypeFunction = NewType("TypeFunction", FunctionType)

TypeLambda = NewType("TypeLambda", LambdaType)

TypeList = NewType("TypeList", Type)

TypeLiteral = NewType("TypeLiteral", LiteralType)

TypeMap = NewType("TypeMap", MapType)

TypeOptional = NewType("TypeOptional", Type)

TypeProduct = NewType("TypeProduct", list[Type])

TypeRecord = NewType("TypeRecord", RowType)

TypeSet = NewType("TypeSet", Type)

TypeSum = NewType("TypeSum", list[Type])

TypeUnion = NewType("TypeUnion", RowType)

TypeVariable = NewType("TypeVariable", Name)

TypeWrap = NewType("TypeWrap", WrappedType)

Type = Annotated[
    TypeAnnotated
    | TypeApplication
    | TypeFunction
    | TypeLambda
    | TypeList
    | TypeLiteral
    | TypeMap
    | TypeOptional
    | TypeProduct
    | TypeRecord
    | TypeSet
    | TypeSum
    | TypeUnion
    | TypeVariable
    | TypeWrap,
    "A data type",
]


@dataclass
class TypeAbstraction:
    """A System F type abstraction term"""

    parameter: Annotated[Name, "The type variable introduced by the abstraction"]

    body: Annotated[Term, "The body of the abstraction"]


@dataclass
class TypeScheme:
    """A type expression together with free type variables occurring in the expression"""

    variables: list[Name]

    type: Type


@dataclass
class TypedTerm:
    """A term together with its type"""

    term: Term

    type: Type


@dataclass
class Unit:
    """An empty record as a canonical unit value"""


@dataclass
class WrappedTerm:
    """A term wrapped in a type name"""

    type_name: Name

    object: Term


@dataclass
class WrappedType:
    """A type wrapped in a type name"""

    type_name: Name

    object: Type
