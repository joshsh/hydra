"""Hydra's core data model of type and term expressions."""

from __future__ import annotations
from typing import Annotated, Literal, NewType
from dataclasses import dataclass

@dataclass
class AnnotatedTerm:
    """A term together with an annotation."""

    subject: Term
    annotation: dict[Name, Term]

@dataclass
class AnnotatedType:
    """A type together with an annotation."""

    subject: Type
    annotation: dict[Name, Term]

@dataclass
class Application:
    """A term which applies a function to an argument."""

    function: Annotated[Term, "The left-hand side of the application"]
    argument: Annotated[Term, "The right-hand side of the application"]

@dataclass
class ApplicationType:
    """The type-level analog of an application term."""

    function: Annotated[Type, "The left-hand side of the application"]
    argument: Annotated[Type, "The right-hand side of the application"]

@dataclass
class CaseStatement:
    """A union elimination; a case statement."""

    type_name: Name
    default: Term | None
    cases: list[Field]

# Eliminates a list using a fold function; this function has the signature b -> [a] -> b
EliminationList = NewType("EliminationList", Term)

# Eliminates an optional term by matching over the two possible cases
EliminationOptional = NewType("EliminationOptional", OptionalCases)

# Eliminates a tuple by projecting the component at a given 0-indexed offset
EliminationProduct = NewType("EliminationProduct", TupleProjection)

# Eliminates a record by projecting a given field
EliminationRecord = NewType("EliminationRecord", Projection)

# Eliminates a union term by matching over the fields of the union. This is a case statement.
EliminationUnion = NewType("EliminationUnion", CaseStatement)

# Unwrap a wrapped term
EliminationWrap = NewType("EliminationWrap", Name)

# A corresponding elimination for an introduction term.
Elimination = EliminationList | EliminationOptional | EliminationProduct | EliminationRecord | EliminationUnion | EliminationWrap

@dataclass
class Field:
    """A name/term pair."""

    name: Name
    term: Term

@dataclass
class FieldType:
    """A name/type pair."""

    name: Name
    type: Type

FloatTypeBigfloat = Literal["bigfloat"]

FloatTypeFloat32 = Literal["float32"]

FloatTypeFloat64 = Literal["float64"]

# A floating-point type.
FloatType = FloatTypeBigfloat | FloatTypeFloat32 | FloatTypeFloat64

# An arbitrary-precision floating-point value
FloatValueBigfloat = NewType("FloatValueBigfloat", float)

# A 32-bit floating-point value
FloatValueFloat32 = NewType("FloatValueFloat32", float)

# A 64-bit floating-point value
FloatValueFloat64 = NewType("FloatValueFloat64", float)

# A floating-point literal value.
FloatValue = FloatValueBigfloat | FloatValueFloat32 | FloatValueFloat64

# An elimination for any of a few term variants
FunctionElimination = NewType("FunctionElimination", Elimination)

# A function abstraction (lambda)
FunctionLambda = NewType("FunctionLambda", Lambda)

# A reference to a built-in (primitive) function
FunctionPrimitive = NewType("FunctionPrimitive", Name)

# A function.
Function = FunctionElimination | FunctionLambda | FunctionPrimitive

@dataclass
class FunctionType:
    """A function type, also known as an arrow type."""

    domain: Type
    codomain: Type

@dataclass
class Injection:
    """An instance of a union type; i.e. a string-indexed generalization of inl() or inr()."""

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

# An integer type.
IntegerType = IntegerTypeBigint | IntegerTypeInt8 | IntegerTypeInt16 | IntegerTypeInt32 | IntegerTypeInt64 | IntegerTypeUint8 | IntegerTypeUint16 | IntegerTypeUint32 | IntegerTypeUint64

# An arbitrary-precision integer value
IntegerValueBigint = NewType("IntegerValueBigint", int)

# An 8-bit signed integer value
IntegerValueInt8 = NewType("IntegerValueInt8", int)

# A 16-bit signed integer value (short value)
IntegerValueInt16 = NewType("IntegerValueInt16", int)

# A 32-bit signed integer value (int value)
IntegerValueInt32 = NewType("IntegerValueInt32", int)

# A 64-bit signed integer value (long value)
IntegerValueInt64 = NewType("IntegerValueInt64", int)

# An 8-bit unsigned integer value (byte)
IntegerValueUint8 = NewType("IntegerValueUint8", int)

# A 16-bit unsigned integer value
IntegerValueUint16 = NewType("IntegerValueUint16", int)

# A 32-bit unsigned integer value (unsigned int)
IntegerValueUint32 = NewType("IntegerValueUint32", int)

# A 64-bit unsigned integer value (unsigned long)
IntegerValueUint64 = NewType("IntegerValueUint64", int)

# An integer literal value.
IntegerValue = IntegerValueBigint | IntegerValueInt8 | IntegerValueInt16 | IntegerValueInt32 | IntegerValueInt64 | IntegerValueUint8 | IntegerValueUint16 | IntegerValueUint32 | IntegerValueUint64

@dataclass
class Lambda:
    """A function abstraction (lambda)."""

    parameter: Annotated[Name, "The parameter of the lambda"]
    domain: Annotated[Type | None, "An optional domain type for the lambda"]
    body: Annotated[Term, "The body of the lambda"]

@dataclass
class LambdaType:
    """A type abstraction; the type-level analog of a lambda term."""

    parameter: Annotated[Name, "The variable which is bound by the lambda"]
    body: Annotated[Type, "The body of the lambda"]

@dataclass
class Let:
    """A set of (possibly recursive) 'let' bindings together with an environment in which they are bound."""

    bindings: list[LetBinding]
    environment: Term

@dataclass
class LetBinding:
    """A field with an optional type scheme, used to bind variables to terms in a 'let' expression."""

    name: Name
    term: Term
    type: TypeScheme | None

# A binary literal
LiteralBinary = NewType("LiteralBinary", bytes)

# A boolean literal
LiteralBoolean = NewType("LiteralBoolean", bool)

# A floating-point literal
LiteralFloat = NewType("LiteralFloat", FloatValue)

# An integer literal
LiteralInteger = NewType("LiteralInteger", IntegerValue)

# A string literal
LiteralString = NewType("LiteralString", str)

# A term constant; an instance of a literal type.
Literal = LiteralBinary | LiteralBoolean | LiteralFloat | LiteralInteger | LiteralString

LiteralTypeBinary = Literal["binary"]

LiteralTypeBoolean = Literal["boolean"]

# The type of a floating-point value
LiteralTypeFloat = NewType("LiteralTypeFloat", FloatType)

# The type of an integer value
LiteralTypeInteger = NewType("LiteralTypeInteger", IntegerType)

LiteralTypeString = Literal["string"]

# Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants.
LiteralType = LiteralTypeBinary | LiteralTypeBoolean | LiteralTypeFloat | LiteralTypeInteger | LiteralTypeString

@dataclass
class MapType:
    """A map type."""

    keys: Type
    values: Type

# A unique identifier in some context; a string-valued key.
Name = NewType("Name", str)

@dataclass
class OptionalCases:
    """A case statement for matching optional terms."""

    nothing: Annotated[Term, "A term provided if the optional value is nothing"]
    just: Annotated[Term, "A function which is applied if the optional value is non-nothing"]

@dataclass
class Projection:
    """A record elimination; a projection."""

    type_name: Annotated[Name, "The name of the record type"]
    field: Annotated[Name, "The name of the projected field"]

@dataclass
class Record:
    """A record, or labeled tuple; a map of field names to terms."""

    type_name: Name
    fields: list[Field]

@dataclass
class RowType:
    """A labeled record or union type."""

    type_name: Annotated[Name, "The name of the row type, which must correspond to the name of a Type element"]
    fields: Annotated[list[FieldType], "The fields of this row type, excluding any inherited fields"]

@dataclass
class Sum:
    """The unlabeled equivalent of an Injection term."""

    index: int
    size: int
    term: Annotated[Term, "A data term"]

# A term annotated with metadata
TermAnnotated = NewType("TermAnnotated", AnnotatedTerm)

# A function application
TermApplication = NewType("TermApplication", Application)

# A function term
TermFunction = NewType("TermFunction", Function)

TermLet = NewType("TermLet", Let)

# A list
TermList = NewType("TermList", list[Term])

# A literal value
TermLiteral = NewType("TermLiteral", Literal)

# A map of keys to values
TermMap = NewType("TermMap", dict[Term, Term])

# An optional value
TermOptional = NewType("TermOptional", Term | None)

# A tuple
TermProduct = NewType("TermProduct", list[Term])

# A record term
TermRecord = NewType("TermRecord", Record)

# A set of values
TermSet = NewType("TermSet", set[Term])

# A variant tuple
TermSum = NewType("TermSum", Sum)

# A System F type abstraction term
TermTypeAbstraction = NewType("TermTypeAbstraction", TypeAbstraction)

# A System F type application term
TermTypeApplication = NewType("TermTypeApplication", TypedTerm)

# A term annotated with its type
TermTyped = NewType("TermTyped", TypedTerm)

# An injection; an instance of a union type
TermUnion = NewType("TermUnion", Injection)

# A variable reference
TermVariable = NewType("TermVariable", Name)

TermWrap = NewType("TermWrap", WrappedTerm)

# A data term.
Term = TermAnnotated | TermApplication | TermFunction | TermLet | TermList | TermLiteral | TermMap | TermOptional | TermProduct | TermRecord | TermSet | TermSum | TermTypeAbstraction | TermTypeApplication | TermTyped | TermUnion | TermVariable | TermWrap

@dataclass
class TupleProjection:
    """A tuple elimination; a projection from an integer-indexed product."""

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

# A data type.
Type = TypeAnnotated | TypeApplication | TypeFunction | TypeLambda | TypeList | TypeLiteral | TypeMap | TypeOptional | TypeProduct | TypeRecord | TypeSet | TypeSum | TypeUnion | TypeVariable | TypeWrap

@dataclass
class TypeAbstraction:
    """A System F type abstraction term."""

    parameter: Annotated[Name, "The type variable introduced by the abstraction"]
    body: Annotated[Term, "The body of the abstraction"]

@dataclass
class TypeScheme:
    """A type expression together with free type variables occurring in the expression."""

    variables: list[Name]
    type: Type

@dataclass
class TypedTerm:
    """A term together with its type."""

    term: Term
    type: Type

@dataclass
class Unit:
    """An empty record as a canonical unit value."""



@dataclass
class WrappedTerm:
    """A term wrapped in a type name."""

    type_name: Name
    object: Term

@dataclass
class WrappedType:
    """A type wrapped in a type name."""

    type_name: Name
    object: Type