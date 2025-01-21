"""Hydra's core data model of type and term expressions."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.types import Variant
from typing import Annotated, NewType

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

class EliminationList(Variant[Term]):
    """Eliminates a list using a fold function; this function has the signature b -> [a] -> b."""

class EliminationOptional(Variant[OptionalCases]):
    """Eliminates an optional term by matching over the two possible cases."""

class EliminationProduct(Variant[TupleProjection]):
    """Eliminates a tuple by projecting the component at a given 0-indexed offset."""

class EliminationRecord(Variant[Projection]):
    """Eliminates a record by projecting a given field."""

class EliminationUnion(Variant[CaseStatement]):
    """Eliminates a union term by matching over the fields of the union. This is a case statement."""

class EliminationWrap(Variant[Name]):
    """Unwrap a wrapped term."""

# A corresponding elimination for an introduction term.
type Elimination = EliminationList | EliminationOptional | EliminationProduct | EliminationRecord | EliminationUnion | EliminationWrap

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

class FloatType(Enum):
    """A floating-point type."""
    
    BIGFLOAT = "bigfloat"
    FLOAT32 = "float32"
    FLOAT64 = "float64"

class FloatValueBigfloat(Variant[float]):
    """An arbitrary-precision floating-point value."""

class FloatValueFloat32(Variant[float]):
    """A 32-bit floating-point value."""

class FloatValueFloat64(Variant[float]):
    """A 64-bit floating-point value."""

# A floating-point literal value.
type FloatValue = FloatValueBigfloat | FloatValueFloat32 | FloatValueFloat64

class FunctionElimination(Variant[Elimination]):
    """An elimination for any of a few term variants."""

class FunctionLambda(Variant[Lambda]):
    """A function abstraction (lambda)."""

class FunctionPrimitive(Variant[Name]):
    """A reference to a built-in (primitive) function."""

# A function.
type Function = FunctionElimination | FunctionLambda | FunctionPrimitive

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

class IntegerType(Enum):
    """An integer type."""
    
    BIGINT = "bigint"
    INT8 = "int8"
    INT16 = "int16"
    INT32 = "int32"
    INT64 = "int64"
    UINT8 = "uint8"
    UINT16 = "uint16"
    UINT32 = "uint32"
    UINT64 = "uint64"

class IntegerValueBigint(Variant[int]):
    """An arbitrary-precision integer value."""

class IntegerValueInt8(Variant[int]):
    """An 8-bit signed integer value."""

class IntegerValueInt16(Variant[int]):
    """A 16-bit signed integer value (short value)."""

class IntegerValueInt32(Variant[int]):
    """A 32-bit signed integer value (int value)."""

class IntegerValueInt64(Variant[int]):
    """A 64-bit signed integer value (long value)."""

class IntegerValueUint8(Variant[int]):
    """An 8-bit unsigned integer value (byte)."""

class IntegerValueUint16(Variant[int]):
    """A 16-bit unsigned integer value."""

class IntegerValueUint32(Variant[int]):
    """A 32-bit unsigned integer value (unsigned int)."""

class IntegerValueUint64(Variant[int]):
    """A 64-bit unsigned integer value (unsigned long)."""

# An integer literal value.
type IntegerValue = IntegerValueBigint | IntegerValueInt8 | IntegerValueInt16 | IntegerValueInt32 | IntegerValueInt64 | IntegerValueUint8 | IntegerValueUint16 | IntegerValueUint32 | IntegerValueUint64

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

class LiteralBinary(Variant[bytes]):
    """A binary literal."""

class LiteralBoolean(Variant[bool]):
    """A boolean literal."""

class LiteralFloat(Variant[FloatValue]):
    """A floating-point literal."""

class LiteralInteger(Variant[IntegerValue]):
    """An integer literal."""

class LiteralString(Variant[str]):
    """A string literal."""

# A term constant; an instance of a literal type.
type Literal = LiteralBinary | LiteralBoolean | LiteralFloat | LiteralInteger | LiteralString

class LiteralTypeBinary(Variant[None]):
    """The type of a binary (byte string) value."""

class LiteralTypeBoolean(Variant[None]):
    """The type of a boolean (true/false) value."""

class LiteralTypeFloat(Variant[FloatType]):
    """The type of a floating-point value."""

class LiteralTypeInteger(Variant[IntegerType]):
    """The type of an integer value."""

class LiteralTypeString(Variant[None]):
    """The type of a string value."""

# Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants.
type LiteralType = LiteralTypeBinary | LiteralTypeBoolean | LiteralTypeFloat | LiteralTypeInteger | LiteralTypeString

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

class TermAnnotated(Variant[AnnotatedTerm]):
    """A term annotated with metadata."""

class TermApplication(Variant[Application]):
    """A function application."""

class TermFunction(Variant[Function]):
    """A function term."""

class TermLet(Variant[Let]): ...

class TermList(Variant[list[Term]]):
    """A list."""

class TermLiteral(Variant[Literal]):
    """A literal value."""

class TermMap(Variant[dict[Term, Term]]):
    """A map of keys to values."""

class TermOptional(Variant[Term | None]):
    """An optional value."""

class TermProduct(Variant[list[Term]]):
    """A tuple."""

class TermRecord(Variant[Record]):
    """A record term."""

class TermSet(Variant[set[Term]]):
    """A set of values."""

class TermSum(Variant[Sum]):
    """A variant tuple."""

class TermTypeAbstraction(Variant[TypeAbstraction]):
    """A System F type abstraction term."""

class TermTypeApplication(Variant[TypedTerm]):
    """A System F type application term."""

class TermTyped(Variant[TypedTerm]):
    """A term annotated with its type."""

class TermUnion(Variant[Injection]):
    """An injection; an instance of a union type."""

class TermVariable(Variant[Name]):
    """A variable reference."""

class TermWrap(Variant[WrappedTerm]): ...

# A data term.
type Term = TermAnnotated | TermApplication | TermFunction | TermLet | TermList | TermLiteral | TermMap | TermOptional | TermProduct | TermRecord | TermSet | TermSum | TermTypeAbstraction | TermTypeApplication | TermTyped | TermUnion | TermVariable | TermWrap

@dataclass
class TupleProjection:
    """A tuple elimination; a projection from an integer-indexed product."""
    
    arity: Annotated[int, "The arity of the tuple"]
    index: Annotated[int, "The 0-indexed offset from the beginning of the tuple"]

class TypeAnnotated(Variant[AnnotatedType]): ...

class TypeApplication(Variant[ApplicationType]): ...

class TypeFunction(Variant[FunctionType]): ...

class TypeLambda(Variant[LambdaType]): ...

class TypeList(Variant[Type]): ...

class TypeLiteral(Variant[LiteralType]): ...

class TypeMap(Variant[MapType]): ...

class TypeOptional(Variant[Type]): ...

class TypeProduct(Variant[list[Type]]): ...

class TypeRecord(Variant[RowType]): ...

class TypeSet(Variant[Type]): ...

class TypeSum(Variant[list[Type]]): ...

class TypeUnion(Variant[RowType]): ...

class TypeVariable(Variant[Name]): ...

class TypeWrap(Variant[WrappedType]): ...

# A data type.
type Type = TypeAnnotated | TypeApplication | TypeFunction | TypeLambda | TypeList | TypeLiteral | TypeMap | TypeOptional | TypeProduct | TypeRecord | TypeSet | TypeSum | TypeUnion | TypeVariable | TypeWrap

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