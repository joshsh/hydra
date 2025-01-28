"""A DSL for constructing Hydra types in Python."""

from functools import reduce
from hydra.core import (
    Name,
    Type,
    TypeFunction,
    FunctionType,
    TypeApplication,
    ApplicationType,
    TypeAnnotated,
    AnnotatedType,
    TypeLambda,
    TypeList,
    TypeLiteral,
    TypeMap,
    TypeOptional,
    TypeProduct,
    TypeRecord,
    TypeSet,
    TypeSum,
    TypeUnion,
    TypeVariable,
    TypeWrap,
    LambdaType,
    LiteralType,
    MapType,
    RowType,
    FieldType,
    WrappedType,
    TypeScheme,
    Term,
)
import hydra.dsl.literal_types as lt


PLACEHOLDER_NAME = Name("placeholder")


def boolean() -> Type:
    """Construct a boolean type."""
    return literal(lt.boolean())


def binary() -> Type:
    """Construct a binary type."""
    return literal(lt.binary())


def string() -> Type:
    """Construct a string type."""
    return literal(lt.string())


def integer(itype: lt.IntegerType) -> Type:
    """Construct an integer type."""
    return literal(lt.integer(itype))


def uint8() -> Type:
    """Construct a uint8 type."""
    return literal(lt.uint8())


def uint16() -> Type:
    """Construct a uint16 type."""
    return literal(lt.uint16())


def uint32() -> Type:
    """Construct a uint32 type."""
    return literal(lt.uint32())


def uint64() -> Type:
    """Construct a uint64 type."""
    return literal(lt.uint64())


def int8() -> Type:
    """Construct an int8 type."""
    return literal(lt.int8())


def int16() -> Type:
    """Construct an int16 type."""
    return literal(lt.int16())


def int32() -> Type:
    """Construct an int32 type."""
    return literal(lt.int32())


def int64() -> Type:
    """Construct an int64 type."""
    return literal(lt.int64())


def non_negative_int32() -> Type:
    """Construct a non-negative int32 type."""
    return int32()


def bigint() -> Type:
    """Construct a bigint type."""
    return literal(lt.bigint())


def float_(ftype: lt.FloatType) -> Type:
    """Construct a float type."""
    return literal(lt.float_(ftype))


def float32() -> Type:
    """Construct a float32 type."""
    return literal(lt.float32())


def float64() -> Type:
    """Construct a float64 type."""
    return literal(lt.float64())


def bigfloat() -> Type:
    """Construct a bigfloat type."""
    return literal(lt.bigfloat())


def annot(ann: dict[str, Term], t: Type) -> Type:
    """Construct an annotated type."""
    return TypeAnnotated(AnnotatedType(t, {Name(k): v for k, v in ann.items()}))


def apply(lhs: Type, rhs: Type) -> Type:
    """Construct an application type."""
    return TypeApplication(ApplicationType(lhs, rhs))


def apply_n(ts: list[Type]) -> Type:
    """Construct an application type."""
    return reduce(apply, ts[1:], ts[0])


def set_(t: Type) -> Type:
    """Construct a set type."""
    return TypeSet(t)


def sum_(ts: list[Type]) -> Type:
    """Construct a sum type."""
    return TypeSum(ts)


def union(fields: list[FieldType]) -> Type:
    """Construct a union type."""
    return TypeUnion(RowType(PLACEHOLDER_NAME, fields))


def unit() -> Type:
    """Construct a unit type."""
    return record([field(PLACEHOLDER_NAME, unit())])


def enum(names: list[str]) -> Type:
    """Construct an enum type."""
    return union([field(Name(n), unit()) for n in names])


def field(n: Name, t: Type) -> FieldType:
    """Construct a field type."""
    return FieldType(n, t)


def fields_to_map(fields: list[FieldType]) -> dict[Name, Type]:
    """Construct a map type from a list of fields."""
    return {f.name: f.type for f in fields}


def function(a: Type, b: Type) -> Type:
    """Construct a function type."""
    return TypeFunction(FunctionType(a, b))


def function_n(ts: list[Type]) -> Type:
    """Construct a function type."""
    return reduce(lambda acc, t: function(t, acc), reversed(ts), ts[0])


def lam(v: Name, b: Type) -> Type:
    """Construct a lambda type."""
    return TypeLambda(LambdaType(v, b))


def lams(vs: list[str], body: Type) -> Type:
    """Construct a lambda type."""
    return reduce(lambda acc, v: lam(Name(v), acc), reversed(vs), body)


def list_(t: Type) -> Type:
    """Construct a list type."""
    return TypeList(t)


def literal(t: LiteralType) -> Type:
    """Construct a literal type."""
    return TypeLiteral(t)


def map_(k: Type, v: Type) -> Type:
    """Construct a map type."""
    return TypeMap(MapType(k, v))


def mono(t: Type) -> TypeScheme:
    """Construct a type scheme."""
    return TypeScheme([], t)


def optional(t: Type) -> Type:
    """Construct an optional type."""
    return TypeOptional(t)


def pair(a: Type, b: Type) -> Type:
    """Construct a pair type."""
    return product([a, b])


def poly(vs: list[str], t: Type) -> TypeScheme:
    """Construct a type scheme."""
    return TypeScheme([Name(v) for v in vs], t)


def product(ts: list[Type]) -> Type:
    """Construct a product type."""
    return TypeProduct(ts)


def record(fields: list[FieldType]) -> Type:
    """Construct a record type."""
    return TypeRecord(RowType(PLACEHOLDER_NAME, fields))


def scheme(variables: list[str], body: Type) -> TypeScheme:
    """Construct a type scheme."""
    return TypeScheme([Name(v) for v in variables], body)


def var(n: Name) -> Type:
    """Construct a variable type."""
    return TypeVariable(n)


def wrap_with_name(name: Name, t: Type) -> Type:
    """Construct a wrapped type."""
    return TypeWrap(WrappedType(name, t))


def wrap(t: Type) -> Type:
    """Construct a wrapped type."""
    return wrap_with_name(PLACEHOLDER_NAME, t)
