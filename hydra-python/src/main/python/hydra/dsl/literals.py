"""A DSL for constructing literal values."""

from hydra.core import (
    Literal,
    FloatValue,
    IntegerValue,
    LiteralBinary,
    LiteralBoolean,
    LiteralFloat,
    LiteralInteger,
    LiteralString,
    FloatValueBigfloat,
    IntegerValueBigint,
    FloatValueFloat32,
    FloatValueFloat64,
    IntegerValueInt16,
    IntegerValueInt32,
    IntegerValueInt64,
    IntegerValueInt8,
    IntegerValueUint16,
    IntegerValueUint32,
    IntegerValueUint64,
    IntegerValueUint8,
)


def binary(value: bytes) -> Literal:
    """Construct a binary literal."""
    return LiteralBinary(value)


def boolean(value: bool) -> Literal:
    """Construct a boolean literal."""
    return LiteralBoolean(value)


def string(value: str) -> Literal:
    """Construct a string literal."""
    return LiteralString(value)


def float_(value: FloatValue) -> Literal:
    """Construct a float literal."""
    return LiteralFloat(value)


def float32(value: float) -> Literal:
    """Construct a float32 literal."""
    return float_(FloatValueFloat32(value))


def float64(value: float) -> Literal:
    """Construct a float64 literal."""
    return float_(FloatValueFloat64(value))


def bigfloat(value: float) -> Literal:
    """Construct a bigfloat literal."""
    return float_(FloatValueBigfloat(value))


def integer(value: IntegerValue) -> Literal:
    """Construct an integer literal."""
    return LiteralInteger(value)


def int8(value: int) -> Literal:
    """Construct an int8 literal."""
    return integer(IntegerValueInt8(value))


def int16(value: int) -> Literal:
    """Construct an int16 literal."""
    return integer(IntegerValueInt16(value))


def int32(value: int) -> Literal:
    """Construct an int32 literal."""
    return integer(IntegerValueInt32(value))


def int64(value: int) -> Literal:
    """Construct an int64 literal."""
    return integer(IntegerValueInt64(value))


def bigint(value: int) -> Literal:
    """Construct a bigint literal."""
    return integer(IntegerValueBigint(value))


def uint16(value: int) -> Literal:
    """Construct a uint16 literal."""
    return integer(IntegerValueUint16(value))


def uint32(value: int) -> Literal:
    """Construct a uint32 literal."""
    return integer(IntegerValueUint32(value))


def uint8(value: int) -> Literal:
    """Construct a uint8 literal."""
    return integer(IntegerValueUint8(value))


def uint64(value: int) -> Literal:
    """Construct a uint64 literal."""
    return integer(IntegerValueUint64(value))
