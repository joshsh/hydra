"""A DSL of short names for literal types."""

from hydra.core import (
    FloatType,
    LiteralType,
    LiteralTypeFloat,
    LiteralTypeInteger,
    IntegerType,
    LiteralTypeBinary,
    LiteralTypeBoolean,
    LiteralTypeString,
)


def binary() -> LiteralType:
    """Construct a binary literal type."""
    return LiteralTypeBinary(None)


def boolean() -> LiteralType:
    """Construct a boolean literal type."""
    return LiteralTypeBoolean(None)


def string() -> LiteralType:
    """Construct a string literal type."""
    return LiteralTypeString(None)


def float_(ftype: FloatType) -> LiteralType:
    """Construct a float literal type."""
    return LiteralTypeFloat(ftype)


def float32() -> LiteralType:
    """Construct a float32 literal type."""
    return float_(FloatType.FLOAT32)


def float64() -> LiteralType:
    """Construct a float64 literal type."""
    return float_(FloatType.FLOAT64)


def bigfloat() -> LiteralType:
    """Construct a bigfloat literal type."""
    return float_(FloatType.BIGFLOAT)


def integer(itype: IntegerType) -> LiteralType:
    """Construct an integer literal type."""
    return LiteralTypeInteger(itype)


def int8() -> LiteralType:
    """Construct an int8 literal type."""
    return integer(IntegerType.INT8)


def int16() -> LiteralType:
    """Construct an int16 literal type."""
    return integer(IntegerType.INT16)


def int32() -> LiteralType:
    """Construct an int32 literal type."""
    return integer(IntegerType.INT32)


def int64() -> LiteralType:
    """Construct an int64 literal type."""
    return integer(IntegerType.INT64)


def bigint() -> LiteralType:
    """Construct a bigint literal type."""
    return integer(IntegerType.BIGINT)


def uint8() -> LiteralType:
    """Construct a uint8 literal type."""
    return integer(IntegerType.UINT8)


def uint16() -> LiteralType:
    """Construct a uint16 literal type."""
    return integer(IntegerType.UINT16)


def uint32() -> LiteralType:
    """Construct a uint32 literal type."""
    return integer(IntegerType.UINT32)


def uint64() -> LiteralType:
    """Construct a uint64 literal type."""
    return integer(IntegerType.UINT64)


def show_literal_type(ltype: LiteralType) -> str:
    """Show a literal type as a string."""
    match ltype:
        case LiteralTypeBinary():
            return "binary"
        case LiteralTypeBoolean():
            return "boolean"
        case LiteralTypeFloat(value):
            match value:
                case FloatType.BIGFLOAT:
                    return "float:bigfloat"
                case FloatType.FLOAT32:
                    return "float:float32"
                case FloatType.FLOAT64:
                    return "float:float64"
        case LiteralTypeInteger(value):
            match value:
                case IntegerType.BIGINT:
                    return "integer:bigint"
                case IntegerType.INT8:
                    return "integer:int8"
                case IntegerType.INT16:
                    return "integer:int16"
                case IntegerType.INT32:
                    return "integer:int32"
                case IntegerType.INT64:
                    return "integer:int64"
                case IntegerType.UINT8:
                    return "integer:uint8"
                case IntegerType.UINT16:
                    return "integer:uint16"
                case IntegerType.UINT32:
                    return "integer:uint32"
                case IntegerType.UINT64:
                    return "integer:uint64"
        case LiteralTypeString():
            return "string"
