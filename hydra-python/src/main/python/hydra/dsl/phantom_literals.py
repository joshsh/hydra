"""A DSL for constructing literal terms using Python's built-in datatypes."""

from hydra.phantoms import TTerm
import hydra.dsl.terms as terms

type Bigfloat = float


def string(value: str) -> TTerm[str]:
    """Construct a string term."""
    return TTerm[str](terms.string(value))


def boolean(value: bool) -> TTerm[bool]:
    """Construct a boolean term."""
    return TTerm[bool](terms.boolean(value))

def true() -> TTerm[bool]:
    """Construct a true term."""
    return boolean(True)


def false() -> TTerm[bool]:
    """Construct a false term."""
    return boolean(False)


def bigfloat(value: Bigfloat) -> TTerm[Bigfloat]:
    """Construct a bigfloat term."""
    return TTerm[Bigfloat](terms.bigfloat(value))


def bigint(value: int) -> TTerm[int]:
    """Construct a bigint term."""
    return TTerm[int](terms.bigint(value))


def binary(value: bytes) -> TTerm[bytes]:
    """Construct a binary term."""
    return TTerm[bytes](terms.binary(value))



def double(value: float) -> TTerm[float]:
    """Construct a double term."""
    return TTerm[float](terms.float64(value))


def float_(value: float) -> TTerm[float]:
    """Construct a float term."""
    return float32(value)


def float32(value: float) -> TTerm[float]:
    """Construct a float32 term."""
    return TTerm[float](terms.float32(value))


def float64(value: float) -> TTerm[float]:
    """Construct a float64 term."""
    return TTerm[float](terms.float64(value))


def integer(value: int) -> TTerm[int]:
    """Construct an int term."""
    return int32(value)


def int8(value: int) -> TTerm[int]:
    """Construct an int8 term."""
    return TTerm[int](terms.int8(value))


def int16(value: int) -> TTerm[int]:
    """Construct an int16 term."""
    return TTerm[int](terms.int16(value))


def int32(value: int) -> TTerm[int]:
    """Construct an int32 term."""
    return TTerm[int](terms.int32(value))


def int64(value: int) -> TTerm[int]:
    """Construct an int64 term."""
    return TTerm[int](terms.int64(value))
