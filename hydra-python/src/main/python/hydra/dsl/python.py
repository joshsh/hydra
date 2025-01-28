"""A library for python utilities."""

from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")


@dataclass
class Variant(Generic[T]):
    """A variant type."""

    value: T
