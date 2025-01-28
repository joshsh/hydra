"""A collection of foundational typing constructs specific to Hydra-Python."""

from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")


@dataclass
class Variant(Generic[T]):
    """A variant type."""

    value: T
