"""A common API for Hydra union types in Python."""

from typing import TypeVar, Generic
from dataclasses import dataclass

T = TypeVar("T")

@dataclass
class Variant(Generic[T]):
    """A helper class for variants (alternatives) of Hydra union types in Python."""

    value: T
