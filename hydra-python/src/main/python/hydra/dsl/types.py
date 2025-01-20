"""A domain-specific language for constructing Hydra types in Python."""

from typing import TypeVar, Generic
from dataclasses import dataclass

T = TypeVar("T")

@dataclass
class Variant(Generic[T]):
    """A helper class for variants (alternatives) of Hydra union types."""

    value: T
