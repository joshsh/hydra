"""A collection of foundational typing constructs specific to Hydra-Python."""

from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")


@dataclass
class Node(Generic[T]):
    """A wrapper for another type; a NewType alternative which allows type parameters."""

    value: T
