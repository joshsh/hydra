"""Phantom types for use with Hydra DSLs."""

from __future__ import annotations
from dataclasses import dataclass
from typing import Generic, TypeVar
import hydra.core

A = TypeVar("A")

# An association of a field name (as in a case statement) with a phantom type.
type TCase = hydra.core.Name

@dataclass
class TElement(Generic[A]):
    """An association with a named term (element) with a phantom type."""
    
    name: hydra.core.Name
    term: TTerm[A]

# An association with a term-level field with a phantom type.
type TField = hydra.core.Field

# An association of a term with a phantom type.
type TTerm = hydra.core.Term