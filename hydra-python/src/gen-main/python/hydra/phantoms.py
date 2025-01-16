"""Phantom types for use with Hydra DSLs"""

from __future__ import annotations
from typing import Annotated, TypeVar
from dataclasses import dataclass
import hydra.core

A = TypeVar("A")

TCase = Annotated[
    hydra.core.Name,
    "An association of a field name (as in a case statement) with a phantom type",
]


@dataclass
class TElement(Generic[A]):
    """An association with a named term (element) with a phantom type"""

    name: hydra.core.Name

    term: TTerm[A]


TField = Annotated[
    hydra.core.Field, "An association with a term-level field with a phantom type"
]

TTerm = Annotated[hydra.core.Term, "An association of a term with a phantom type"]
