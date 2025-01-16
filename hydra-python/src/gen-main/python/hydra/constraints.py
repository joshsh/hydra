"""A model for path- and pattern-based graph constraints, which may be considered as part of the schema of a graph"""

from __future__ import annotations
from typing import Annotated, Callable, Literal, NewType, TypeVar
from dataclasses import dataclass, field
import hydra.core
import hydra.query


@dataclass
class PathEquation:
    """A declared equivalence between two abstract paths in a graph"""

    left: hydra.query.Path

    right: hydra.query.Path


@dataclass
class PatternImplication:
    """A pattern which, if it matches in a given graph, implies that another pattern must also match. Query variables are shared between the two patterns."""

    antecedent: hydra.query.Pattern

    consequent: hydra.query.Pattern
