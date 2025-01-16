"""The extension to graphs of Hydra's core type system (hydra/core)"""

from __future__ import annotations
from typing import Annotated, Literal, TypeVar
from collections.abc import Callable
from dataclasses import dataclass
import hydra.compute
import hydra.core

X = TypeVar("X")

ComparisonLessThan = Literal["lessThan"]

ComparisonEqualTo = Literal["equalTo"]

ComparisonGreaterThan = Literal["greaterThan"]

Comparison = Annotated[
    ComparisonLessThan | ComparisonEqualTo | ComparisonGreaterThan,
    "An equality judgement: less than, equal to, or greater than",
]


@dataclass
class Graph:
    """A graph, or set of name/term bindings together with parameters (annotations, primitives) and a schema graph"""

    elements: Annotated[
        dict[hydra.core.Name, Element], "All of the elements in the graph"
    ]

    environment: Annotated[
        dict[hydra.core.Name, hydra.core.Term | None],
        "The lambda environment of this graph context; it indicates whether a variable is bound by a lambda (Nothing) or a let (Just term)",
    ]

    types: Annotated[
        dict[hydra.core.Name, hydra.core.TypeScheme],
        "The typing environment of the graph",
    ]

    body: Annotated[
        hydra.core.Term, "The body of the term which generated this context"
    ]

    primitives: Annotated[
        dict[hydra.core.Name, Primitive],
        "All supported primitive constants and functions, by name",
    ]

    schema: Annotated[
        Graph | None,
        "The schema of this graph. If this parameter is omitted (nothing), the graph is its own schema graph.",
    ]


@dataclass
class Element:
    """A graph element, having a name, data term (value), and schema term (type)"""

    name: hydra.core.Name

    data: hydra.core.Term


@dataclass
class Primitive:
    """A built-in function"""

    name: Annotated[hydra.core.Name, "The unique name of the primitive function"]

    type: Annotated[
        hydra.core.TypeScheme, "The type signature of the primitive function"
    ]

    implementation: Annotated[
        Callable[[list[hydra.core.Term]], hydra.compute.Flow[Graph, hydra.core.Term]],
        "A concrete implementation of the primitive function",
    ]


@dataclass
class TermCoder(Generic[X]):
    """A type together with a coder for mapping terms into arguments for primitive functions, and mapping computed results into terms"""

    type: hydra.core.Type

    coder: hydra.compute.Coder[Graph, Graph, hydra.core.Term, X]


TypeClassEquality = Literal["equality"]

TypeClassOrdering = Literal["ordering"]

TypeClass = Annotated[
    TypeClassEquality | TypeClassOrdering,
    "Any of a small number of built-in type classes",
]
