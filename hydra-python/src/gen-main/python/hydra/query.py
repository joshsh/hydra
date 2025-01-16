"""A model for language-agnostic graph pattern queries"""

from __future__ import annotations
from typing import Annotated, Literal, NewType
from dataclasses import dataclass
import hydra.core

ComparisonConstraintEqual = Literal["equal"]

ComparisonConstraintNotEqual = Literal["notEqual"]

ComparisonConstraintLessThan = Literal["lessThan"]

ComparisonConstraintGreaterThan = Literal["greaterThan"]

ComparisonConstraintLessThanOrEqual = Literal["lessThanOrEqual"]

ComparisonConstraintGreaterThanOrEqual = Literal["greaterThanOrEqual"]

ComparisonConstraint = Annotated[
    ComparisonConstraintEqual
    | ComparisonConstraintNotEqual
    | ComparisonConstraintLessThan
    | ComparisonConstraintGreaterThan
    | ComparisonConstraintLessThanOrEqual
    | ComparisonConstraintGreaterThanOrEqual,
    "One of several comparison operators",
]


@dataclass
class Edge:
    """An abstract edge based on a record type"""

    type: Annotated[
        hydra.core.Name,
        "The name of a record type, for which the edge also specifies an out- and an in- projection",
    ]

    out: Annotated[
        hydra.core.Name | None,
        "The field representing the out-projection of the edge. Defaults to 'out'.",
    ]

    in_: Annotated[
        hydra.core.Name | None,
        "The field representing the in-projection of the edge. Defaults to 'in'.",
    ]


@dataclass
class GraphPattern:
    """A query pattern which matches within a designated component subgraph"""

    graph: Annotated[hydra.core.Name, "The name of the component graph"]

    patterns: Annotated[list[Pattern], "The patterns to match within the subgraph"]


NodeTerm = Annotated[
    NewType("NodeTerm", hydra.core.Term),
    "A graph term; an expression which is valid in the graph being matched",
]

NodeVariable = Annotated[
    NewType("NodeVariable", Variable),
    "A query variable, not to be confused with a variable term",
]

NodeWildcard = Literal["wildcard"]

Node = Annotated[
    NodeTerm | NodeVariable | NodeWildcard,
    "A node in a query expression; it may be a term, a variable, or a wildcard",
]

PathStep = Annotated[NewType("PathStep", Step), "A path given by a single step"]

PathRegex = Annotated[
    NewType("PathRegex", RegexSequence),
    "A path given by a regular expression quantifier applied to another path",
]

PathInverse = Annotated[
    NewType("PathInverse", Path), "A path given by the inverse of another path"
]

Path = Annotated[PathStep | PathRegex | PathInverse, "A query path"]

PatternTriple = Annotated[
    NewType("PatternTriple", TriplePattern), "A subject/predicate/object pattern"
]

PatternNegation = Annotated[
    NewType("PatternNegation", Pattern), "The negation of another pattern"
]

PatternConjunction = Annotated[
    NewType("PatternConjunction", list[Pattern]),
    "The conjunction ('and') of several other patterns",
]

PatternDisjunction = Annotated[
    NewType("PatternDisjunction", list[Pattern]),
    "The disjunction (inclusive 'or') of several other patterns",
]

PatternGraph = Annotated[
    NewType("PatternGraph", GraphPattern),
    "A pattern which matches within a named subgraph",
]

Pattern = Annotated[
    PatternTriple
    | PatternNegation
    | PatternConjunction
    | PatternDisjunction
    | PatternGraph,
    "A query pattern",
]


@dataclass
class Query:
    """A SELECT-style graph pattern matching query"""

    variables: Annotated[list[Variable], "The variables selected by the query"]

    patterns: Annotated[list[Pattern], "The patterns to be matched"]


@dataclass
class Range:
    """A range from min to max, inclusive"""

    min: int

    max: int


RegexQuantifierOne = Literal["one"]

RegexQuantifierZeroOrOne = Literal["zeroOrOne"]

RegexQuantifierZeroOrMore = Literal["zeroOrMore"]

RegexQuantifierOneOrMore = Literal["oneOrMore"]

RegexQuantifierExactly = Annotated[
    NewType("RegexQuantifierExactly", int),
    "The {n} quantifier; matches exactly n occurrences",
]

RegexQuantifierAtLeast = Annotated[
    NewType("RegexQuantifierAtLeast", int),
    "The {n,} quantifier; matches at least n occurrences",
]

RegexQuantifierRange = Annotated[
    NewType("RegexQuantifierRange", Range),
    "The {n, m} quantifier; matches between n and m (inclusive) occurrences",
]

RegexQuantifier = Annotated[
    RegexQuantifierOne
    | RegexQuantifierZeroOrOne
    | RegexQuantifierZeroOrMore
    | RegexQuantifierOneOrMore
    | RegexQuantifierExactly
    | RegexQuantifierAtLeast
    | RegexQuantifierRange,
    "A regular expression quantifier",
]


@dataclass
class RegexSequence:
    """A path with a regex quantifier"""

    path: Path

    quantifier: RegexQuantifier


StepEdge = Annotated[
    NewType("StepEdge", Edge), "An out-to-in traversal of an abstract edge"
]

StepProject = Annotated[
    NewType("StepProject", hydra.core.Projection),
    "A projection from a record through one of its fields",
]

StepCompare = Annotated[
    NewType("StepCompare", ComparisonConstraint), "A comparison of two terms"
]

Step = Annotated[
    StepEdge | StepProject | StepCompare,
    "An atomic function as part of a query. When applied to a graph, steps are typed by function types.",
]


@dataclass
class TriplePattern:
    """A subject/predicate/object pattern"""

    subject: Node

    predicate: Path

    object: Node


Variable = Annotated[str, "A query variable"]
