"""A model for Hydra namespaces and modules"""

from __future__ import annotations
from typing import Annotated, Callable, Literal, NewType, TypeVar
from dataclasses import dataclass, field
import hydra.core
import hydra.graph

FileExtension = str

@dataclass
class Library:
    """A library of primitive functions"""

    namespace: Annotated[Namespace, 'A common prefix for all primitive function names in the library']
    
    prefix: Annotated[str, 'A preferred namespace prefix for function names in the library']
    
    primitives: Annotated[list[hydra.graph.Primitive], 'The primitives defined in this library']

@dataclass
class Module:
    """A logical collection of elements in the same namespace, having dependencies on zero or more other modules"""

    namespace: Annotated[Namespace, 'A common prefix for all element names in the module']
    
    elements: Annotated[list[hydra.graph.Element], 'The elements defined in this module']
    
    term_dependencies: Annotated[list[Module], 'Any modules which the term expressions of this module directly depend upon']
    
    type_dependencies: Annotated[list[Module], 'Any modules which the type expressions of this module directly depend upon']
    
    description: Annotated[str | None, 'An optional human-readable description of the module']

Namespace = Annotated[str, 'A prefix for element names']

@dataclass
class QualifiedName:
    """A qualified name consisting of an optional namespace together with a mandatory local name"""

    namespace: Namespace | None
    
    local: str