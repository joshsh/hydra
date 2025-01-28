"""A model for Hydra transformation workflows."""

from __future__ import annotations
from collections.abc import Callable
from dataclasses import dataclass
from hydra.dsl.python import Variant
from typing import Annotated, Generic, TypeVar
import hydra.compute
import hydra.core
import hydra.graph
import hydra.module

A = TypeVar("A")
S = TypeVar("S")

@dataclass
class HydraSchemaSpec:
    """The specification of a Hydra schema, provided as a set of modules and a distinguished type."""
    
    modules: Annotated[list[hydra.module.Module], "The modules to include in the schema graph"]
    type_name: Annotated[hydra.core.Name, "The name of the top-level type; all data which passes through the workflow will be instances of this type"]

@dataclass
class LastMile(Generic[S, A]):
    """The last mile of a transformation, which encodes and serializes terms to a file."""
    
    encoder: Annotated[Callable[[hydra.core.Type], hydra.compute.Flow[S, Callable[[hydra.core.Term, hydra.graph.Graph], hydra.compute.Flow[S, list[A]]]]], "An encoder for terms to a list of output objects"]
    serializer: Annotated[Callable[[list[A]], hydra.compute.Flow[S, str]], "A function which serializes a list of output objects to a string representation"]
    file_extension: Annotated[str, "A file extension for the generated file(s)"]

class SchemaSpecHydra(Variant["HydraSchemaSpec"]):
    """A native Hydra schema."""

class SchemaSpecFile(Variant[str]):
    """A schema provided as a file, available at the given file path."""

class SchemaSpecProvided(Variant[None]):
    """A schema which will be provided within the workflow."""

# The specification of a schema at the source end of a workflow.
type SchemaSpec = SchemaSpecHydra | SchemaSpecFile | SchemaSpecProvided

@dataclass
class TransformWorkflow:
    """The specification of a workflow which takes a schema specification, reads data from a directory, and writes data to another directory."""
    
    name: Annotated[str, "A descriptive name for the workflow"]
    schema_spec: Annotated[SchemaSpec, "The schema specification"]
    src_dir: Annotated[str, "The source directory"]
    dest_dir: Annotated[str, "The destination directory"]