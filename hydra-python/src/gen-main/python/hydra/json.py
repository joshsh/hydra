"""A JSON syntax model. See the BNF at https://www.json.org."""

from __future__ import annotations
from hydra.dsl.types import Variant

class ValueArray(Variant["list[Value]"]):
    """A JSON array."""

class ValueBoolean(Variant[bool]):
    """A boolean value."""

class ValueNull(Variant[None]):
    """JSON's null value."""

class ValueNumber(Variant[float]):
    """A numeric value."""

class ValueObject(Variant["dict[str, Value]"]):
    """A JSON object as a set of key/value pairs."""

class ValueString(Variant[str]):
    """A string value."""

# A JSON value.
type Value = ValueArray | ValueBoolean | ValueNull | ValueNumber | ValueObject | ValueString