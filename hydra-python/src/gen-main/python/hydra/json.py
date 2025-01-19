"""A JSON syntax model. See the BNF at https://www.json.org."""

from __future__ import annotations
from typing import Literal, NewType

# A JSON array
ValueArray = NewType("ValueArray", list[Value])

# A boolean value
ValueBoolean = NewType("ValueBoolean", bool)

ValueNull = Literal["null"]

# A numeric value
ValueNumber = NewType("ValueNumber", float)

# A JSON object as a set of key/value pairs
ValueObject = NewType("ValueObject", dict[str, Value])

# A string value
ValueString = NewType("ValueString", str)

# A JSON value.
Value = ValueArray | ValueBoolean | ValueNull | ValueNumber | ValueObject | ValueString