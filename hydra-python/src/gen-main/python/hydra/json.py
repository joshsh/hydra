"""A JSON syntax model. See the BNF at https://www.json.org"""

from __future__ import annotations
from typing import Annotated, Literal, NewType

ValueArray = Annotated[NewType("ValueArray", list[Value]), "A JSON array"]

ValueBoolean = Annotated[NewType("ValueBoolean", bool), "A boolean value"]

ValueNull = Literal["null"]

ValueNumber = Annotated[NewType("ValueNumber", float), "A numeric value"]

ValueObject = Annotated[
    NewType("ValueObject", dict[str, Value]),
    "A JSON object as a set of key/value pairs",
]

ValueString = Annotated[NewType("ValueString", str), "A string value"]

Value = Annotated[
    ValueArray | ValueBoolean | ValueNull | ValueNumber | ValueObject | ValueString,
    "A JSON value",
]
