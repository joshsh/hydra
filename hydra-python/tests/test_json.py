from hydra.json import (
    Value,
    ValueArray,
    ValueBoolean,
    ValueNull,
    ValueNumber,
    ValueObject,
    ValueString,
)
from dataclasses import dataclass
from typing import Generic, TypeVar

type JsonValue = (
    dict[str, "JsonValue"] | list["JsonValue"] | bool | float | int | str | None
)


def from_hydra_json(v: Value) -> JsonValue:
    match v:
        case ValueArray(value):
            return [from_hydra_json(v) for v in value]
        case ValueObject(value):
            return {k: from_hydra_json(v) for k, v in value.items()}
        case ValueBoolean(value):
            return value
        case ValueNull():
            return None
        case ValueNumber(value):
            return value
        case ValueString(value):
            return value


def test_json():
    v0 = ValueObject(
        {
            "a": ValueArray([ValueNumber(5), ValueNumber(6)]),
            "c": ValueString("hello"),
            "d": ValueBoolean(True),
            "e": ValueNull(None),
        }
    )
    assert from_hydra_json(v0) == {"a": [5, 6], "c": "hello", "d": True, "e": None}


T = TypeVar("T")
A = TypeVar("A")

@dataclass
class Node(Generic[T]):
    """A wrapper for another type; a NewType alternative which allows type parameters."""
    
    value: T


class Name(Node[str]):
    """A wrapper for another type; a NewType alternative which allows type parameters."""
  
class TTerm(Node[Name], Generic[A]): ...