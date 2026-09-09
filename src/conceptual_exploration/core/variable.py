from dataclasses import dataclass
from enum import Enum


@dataclass(frozen=True, slots=True)
class Variable:
    name: str

    def __str__(self) -> str:
        return self.name

    def __lt__(self, other: "Variable") -> bool:
        if not isinstance(other, Variable):
            return NotImplemented
        return self.name < other.name


class Sort(Enum):
    ...


@dataclass(frozen=True, slots=True)
class SortedVariable(Variable):
    sort: Sort