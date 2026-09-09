from dataclasses import dataclass
from typing import Generic, Iterable
from typing import TypeVar

A = TypeVar("A")


@dataclass(frozen=True, slots=True)
class Implication(Generic[A]):
    premise: frozenset[A]
    conclusion: frozenset[A]

    def __init__(
        self,
        premise: Iterable[A],
        conclusion: Iterable[A],
    ):
        object.__setattr__(self, "premise", frozenset(premise))
        object.__setattr__(self, "conclusion", frozenset(conclusion))

    def __lt__(self, other: "Implication[A]") -> bool:
        if not isinstance(other, Implication):
            return NotImplemented

        return (
            len(self.premise),
            sorted(self.premise),
            len(self.conclusion),
            sorted(self.conclusion),
        ) < (
            len(other.premise),
            sorted(other.premise),
            len(other.conclusion),
            sorted(other.conclusion),
        )

    def respected_by(
        self,
        attributes: frozenset[A],
    ) -> bool:

        return self.conclusion <= attributes or not self.premise <= attributes

    def __str__(self) -> str:

        lhs = ", ".join(
            map(str, sorted(self.premise))
        )

        rhs = ", ".join(
            map(str, sorted(self.conclusion))
        )

        return f"{lhs} -> {rhs}"