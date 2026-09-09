from collections.abc import Set
from dataclasses import dataclass
from typing import Generic, TypeVar

from .implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(slots=True)
class PartialObject(Generic[O, A]):

    object: O

    positive: Set[A]
    negative: Set[A]

    def __post_init__(self):
        overlap = self.positive & self.negative
        if overlap:
            raise ValueError(
                f'Positive and negative attributes overlap: {overlap}'
            )

    def refutes(
            self,
            implication: Implication[A],
    ) -> bool:
        return (
                implication.premise <= self.positive
                and
                bool(implication.conclusion & self.negative)
        )

    def __str__(self) -> str:
        positive = "{" + ", ".join(map(str, self.positive)) + "}"
        negative = "{" + ", ".join(map(str, self.negative)) + "}"
        return f"{self.object}[{positive}, {negative}]"