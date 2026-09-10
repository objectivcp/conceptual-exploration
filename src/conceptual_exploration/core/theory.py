from collections.abc import Set, MutableSet, Iterator, Iterable
from typing import TypeVar

from ..algorithms.closure import ClosureOperator
from .implication import Implication

A = TypeVar("A")


class ImplicationTheory(ClosureOperator[A]):

    def __init__(
            self,
            implications: Iterable[Implication[A]] = (),
    ):
        self.implications: list[Implication[A]] = list(implications)

    def __iter__(self) -> Iterator[Implication[A]]:
        return iter(self.implications)

    def add(self, implication: Implication[A]) -> None:
        self.implications.append(implication)

    def closure(self, attributes: Set[A]) -> MutableSet[A]:
        result = set(attributes)
        changed = True
        while changed:
            changed = False
            for implication in self.implications:
                if implication.premise <= result:
                    old_size = len(result)
                    result |= implication.conclusion
                    changed |= (len(result) > old_size)
        return result

    def respected_by(self, attributes: frozenset[A], ) -> bool:
        return all(implication.respected_by(attributes) for implication in self.implications)

    def entails(self, implication: Implication[A]) -> bool:
        return implication.conclusion <= self.closure(implication.premise)

    def simplify(self, implication: Implication[A]) -> Implication[A]:
        simplified_premise = set(implication.premise)
        for a in implication.premise:
            if a in self.closure(simplified_premise - {a}):
                simplified_premise -= {a}
        return Implication(
            simplified_premise,
            implication.conclusion - implication.premise
        )