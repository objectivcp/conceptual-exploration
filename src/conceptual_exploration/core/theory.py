from collections.abc import Set, MutableSet, Iterator, Iterable
from typing import TypeVar

from ..algorithms.closure import ClosureOperator
from .bitset import AttributeIndex
from .implication import Implication

A = TypeVar("A")


class ImplicationTheory(ClosureOperator[A]):
    """A list of implications together with the closure operator they define.

    Each implication is also kept as a pair of bitmasks over `index`, and the
    closures are computed on those; the set-based methods encode their argument
    and decode the result. Callers that work with masks themselves — the
    exploration engine does — pass their own index so the bits agree, and call
    `closure_mask` directly.
    """

    def __init__(
            self,
            implications: Iterable[Implication[A]] = (),
            index: AttributeIndex[A] | None = None,
    ):
        self.index = index if index is not None else AttributeIndex[A]()
        self.implications: list[Implication[A]] = []
        self._masks: list[tuple[int, int]] = []
        for implication in implications:
            self.add(implication)

    def __iter__(self) -> Iterator[Implication[A]]:
        return iter(self.implications)

    def add(self, implication: Implication[A]) -> tuple[int, int]:
        """Add an implication and return its premise and conclusion masks."""
        self.implications.append(implication)
        masks = self._encode(implication)
        self._masks.append(masks)
        return masks

    def _encode(self, implication: Implication[A]) -> tuple[int, int]:
        return (
            self.index.encode(implication.premise),
            self.index.encode(implication.conclusion),
        )

    def closure_mask(self, mask: int) -> int:
        if len(self._masks) != len(self.implications):
            # Someone appended to `implications` directly; catch the masks up.
            self._masks.extend(
                map(self._encode, self.implications[len(self._masks):])
            )
        # An implication that has fired can fire no further, so each pass only
        # looks at the ones whose premise was not yet contained.
        pending = self._masks
        changed = True
        while changed:
            changed = False
            waiting = []
            for premise, conclusion in pending:
                if premise & mask == premise:
                    if conclusion & ~mask:
                        mask |= conclusion
                        changed = True
                else:
                    waiting.append((premise, conclusion))
            pending = waiting
        return mask

    def entails_mask(self, premise: int, conclusion: int) -> bool:
        return conclusion & ~self.closure_mask(premise) == 0

    def closure(self, attributes: Set[A]) -> MutableSet[A]:
        return self.index.decode(self.closure_mask(self.index.encode(attributes)))

    def respected_by(self, attributes: frozenset[A], ) -> bool:
        return all(implication.respected_by(attributes) for implication in self.implications)

    def entails(self, implication: Implication[A]) -> bool:
        return self.entails_mask(*self._encode(implication))

    def simplify(self, implication: Implication[A]) -> Implication[A]:
        simplified_premise = set(implication.premise)
        for a in implication.premise:
            if a in self.closure(simplified_premise - {a}):
                simplified_premise -= {a}
        return Implication(
            simplified_premise,
            implication.conclusion - implication.premise
        )
