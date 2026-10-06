from collections.abc import Set, MutableSet, Iterator, Iterable
from typing import TypeVar

from ..algorithms.closure import ClosureOperator
from .bitset import AttributeIndex
from .implication import Implication

A = TypeVar("A")


def close_mask(mask: int, implications: Iterable[tuple[int, int]]) -> int:
    """Close an attribute mask under implications given as (premise,
    conclusion) mask pairs."""
    # An implication that has fired can fire no further, so each pass only
    # looks at the ones whose premise was not yet contained.
    pending = implications
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
        self._mask_set: set[tuple[int, int]] = set()
        for implication in implications:
            self.add(implication)

    def __iter__(self) -> Iterator[Implication[A]]:
        return iter(self.implications)

    def add(self, implication: Implication[A]) -> tuple[int, int]:
        """Add an implication and return its premise and conclusion masks."""
        self.implications.append(implication)
        masks = self._encode(implication)
        self._masks.append(masks)
        self._mask_set.add(masks)
        return masks

    def _encode(self, implication: Implication[A]) -> tuple[int, int]:
        return (
            self.index.encode(implication.premise),
            self.index.encode(implication.conclusion),
        )

    def closure_mask(self, mask: int) -> int:
        if len(self._masks) != len(self.implications):
            # Someone appended to `implications` directly; catch the masks up.
            missing = list(map(self._encode, self.implications[len(self._masks):]))
            self._masks.extend(missing)
            self._mask_set.update(missing)
        return close_mask(mask, self._masks)

    def entails_mask(self, premise: int, conclusion: int) -> bool:
        # An implication the theory contains needs no closure; mapping a
        # theory closed under the mappings produces nothing but those.
        if conclusion & ~premise == 0 or (premise, conclusion) in self._mask_set:
            return True
        return conclusion & ~self.closure_mask(premise) == 0

    def closure(self, attributes: Set[A]) -> MutableSet[A]:
        return self.index.decode(self.closure_mask(self.index.encode(attributes)))

    def respected_by(self, attributes: frozenset[A], ) -> bool:
        return all(implication.respected_by(attributes) for implication in self.implications)

    def entails(self, implication: Implication[A]) -> bool:
        return self.entails_mask(*self._encode(implication))

    def simplify(self, implication: Implication[A]) -> Implication[A]:
        """Drop the premise attributes the rest of the premise entails.

        Which attributes survive depends on the order they are tried in, so they
        are tried in sorted order: set iteration order varies with hashing, and
        would make the result differ from one run to the next.
        """
        simplified_premise = set(implication.premise)
        for a in sorted(implication.premise):
            if a in self.closure(simplified_premise - {a}):
                simplified_premise -= {a}
        return Implication(
            simplified_premise,
            implication.conclusion - implication.premise
        )
