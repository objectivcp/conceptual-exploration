from collections.abc import Set, MutableSet, Iterator, Iterable
from typing import TypeVar

from ..algorithms.closure import ClosureOperator
from .bitset import AttributeIndex, bits
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

    For closures the theory is also kept transposed: for each attribute, a
    bitmask over the implications (by number) whose premise contains it, and
    one over those whose conclusion does. The implications that can fire are
    then those that no absent attribute's premise mask covers, and an absent
    attribute is derived when its conclusion mask meets them, so a round of
    the closure is a big-integer operation per attribute rather than a step
    per implication. Ruling out the implications whose premise has an absent
    attribute is similar to Wild's closure algorithm; the conclusion masks
    are added so that what fires is read off per attribute as well.
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
        # The transposed theory, by attribute position: the implications
        # whose premise, and those whose conclusion, contains the attribute.
        self._in_premise: dict[int, int] = {}
        self._in_conclusion: dict[int, int] = {}
        for implication in implications:
            self.add(implication)

    def __iter__(self) -> Iterator[Implication[A]]:
        return iter(self.implications)

    def add(self, implication: Implication[A]) -> tuple[int, int]:
        """Add an implication and return its premise and conclusion masks."""
        self.implications.append(implication)
        masks = self._encode(implication)
        self._record(masks)
        return masks

    def _record(self, masks: tuple[int, int]) -> None:
        premise, conclusion = masks
        number = 1 << len(self._masks)
        self._masks.append(masks)
        self._mask_set.add(masks)
        for position in bits(premise):
            self._in_premise[position] = self._in_premise.get(position, 0) | number
        for position in bits(conclusion):
            self._in_conclusion[position] = self._in_conclusion.get(position, 0) | number

    def _encode(self, implication: Implication[A]) -> tuple[int, int]:
        return (
            self.index.encode(implication.premise),
            self.index.encode(implication.conclusion),
        )

    def closure_mask(self, mask: int) -> int:
        if len(self._masks) != len(self.implications):
            # Someone appended to `implications` directly; catch the masks up.
            for implication in self.implications[len(self._masks):]:
                self._record(self._encode(implication))

        everything = (1 << len(self._masks)) - 1
        result = mask
        while True:
            # The implications with a premise attribute the result lacks
            # cannot fire; the rest have fired or are about to.
            blocked = 0
            for position, implications in self._in_premise.items():
                if not result >> position & 1:
                    blocked |= implications
            firing = everything & ~blocked
            new = 0
            for position, implications in self._in_conclusion.items():
                if implications & firing and not result >> position & 1:
                    new |= 1 << position
            if not new:
                return result
            result |= new

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
