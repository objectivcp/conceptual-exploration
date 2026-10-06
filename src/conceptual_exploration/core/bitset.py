from collections.abc import Iterable, Iterator
from typing import Generic, TypeVar

A = TypeVar("A")


def bits(mask: int) -> Iterator[int]:
    """Yield the positions of the set bits of `mask`, lowest first."""
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


class AttributeIndex(Generic[A]):
    """Numbers attributes so that sets of them can be held as int bitmasks.

    Attribute i is bit i. Encoding an attribute the index has not seen gives it
    the next free bit, so an index can start empty and grow as attributes turn
    up. Hashing an attribute happens once, when it is encoded; everything that
    then runs on the masks — closures, subset tests, mappings — is integer work.
    """

    def __init__(self, attributes: Iterable[A] = ()) -> None:
        self.attributes: list[A] = []
        self.positions: dict[A, int] = {}
        for a in attributes:
            self.bit(a)

    def __len__(self) -> int:
        return len(self.attributes)

    def bit(self, attribute: A) -> int:
        position = self.positions.get(attribute)
        if position is None:
            position = len(self.attributes)
            self.positions[attribute] = position
            self.attributes.append(attribute)
        return 1 << position

    def encode(self, attributes: Iterable[A]) -> int:
        mask = 0
        for a in attributes:
            mask |= self.bit(a)
        return mask

    def decode(self, mask: int) -> set[A]:
        return {self.attributes[i] for i in bits(mask)}
