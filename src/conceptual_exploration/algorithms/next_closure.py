from collections.abc import Callable, Generator
from typing import Generic, TypeVar

from ..core.bitset import AttributeIndex

A = TypeVar("A")


class NextClosure(Generic[A]):
    """Ganter's NextClosure over `attributes`, in their lectic order.

    `generate` works on attribute sets and calls `closure_operator` on sets.
    `generate_masks` is the same enumeration over bitmasks, where attribute i
    is bit i; it calls `mask_closure_operator`, which the exploration engine
    supplies to avoid converting between sets and masks at every step.
    """

    def __init__(
            self,
            attributes,
            closure_operator=None,
            *,
            mask_closure_operator: Callable[[int], int] | None = None,
    ):
        self.attributes = tuple(attributes)
        self.closure_operator = closure_operator
        self.index = AttributeIndex(self.attributes)
        if mask_closure_operator is None:
            mask_closure_operator = lambda mask: self.index.encode(
                closure_operator(self.index.decode(mask))
            )
        self.mask_closure_operator = mask_closure_operator

    def generate(self) -> Generator[frozenset[A], bool | None, None]:
        masks = self.generate_masks()
        try:
            mask = next(masks)
            while True:
                changed = yield frozenset(self.index.decode(mask))
                mask = masks.send(changed)
        except StopIteration:
            return

    def generate_masks(self) -> Generator[int, bool | None, None]:
        closure = self.mask_closure_operator

        s = closure(0)
        if (yield s):  # closure of s changed by caller
            s = closure(s)

        i = len(self.attributes)
        while i > 0:
            i -= 1
            bit = 1 << i
            prefix = bit - 1
            if s & bit:
                s ^= bit
            else:
                t = closure(s | bit)
                if (t & ~s) & prefix == 0:
                    if (yield t):
                        t_closed = closure(t)
                        if (t_closed & ~t) & prefix == 0:
                            s = t_closed
                            i = len(self.attributes)
                    else:
                        s = t
                        i = len(self.attributes)
