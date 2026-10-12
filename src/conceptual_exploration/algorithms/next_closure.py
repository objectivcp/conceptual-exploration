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

    def generate_masks(self, start: int | None = None) -> Generator[int, bool | None, None]:
        """The closed sets in lectic order, from the first or from `start` on.

        Started at a set, the enumeration yields it if it is closed and goes
        on with the closed sets lectically after it. Any set will do, since
        the step from a set to the next closed one does not need it to be
        closed itself; this is how an enumeration is resumed.
        """
        closure = self.mask_closure_operator

        if start is None:
            s = closure(0)
            if (yield s):  # closure of s changed by caller
                s = closure(s)
        else:
            s = start
            if closure(s) == s:
                # Whatever the caller does with it, the next closed set is
                # the one after `start` under the closure as it then stands.
                yield s

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
