"""Checking the result of an exploration from its evidence.

An exploration ends with implications and a context whose closure systems
should coincide: the sets closed under the implications should be exactly the
intents of the context. Once each implication is known to hold, by a proof,
and each object to be an example, by a check of its row, this comparison is
what remains to show that the implications are a basis of the theory.
`check_closure_systems` does it on bitmasks, attribute i being bit i, with
its own closures and NextClosure, so that it does not rest on the code that
ran the exploration.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from concurrent.futures import ProcessPoolExecutor


class VerificationError(ValueError):
    pass


class _Closure:
    """The closure under implications, with the implications indexed by the
    attributes of their premises."""

    def __init__(self, attributes: int, rules: Sequence[tuple[int, int]]):
        self.start = 0  # the conclusions of the implications with empty premises
        self.by_attribute: list[list[tuple[int, int]]] = [[] for _ in range(attributes)]
        for premise, conclusion in rules:
            if premise == 0:
                self.start |= conclusion
            mask = premise
            while mask:
                low = mask & -mask
                self.by_attribute[low.bit_length() - 1].append((premise, conclusion))
                mask ^= low

    def __call__(self, mask: int, target: int | None = None) -> int:
        """The closure of mask, or `target` as soon as that is reached: the
        closure is no larger when the implications hold in the context and
        `target` is the intent the mask generates."""
        mask |= self.start
        new = mask
        while new and mask != target:
            low = new & -new
            new ^= low
            for premise, conclusion in self.by_attribute[low.bit_length() - 1]:
                if premise & ~mask == 0 and conclusion & ~mask:
                    new |= conclusion & ~mask
                    mask |= conclusion
        return mask


_worker_closure: _Closure | None = None


def _start_worker(attributes: int, rules: Sequence[tuple[int, int]]) -> None:
    global _worker_closure
    _worker_closure = _Closure(attributes, rules)


def _disagreements(queries: Sequence[tuple[int, int]]) -> list[int]:
    return [mask for mask, value in queries if _worker_closure(mask, value) != value]


def check_closure_systems(
        attributes: int,
        intents: Sequence[int],
        implications: Iterable[tuple[int, int]],
        processes: int = 1,
) -> int:
    """The number of sets closed under the implications, (premise,
    conclusion) pairs of masks, after checking that these sets are exactly
    the intents of the context whose objects have the given intents; raises
    VerificationError if they are not.

    Every object intent must respect every implication. Then NextClosure
    runs with the closure of the context, the intersection of the object
    intents containing a set, and at each set it asks the closure of, the
    closure under the implications must be the same. NextClosure lists the
    closed sets of whatever closure it is given, and what it does depends
    only on the closures it gets: with the implications it would have done
    the same, and listed the same sets. The implications' closures are
    computed in `processes` processes.
    """
    full = (1 << attributes) - 1
    merged: dict[int, int] = {}
    for premise, conclusion in implications:
        merged[premise] = merged.get(premise, 0) | conclusion
    rules = [(premise, conclusion & ~premise) for premise, conclusion in merged.items() if conclusion & ~premise]
    for k, intent in enumerate(intents):
        for premise, conclusion in rules:
            if premise & ~intent == 0 and conclusion & ~intent:
                raise VerificationError(f"Object {k} violates an implication")

    def intent_closure(mask: int) -> int:
        result = full
        for intent in intents:
            if mask & ~intent == 0:
                result &= intent
        return result

    # NextClosure, attribute 0 the most significant in the lectic order, and
    # the sets it asks the closures of.
    closed = intent_closure(0)
    queries = [(0, closed)]
    count = 1
    while closed != full:
        for i in range(attributes - 1, -1, -1):
            bit = 1 << i
            if closed & bit:
                continue
            lower = closed & (bit - 1)
            candidate = intent_closure(lower | bit)
            queries.append((lower | bit, candidate))
            if candidate & (bit - 1) == lower:
                closed = candidate
                count += 1
                break
    if processes <= 1:
        _start_worker(attributes, rules)
        wrong = _disagreements(queries)
    else:
        chunk = -(-len(queries) // (4 * processes))
        with ProcessPoolExecutor(processes, initializer=_start_worker, initargs=(attributes, rules)) as pool:
            wrong = [mask for part in pool.map(_disagreements, [queries[k:k + chunk]
                                                                for k in range(0, len(queries), chunk)])
                     for mask in part]
    if wrong:
        raise VerificationError(f"The closures of {len(wrong)} sets under the implications are not intents, "
                                f"the first {wrong[0]:#x}")
    return count
