"""Checking the result of an exploration from its evidence.

An exploration ends with implications and a context whose closure systems
should coincide: the sets closed under the implications should be exactly the
intents of the context. Once each implication is known to hold, by a proof,
and each object to be an example, by a check of its row, this comparison is
what remains to show that the implications are a basis of the theory.
`check_closure_systems` does it on bitmasks, attribute i being bit i, with
its own closures and NextClosure, so that it does not rest on the code that
ran the exploration. An exploration that ended with open questions, as one
that rejects undecided implications tentatively, has instead a list of the
closed sets that no object settles, each with its open attributes;
`check_open_closure_systems` checks that list.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from concurrent.futures import ProcessPoolExecutor


class VerificationError(ValueError):
    pass


class _Closure:
    """The closure under implications, with the implications indexed by the
    attributes of their premises."""

    def __init__(self, attributes: int, implications: Sequence[tuple[int, int]]):
        self.start = 0  # the conclusions of the implications with empty premises
        self.by_attribute: list[list[tuple[int, int]]] = [[] for _ in range(attributes)]
        for premise, conclusion in implications:
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


def _start_worker(attributes: int, implications: Sequence[tuple[int, int]]) -> None:
    global _worker_closure
    _worker_closure = _Closure(attributes, implications)


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
    merged_implications = [(premise, conclusion & ~premise) for premise, conclusion in merged.items()
                           if conclusion & ~premise]
    for k, intent in enumerate(intents):
        for premise, conclusion in merged_implications:
            if premise & ~intent == 0 and conclusion & ~intent:
                raise VerificationError(f"Object {k} violates an implication")

    # The objects having each attribute, as bitmasks over the objects: the
    # objects having a set's attributes are the intersection of their
    # columns, and its closure the attributes all of these have.
    extents = [sum(1 << k for k, intent in enumerate(intents) if intent >> j & 1) for j in range(attributes)]
    everyone = (1 << len(intents)) - 1

    def intent_closure(mask: int) -> int:
        extent = everyone
        while mask:
            low = mask & -mask
            mask ^= low
            extent &= extents[low.bit_length() - 1]
        return sum(1 << j for j in range(attributes) if extent & ~extents[j] == 0)

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
        _start_worker(attributes, merged_implications)
        wrong = _disagreements(queries)
    else:
        chunk = -(-len(queries) // (4 * processes))
        with ProcessPoolExecutor(processes, initializer=_start_worker, initargs=(attributes, merged_implications)) as pool:
            wrong = [mask for part in pool.map(_disagreements, [queries[k:k + chunk]
                                                                for k in range(0, len(queries), chunk)])
                     for mask in part]
    if wrong:
        raise VerificationError(f"The closures of {len(wrong)} sets under the implications are not intents, "
                                f"the first {wrong[0]:#x}")
    return count


def check_open_closure_systems(
        attributes: int,
        rows: Sequence[tuple[int, int]],
        implications: Iterable[tuple[int, int]],
        open_sets: dict[int, int],
) -> tuple[int, int]:
    """For an exploration that ended with open questions: the number of sets
    closed under the implications, and how many of them the objects settle,
    after checking that the others are exactly the keys of `open_sets`, each
    with its open laws as the value; raises VerificationError if not.

    A row is a pair of masks, the attributes an object certainly has and
    those it certainly lacks, the rest unknown. Every row must respect every
    implication: an object that has a premise lacks none of its conclusion.
    The objects settle a closed set when each other attribute is lacked by
    an object that has the set; its open attributes are those that no such
    object lacks. NextClosure lists the closed sets of the implications.
    Then every implication with a single attribute as conclusion follows
    from the implications, is refuted by an object, or has as premise a
    listed set, up to closure, and as conclusion one of its open attributes.
    """
    full = (1 << attributes) - 1
    merged: dict[int, int] = {}
    for premise, conclusion in implications:
        merged[premise] = merged.get(premise, 0) | conclusion
    merged_implications = [(premise, conclusion & ~premise) for premise, conclusion in merged.items()
                           if conclusion & ~premise]
    for k, (has, lacks) in enumerate(rows):
        if has & lacks:
            raise VerificationError(f"Object {k} both has and lacks an attribute")
        for premise, conclusion in merged_implications:
            if premise & ~has == 0 and conclusion & lacks:
                raise VerificationError(f"Object {k} violates an implication")
    closure = _Closure(attributes, merged_implications)

    def open_attributes(mask: int) -> int:
        lacked = 0
        for has, lacks in rows:
            if mask & ~has == 0:
                lacked |= lacks
        return full & ~mask & ~lacked

    seen, count, settled = set(), 0, 0
    closed = closure(0)
    while True:
        count += 1
        remaining = open_attributes(closed)
        if remaining:
            if open_sets.get(closed) != remaining:
                listed = open_sets.get(closed)
                raise VerificationError(
                    f"The closed set {closed:#x} has the open attributes {remaining:#x}, "
                    + ("but is not listed" if listed is None else f"but is listed with {listed:#x}"))
            seen.add(closed)
        else:
            if closed in open_sets:
                raise VerificationError(f"The listed set {closed:#x} is settled by the objects")
            settled += 1
        if closed == full:
            break
        for i in range(attributes - 1, -1, -1):
            bit = 1 << i
            if closed & bit:
                continue
            lower = closed & (bit - 1)
            candidate = closure(lower | bit)
            if candidate & (bit - 1) == lower:
                closed = candidate
                break
        else:
            break
    unseen = set(open_sets) - seen
    if unseen:
        raise VerificationError(f"{len(unseen)} listed sets are not closed under the implications, "
                                f"the first {min(unseen):#x}")
    return count, settled
