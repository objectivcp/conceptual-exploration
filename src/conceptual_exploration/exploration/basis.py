from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from ..core.bitset import bits
from ..core.implication import Implication
from ..core.theory import close_mask
from .base import ExplorationBase, ImplicationSource

A = TypeVar("A")


@dataclass(frozen=True)
class SimplifiedImplication(Generic[A]):
    """An accepted implication rewritten for reading.

    `implication` is the one the expert accepted, and `source` says whether
    it was confirmed; the simplified implication follows from the trusted
    implications if it was, and otherwise no attribute of its conclusion
    follows from its premise by them (see `simplified_implications`).
    `everything` says that the premise entails every attribute, and that no
    attribute does so on its own, so it is printed as concluding everything:
    no object has the premise unless it has every attribute. That may be a
    contradiction, though not necessarily (a one-element magma satisfies
    every equation).
    """

    premise: frozenset[A]
    conclusion: frozenset[A]
    everything: bool
    source: ImplicationSource
    implication: Implication[A]

    def format(self, name: Callable[[A], str] = str) -> str:
        premise = ", ".join(sorted(map(name, self.premise))) or "∅"
        conclusion = (
            "everything"
            if self.everything
            else ", ".join(sorted(map(name, self.conclusion)))
        )
        return f"{premise} -> {conclusion}"

    def __str__(self) -> str:
        return self.format()


def simplified_implications(base: ExplorationBase) -> list[SimplifiedImplication]:
    """The accepted implications of `base`, simplified for reading, without
    those that are then redundant.

    They are simplified with the trusted implications alone: the background,
    the confirmed implications and their images. Each premise is cut to the
    attributes the rest of it does not entail by them. The conclusion of a
    simplified confirmed implication then starts as everything its premise
    entails by them, and that of a simplified unconfirmed implication as what
    the implication adds to that. Each conclusion is cut to the attributes
    that do not follow from the premise by way of the background, the other
    simplified confirmed implications, and the images of all of these under
    the mappings; one left with no conclusion is redundant and is dropped.
    The simplified confirmed implications are cut first, one at a time
    against the others as already cut, so that with the background and the
    mappings they entail exactly the trusted implications. A simplified
    unconfirmed implication is cut against these alone, never against
    another unconfirmed one, so that each states what is not proved: no
    attribute of its conclusion follows from its premise by the trusted
    implications, and an open question is not merged into another. Read
    together with the background and the mappings (except for the
    unconfirmed implications of a base that does not map them), the
    simplified implications entail exactly what the accepted implications
    do. The images of a simplified implication are not used in cutting it,
    since they would let it derive its own conclusion.

    Conclusion attributes are tried for removal weakest first, by how much
    each entails on its own, so that the attribute the others follow from is
    kept (SameCell rather than SameRow and SameColumn). A premise that
    entails every attribute is cut the same way; it is printed as concluding
    everything unless what is left of its conclusion entails every attribute
    on its own, as a law satisfied only by one-element magmas does.
    """
    index = base.index
    trusted = base.trusted_implications
    sources = base.implication_sources

    def images(premise: int, conclusion: int, mapped: bool = True) -> set[tuple[int, int]]:
        return {
            (p, c)
            for p, c in [(premise, conclusion), *(base.mapped_images(premise, conclusion) if mapped else [])]
            if c & ~p
        }

    # A background implication already among the images is an image of one
    # mapped before, and with the mappings closed under composition so are
    # its own images; a background of whole orbits is mapped once per orbit.
    background: set[tuple[int, int]] = set()
    for implication, source in sources.items():
        if source is ImplicationSource.BACKGROUND:
            masks = (index.encode(implication.premise), index.encode(implication.conclusion))
            if masks not in background:
                background |= images(*masks)

    accepted = base.accepted_implications
    confirmed = [sources[implication] is ImplicationSource.CONFIRMED for implication in accepted]
    simplified = []
    for implication, is_confirmed in zip(accepted, confirmed):
        premise = index.encode(trusted.simplify(implication).premise)
        start = trusted.closure_mask(premise)
        if is_confirmed:
            simplified.append([premise, start & ~premise])
        else:
            given = premise | index.encode(implication.conclusion)
            simplified.append([premise, trusted.closure_mask(given) & ~start])
    # Unconfirmed implications that the base does not map stand for themselves.
    mapped = [base.map_unconfirmed or c for c in confirmed]
    simplified_images = [images(premise, conclusion, m) for (premise, conclusion), m in zip(simplified, mapped)]

    def cut(i: int) -> None:
        premise, conclusion = simplified[i]
        others = (simplified_images[j] for j in range(len(simplified)) if j != i and confirmed[j])
        rest = list(background.union(*others))
        target = conclusion
        weakest_first = sorted(
            bits(target),
            key=lambda position: (trusted.closure_mask(1 << position).bit_count(), position),
        )
        for position in weakest_first:
            candidate = conclusion & ~(1 << position)
            implications = rest + list(images(premise, candidate, mapped[i]))
            if target & ~close_mask(premise, implications) == 0:
                conclusion = candidate
        simplified[i][1] = conclusion
        simplified_images[i] = images(premise, conclusion, mapped[i])

    for i in range(len(simplified)):
        if confirmed[i]:
            cut(i)
    for i in range(len(simplified)):
        if not confirmed[i]:
            cut(i)

    full = base.full_mask
    return [
        SimplifiedImplication(
            premise=frozenset(index.decode(premise)),
            conclusion=frozenset(index.decode(conclusion)),
            everything=(
                trusted.closure_mask(premise | (0 if confirmed[i] else conclusion)) & full == full
                and trusted.closure_mask(conclusion) & full != full
            ),
            source=ImplicationSource.CONFIRMED if confirmed[i] else ImplicationSource.UNCONFIRMED,
            implication=implication,
        )
        for i, (implication, (premise, conclusion)) in enumerate(zip(accepted, simplified))
        if conclusion
    ]


# Former names, kept for code that still uses them.
Rule = SimplifiedImplication
simplified_rules = simplified_implications
reduced_basis = simplified_implications
