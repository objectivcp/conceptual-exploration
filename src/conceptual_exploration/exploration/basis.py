from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from ..core.bitset import bits
from ..core.implication import Implication
from ..core.theory import close_mask
from .base import ExplorationBase, ImplicationSource

A = TypeVar("A")


@dataclass(frozen=True)
class Rule(Generic[A]):
    """An accepted implication rewritten for reading.

    `implication` is the one the expert accepted, and `source` says whether
    it was confirmed; the rule follows from the trusted implications if it
    was, and otherwise no attribute of its conclusion follows from its
    premise by them (see `simplified_rules`). `everything` says that the
    premise entails every attribute, and that no attribute does so on its
    own, so the rule is printed as concluding everything: no object has the
    premise unless it has every attribute. That may be a contradiction,
    though not necessarily (a one-element magma satisfies every equation).
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


def simplified_rules(base: ExplorationBase) -> list[Rule]:
    """The accepted implications of `base`, simplified into rules for reading,
    without those that are then redundant.

    Rules are simplified with the trusted implications alone: the
    background, the confirmed implications and their images. Each premise is
    cut to the attributes the rest of it does not entail by them. The
    conclusion of a confirmed implication's rule then starts as everything
    its premise entails by them, and that of an unconfirmed implication's
    rule as what the implication adds to that. Each conclusion is cut to the
    attributes that do not follow from the premise by way of the background,
    the rules of the other confirmed implications, and the images of all of
    these under the mappings; a rule left with no conclusion is redundant and
    is dropped. The confirmed implications' rules are cut first, one at a
    time against the others as already cut, so that with the background and
    the mappings they entail exactly the trusted implications. An
    unconfirmed implication's rule is cut against these alone, never against
    another unconfirmed one, so that each states what is not proved: no
    attribute of its conclusion follows from its premise by the trusted
    implications, and an open question is not merged into another. Read
    together with the background and the mappings (except for the
    unconfirmed implications of a base that does not map them), the rules
    entail exactly what the accepted implications do. A rule's own images
    are not used in cutting it, since they would let it derive its own
    conclusion.

    Conclusion attributes are tried for removal weakest first, by how much
    each entails on its own, so that a rule keeps the attribute the others
    follow from (SameCell rather than SameRow and SameColumn). A premise that
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
    rules = []
    for implication, is_confirmed in zip(accepted, confirmed):
        premise = index.encode(trusted.simplify(implication).premise)
        start = trusted.closure_mask(premise)
        if is_confirmed:
            rules.append([premise, start & ~premise])
        else:
            given = premise | index.encode(implication.conclusion)
            rules.append([premise, trusted.closure_mask(given) & ~start])
    # Unconfirmed implications that the base does not map stand for themselves.
    mapped = [base.map_unconfirmed or c for c in confirmed]
    rule_images = [images(premise, conclusion, m) for (premise, conclusion), m in zip(rules, mapped)]

    def cut(i: int) -> None:
        premise, conclusion = rules[i]
        rest = list(background.union(*(rule_images[j] for j in range(len(rules)) if j != i and confirmed[j])))
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
        rules[i][1] = conclusion
        rule_images[i] = images(premise, conclusion, mapped[i])

    for i in range(len(rules)):
        if confirmed[i]:
            cut(i)
    for i in range(len(rules)):
        if not confirmed[i]:
            cut(i)

    full = base.full_mask
    return [
        Rule(
            premise=frozenset(index.decode(premise)),
            conclusion=frozenset(index.decode(conclusion)),
            everything=(
                trusted.closure_mask(premise | (0 if confirmed[i] else conclusion)) & full == full
                and trusted.closure_mask(conclusion) & full != full
            ),
            source=ImplicationSource.CONFIRMED if confirmed[i] else ImplicationSource.UNCONFIRMED,
            implication=implication,
        )
        for i, (implication, (premise, conclusion)) in enumerate(zip(accepted, rules))
        if conclusion
    ]


# The former name.
reduced_basis = simplified_rules
