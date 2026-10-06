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

    `implication` is the one the expert accepted. `everything` says that the
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


def reduced_basis(base: ExplorationBase) -> list[Rule]:
    """The accepted implications of `base`, rewritten for reading.

    Each premise is cut to the attributes the rest of it does not entail.
    Each conclusion then starts as everything the premise entails and is cut
    to the attributes that do not follow from the premise by way of the
    background, the other rules, and the images of all of them under the
    mappings; a rule left with no conclusion is dropped. Rules are cut one at
    a time against the others as already cut, so that, read together with the
    background and the mappings, the result entails exactly what the accepted
    implications do. A rule's own images are not used in cutting it, since
    they would let it derive its own conclusion.

    Conclusion attributes are tried for removal weakest first, by how much
    each entails on its own, so that a rule keeps the attribute the others
    follow from (SameCell rather than SameRow and SameColumn). A premise that
    entails every attribute is cut the same way; it is printed as concluding
    everything unless what is left of its conclusion entails every attribute
    on its own, as a law satisfied only by one-element magmas does.
    """
    index = base.index
    theory = base.implications

    def images(premise: int, conclusion: int) -> set[tuple[int, int]]:
        return {
            (p, c)
            for p, c in [(premise, conclusion), *base.mapped_images(premise, conclusion)]
            if c & ~p
        }

    # A background implication already among the images is an image of one
    # mapped before, and with the mappings closed under composition so are
    # its own images; a background of whole orbits is mapped once per orbit.
    background: set[tuple[int, int]] = set()
    for implication, source in base.implication_sources.items():
        if source is ImplicationSource.BACKGROUND:
            masks = (index.encode(implication.premise), index.encode(implication.conclusion))
            if masks not in background:
                background |= images(*masks)

    accepted = base.accepted_implications
    rules = []
    for implication in accepted:
        premise = index.encode(theory.simplify(implication).premise)
        closure = theory.closure_mask(premise)
        rules.append([premise, closure & ~premise])
    rule_images = [images(premise, conclusion) for premise, conclusion in rules]

    for i, rule in enumerate(rules):
        premise, conclusion = rule
        rest = list(background.union(*(rule_images[:i] + rule_images[i + 1:])))
        target = conclusion
        weakest_first = sorted(
            bits(target),
            key=lambda position: (theory.closure_mask(1 << position).bit_count(), position),
        )
        for position in weakest_first:
            candidate = conclusion & ~(1 << position)
            implications = rest + list(images(premise, candidate))
            if target & ~close_mask(premise, implications) == 0:
                conclusion = candidate
        rule[1] = conclusion
        rule_images[i] = images(premise, conclusion)

    full = base.full_mask
    return [
        Rule(
            premise=frozenset(index.decode(premise)),
            conclusion=frozenset(index.decode(conclusion)),
            everything=(
                theory.closure_mask(premise) & full == full
                and theory.closure_mask(conclusion) & full != full
            ),
            source=base.implication_sources[implication],
            implication=implication,
        )
        for implication, (premise, conclusion) in zip(accepted, rules)
        if conclusion
    ]
