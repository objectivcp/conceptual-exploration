"""Classical entailment between implications, for reading results.

The exploration reasons with Horn closure. Read as propositional clauses,
implications entail more, since a declared complement holds exactly where
its predicate does not: of two complementary atoms on the same arguments,
every object has exactly one. An implication may then follow from others by
contraposition or by cases, as on partial Sudoku grids
`Forced(y, n), Possible(x, n), SameRow(x, y) -> SameCell(x, y)` follows from
`Forced(y, n), DifferentCells(x, y), SameRow(x, y) -> Excluded(x, n)`.

`classically_irredundant` drops the simplified implications that follow
from the others in this sense, and `ClassicalTheory` answers whether an
implication follows from a set of others at all. Both need python-sat.
"""

from collections.abc import Callable, Hashable, Iterable, Sequence
from typing import Any

from ..logic.atom import Atom
from ..logic.predicate import Predicate
from .base import ExplorationBase, ImplicationSource
from .basis import SimplifiedImplication


class ClassicalTheory:
    """Implications read as propositional clauses, with complements total.

    Attributes become SAT variables as they are met. When an `Atom` and the
    atom of its predicate's declared complement on the same arguments have
    both been met, the clauses that exactly one of them holds are added.
    Clauses may be added under a guard (see `guard`), so that one theory
    serves questions that each use a different part of it.
    """

    def __init__(self, solver_name: str = "g3") -> None:
        try:
            from pysat.solvers import Solver
        except ImportError as error:
            raise ImportError(
                "ClassicalTheory needs python-sat: pip install python-sat"
            ) from error
        self._solver = Solver(name=solver_name)
        self._variables: dict[Hashable, int] = {}
        self._predicates: dict[str, Predicate] = {}
        self._top = 0

    def guard(self) -> int:
        """A fresh literal; clauses added under it count only in the
        `entails` calls that list it among their guards."""
        self._top += 1
        return self._top

    def add(
        self,
        premise: Iterable[Hashable],
        conclusion: Iterable[Hashable],
        guard: int | None = None,
    ) -> None:
        """Add premise -> conclusion, as one clause per conclusion attribute
        not in the premise."""
        premise = set(premise)
        clause = [-self._variable(a) for a in premise] + ([-guard] if guard else [])
        for a in conclusion:
            if a not in premise:
                self._solver.add_clause(clause + [self._variable(a)])

    def entails(
        self,
        premise: Iterable[Hashable],
        conclusion: Iterable[Hashable],
        guards: Iterable[int] = (),
    ) -> bool:
        """Whether premise -> conclusion follows classically from the
        clauses added without a guard or under one of `guards`."""
        premise = set(premise)
        assumptions = [self._variable(a) for a in premise] + list(guards)
        return all(
            not self._solver.solve(assumptions=assumptions + [-self._variable(a)])
            for a in conclusion
            if a not in premise
        )

    def close(self) -> None:
        self._solver.delete()

    def _variable(self, attribute: Hashable) -> int:
        if attribute not in self._variables:
            self._top += 1
            self._variables[attribute] = self._top
            if isinstance(attribute, Atom):
                self._pair(attribute)
        return self._variables[attribute]

    def _pair(self, atom: Atom) -> None:
        """Add the clauses for `atom` and its complement, if both are met."""
        predicate = atom.predicate
        self._predicates.setdefault(predicate.name, predicate)
        names = {predicate.complement} | {
            other.name for other in self._predicates.values()
            if other.complement == predicate.name
        }
        for name in names:
            other = self._predicates.get(name) if name else None
            if other is None:
                continue
            complement = Atom(other, atom.arguments).normalize()
            if isinstance(complement, Atom) and complement in self._variables:
                a, b = self._variables[atom], self._variables[complement]
                self._solver.add_clause([a, b])
                self._solver.add_clause([-a, -b])


class _Everything:
    """Stands for the conjunction of all attributes of a base, so that an
    implication concluding everything is one clause rather than one per
    attribute."""

    def __repr__(self) -> str:
        return "everything"


def _base_theory(base: ExplorationBase) -> tuple[ClassicalTheory, Callable[..., None]]:
    """A theory of the background and its images, and a function adding an
    implication given by masks, with its images, under a guard."""
    theory = ClassicalTheory()
    index = base.index
    everything = _Everything()
    theory.add([everything], index.decode(base.full_mask))

    def add_masks(premise: int, conclusion: int, guard: int | None = None, mapped: bool = True) -> None:
        images = [(premise, conclusion), *(base.mapped_images(premise, conclusion) if mapped else [])]
        for p, c in images:
            if (p | c) & base.full_mask == base.full_mask:
                theory.add(index.decode(p), [everything], guard)
            else:
                theory.add(index.decode(p), index.decode(c), guard)

    # The background is mapped once per orbit, as in `simplified_implications`.
    seen: set[tuple[int, int]] = set()
    for implication, source in base.implication_sources.items():
        if source is ImplicationSource.BACKGROUND:
            masks = (index.encode(implication.premise), index.encode(implication.conclusion))
            if masks not in seen:
                images = {masks, *base.mapped_images(*masks)}
                seen |= images
                for p, c in images:
                    add_masks(p, c, mapped=False)
    return theory, add_masks


def classically_irredundant(
    base: ExplorationBase,
    implications: Sequence[SimplifiedImplication],
    drop_first: Callable[[SimplifiedImplication], Any] | None = None,
) -> list[SimplifiedImplication]:
    """The simplified implications of `base` without those that follow
    classically from the others kept, the background, and the images of all
    of these under the mappings, with declared complements total.

    Implications are tried for removal one at a time, in the order of
    `drop_first` (smallest first) or else last first, and each is tested
    against those still kept. Only confirmed implications are dropped or
    used, as `simplified_implications` treats unconfirmed ones. What is
    kept entails classically everything `implications` do, though perhaps
    no longer by Horn closure: a contrapositive form may be dropped in favour
    of the implication it restates.
    """
    theory, add_masks = _base_theory(base)
    index = base.index
    all_attributes = index.decode(base.full_mask)
    guards: list[int | None] = []
    for implication in implications:
        if implication.source is ImplicationSource.CONFIRMED:
            guard = theory.guard()
            conclusion = base.full_mask if implication.everything else index.encode(implication.conclusion)
            add_masks(index.encode(implication.premise), conclusion, guard)
            guards.append(guard)
        else:
            guards.append(None)

    order = sorted(
        range(len(implications)),
        key=(lambda i: drop_first(implications[i])) if drop_first else (lambda i: -i),
    )
    kept = set(range(len(implications)))
    try:
        for i in order:
            if guards[i] is None:
                continue
            implication = implications[i]
            others = [guards[j] for j in kept if j != i and guards[j] is not None]
            conclusion = all_attributes if implication.everything else implication.conclusion
            if theory.entails(implication.premise, conclusion, others):
                kept.remove(i)
    finally:
        theory.close()
    return [implication for i, implication in enumerate(implications) if i in kept]


def trusted_theory(base: ExplorationBase) -> ClassicalTheory:
    """The trusted implications of `base` (background, confirmed and their
    images) read classically, for asking what follows from them."""
    theory = ClassicalTheory()
    for implication in base.trusted_implications:
        theory.add(implication.premise, implication.conclusion)
    return theory
