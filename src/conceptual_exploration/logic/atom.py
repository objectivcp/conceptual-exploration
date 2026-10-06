from collections.abc import Callable, Iterable
from dataclasses import dataclass
from itertools import product

from ..core.implication import Implication
from ..core.truth import Truth
from .predicate import Predicate, EvaluatablePredicate
from .variable import Variable


class EvaluationNotSupportedError(Exception):
    pass


@dataclass(frozen=True, slots=True)
class Atom:
    predicate: Predicate
    arguments: tuple[Variable, ...]

    def __post_init__(self):
        if len(self.arguments) != self.predicate.arity:
            raise ValueError(
                f"Predicate {self.predicate} has arity {self.predicate.arity}, "
                f"but {len(self.arguments)} arguments were given: {self.arguments}"
            )

    def rename(self, mapping: Callable[[Variable], Variable]) -> "Atom":
        return Atom(
            self.predicate,
            tuple(mapping(argument) for argument in self.arguments),
        )

    def normalize(self) -> "Atom | Truth":
        """This atom in canonical form, or its truth value where the
        predicate's properties fix it.

        Of the two orders of a symmetric atom's arguments, the canonical one
        has them sorted. An atom that is already canonical is returned itself.
        """
        p = self.predicate
        if p.arity == 2:
            first, second = self.arguments
            if first == second:
                if p.reflexive:
                    return Truth.TRUE
                if p.irreflexive:
                    return Truth.FALSE
            elif p.symmetric and second < first:
                return Atom(p, (second, first))
        return self

    def __str__(self) -> str:
        return self.predicate.format(self.arguments)

    def __lt__(self, other: "Atom") -> bool:
        if not isinstance(other, Atom):
            return NotImplemented
        return (self.predicate, self.arguments) < (other.predicate, other.arguments)

    def __call__(self, assignment: dict[Variable, object]) -> "GroundedAtom":
        return GroundedAtom(self, assignment)


class GroundedAtom:
    __slots__ = ("predicate", "arguments")

    def __init__(self, atom: Atom, assignment: dict[Variable, object]) -> None:
        self.predicate: Predicate = atom.predicate
        self.arguments: tuple[object, ...] = tuple(
            assignment[argument] for argument in atom.arguments
        )

    def holds(self) -> bool:
        if isinstance(self.predicate, EvaluatablePredicate):
            return self.predicate(*self.arguments)

        raise EvaluationNotSupportedError(
            f"Predicate {self.predicate!r} does not support evaluation"
        )


def atoms_over(
        predicates: Iterable[Predicate],
        variables: Iterable[Variable],
) -> list[Atom]:
    """List every atom obtained by applying each predicate to all
    argument tuples drawn (with repetition) from ``variables``.

    Only atoms in canonical form whose truth is not fixed are listed; see
    `Atom.normalize`. For predicates that declare no properties, that is all
    of them.
    """
    variables = tuple(variables)
    atoms: list[Atom] = []
    for predicate in predicates:
        for arguments in product(variables, repeat=predicate.arity):
            if predicate.valid_arguments(arguments):
                atom = Atom(predicate, arguments)
                if atom.normalize() is atom:
                    atoms.append(atom)
    return atoms


def normalize_implication(
        implication: Implication[Atom],
        atoms: Iterable[Atom],
) -> Implication[Atom] | None:
    """Rewrite an implication over canonical atoms, or return None if it says
    nothing once the fixed truth values are taken into account.

    A true atom drops out of either side. A false premise atom makes the
    implication vacuous; a false conclusion atom means the premise cannot
    hold, so the conclusion becomes all of `atoms`.
    """
    premise = set()
    for atom in implication.premise:
        normal = atom.normalize()
        if normal is Truth.FALSE:
            return None
        if normal is not Truth.TRUE:
            premise.add(normal)

    conclusion = set()
    for atom in implication.conclusion:
        normal = atom.normalize()
        if normal is Truth.FALSE:
            conclusion = set(atoms)
            break
        if normal is not Truth.TRUE:
            conclusion.add(normal)

    conclusion -= premise
    if not conclusion:
        return None
    return Implication(premise, conclusion)
