from collections.abc import Callable, Iterable
from dataclasses import dataclass
from itertools import product

from logic.predicate import Predicate, EvaluatablePredicate
from logic.variable import Variable


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

    def __str__(self) -> str:
        return self.predicate.format(self.arguments)

    def __lt__(self, other: "Atom") -> bool:
        if not isinstance(other, Atom):
            return NotImplemented
        return (
            self.predicate,
            self.arguments,
        ) < (
            other.predicate,
            other.arguments,
        )

    def __call__(self, assignment) -> "GroundedAtom":
        return GroundedAtom(self, assignment)


class GroundedAtom:
    def __init__(self, atom: Atom, assignment: dict[Variable, object]):
        self.predicate = atom.predicate
        self.arguments = tuple(
            assignment[argument]
            for argument in atom.arguments
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
    argument tuples drawn (with repetition) from ``variables``."""
    variables = tuple(variables)
    atoms: list[Atom] = []
    for predicate in predicates:
        for arguments in product(variables, repeat=predicate.arity):
            if predicate.valid_arguments(arguments):
                atoms.append(Atom(predicate, arguments))
    return atoms
