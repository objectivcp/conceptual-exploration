from collections.abc import Iterable

from logic.atom import Atom, atoms_over
from core.implication import Implication
from logic.predicate import Predicate
from logic.symmetries import variable_symmetries, sorted_variable_symmetries
from logic.variable import Variable, SortedVariable
from experts.base import Expert
from .attribute import AttributeExploration
from .base import ExplorationBase


class RuleExploration(AttributeExploration):
    """First-order rule exploration over a signature and a set of variables.

    Convenience wrapper: builds the atoms, the variable symmetries, and a
    :class:`RuleExplorationBase`, then drives the shared
    :class:`AttributeExploration` engine.
    """

    def __init__(
            self,
            predicates: Iterable[Predicate],
            variables: Iterable[Variable],
            expert: Expert,
            *,
            background: Iterable[Implication[Atom]] = (),
            substitutions: bool = False,
            evaluate_all: bool = False, # ask expert to evaluate all atoms
    ) -> None:
        atoms = atoms_over(predicates, variables)
        variables = tuple(variables)
        mappings = (
            sorted_variable_symmetries(variables, substitutions=substitutions)
            if isinstance(variables[0], SortedVariable)
            else variable_symmetries(variables, substitutions=substitutions)
        )
        base = ExplorationBase(
            atoms,
            background_implications=background,
            mappings=mappings,
        )
        super().__init__(base, expert, evaluate_all)
