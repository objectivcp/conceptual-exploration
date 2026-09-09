from collections import defaultdict
from collections.abc import Callable, Iterable
from itertools import permutations, product

from core.atom import Atom, atoms_over
from core.implication import Implication
from core.signature import Predicate
from core.variable import Variable, SortedVariable
from experts.expert import Expert
from .attribute_exploration import AttributeExploration
from .exploration_base import ExplorationBase


def variable_symmetries(
        variables: tuple[Variable, ...],
        *,
        substitutions: bool = False,
) -> list[Callable[[Atom], Atom]]:
    """Atom-renaming maps induced by renamings of ``variables``.

    By default, only permutations of the variables are used (sound symmetries that
    map the atom set bijectively onto itself). With ``substitutions=True`` every
    variable map is used, including non-injective ones that specialize a rule by
    identifying variables. The identity is excluded.
    """
    renamings = (
        product(variables, repeat=len(variables))
        if substitutions
        else permutations(variables)
    )
    mappings: list[Callable[[Atom], Atom]] = []
    for images in renamings:
        if images != variables:
            mappings.append(_atom_renaming(dict(zip(variables, images))))
    return mappings


def sorted_variable_symmetries(
    variables: tuple[SortedVariable, ...],
    substitutions: bool,
) -> list[Callable[[Atom], Atom]]:

    variables_by_sort = defaultdict(list)
    for v in variables:
        variables_by_sort[v.sort].append(v)

    sort_renamings = [
        tuple(
            product(vars_of_sort, repeat=len(vars_of_sort))
            if substitutions
            else permutations(vars_of_sort)
        )
        for vars_of_sort in variables_by_sort.values()
    ]

    mappings = []

    for choices in product(*sort_renamings):
        mapping = {
            v: i
            for vars_of_sort, images in zip(variables_by_sort.values(), choices)
            for v, i in zip(vars_of_sort, images)
        }
        if any(mapping[v] != v for v in variables):
            mappings.append(_atom_renaming(mapping))

    return mappings


def _atom_renaming(
        variable_map: dict[Variable, Variable],
) -> Callable[[Atom], Atom]:
    return lambda atom: atom.rename(lambda variable: variable_map[variable])


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
