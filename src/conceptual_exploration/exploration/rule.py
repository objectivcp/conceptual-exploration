from collections.abc import Callable, Iterable

from ..logic.atom import Atom, atoms_over, normalize_implication
from ..core.implication import Implication
from ..logic.predicate import Predicate
from ..logic.symmetries import variable_symmetries, sorted_variable_symmetries
from ..logic.variable import Variable, SortedVariable
from ..experts.base import Expert
from .attribute import AttributeExploration, QuestionReport
from .base import ExplorationBase


class RuleExploration(AttributeExploration):
    """First-order rule exploration over a signature and a set of variables.

    Convenience wrapper: builds the atoms, the variable symmetries, and a
    :class:`RuleExplorationBase`, then drives the shared
    :class:`AttributeExploration` engine.

    The atoms are the canonical ones the predicates' declared properties
    leave (see `Atom.normalize`). The background is rewritten over them, and
    extended by `{P(a), Q(a)} -> ⊥` for each pair of complementary predicates;
    `background` holds the result.
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
            on_question: Callable[[QuestionReport], None] | None = None,
    ) -> None:
        predicates = tuple(predicates)
        variables = tuple(variables)
        atoms = atoms_over(predicates, variables)
        self.background = [
            normalized
            for implication in background
            if (normalized := normalize_implication(implication, atoms)) is not None
        ]
        self.background.extend(_complement_background(predicates, atoms))
        mappings = (
            sorted_variable_symmetries(variables, substitutions=substitutions)
            if isinstance(variables[0], SortedVariable)
            else variable_symmetries(variables, substitutions=substitutions)
        )
        base = ExplorationBase(
            atoms,
            background_implications=self.background,
            mappings=mappings,
        )
        super().__init__(base, expert, evaluate_all, on_question)


def _complement_background(
        predicates: tuple[Predicate, ...],
        atoms: list[Atom],
) -> list[Implication[Atom]]:
    """`{P(a), Q(a)} -> ⊥` for every atom P(a) whose predicate names Q as its
    complement, once per pair."""
    by_name = {p.name: p for p in predicates}
    atom_set = set(atoms)
    seen = set()
    background = []
    for atom in atoms:
        name = atom.predicate.complement
        if name is None or name not in by_name:
            continue
        other = Atom(by_name[name], atom.arguments).normalize()
        pair = frozenset((atom, other))
        if other in atom_set and pair not in seen:
            seen.add(pair)
            background.append(Implication(pair, atoms))
    return background
