from dataclasses import dataclass
from itertools import combinations, product
from typing import Generic, TypeVar

from conceptual_exploration import reduced_basis, report_every
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.attribute import AttributeExploration
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.core.theory import ImplicationTheory

A = TypeVar("A")


class ImplicationExpert(Expert[set[str], Implication[str]]):
    def __init__(self, atoms: tuple[str, ...], attribute_implications: list[Implication[str]]):
        self.atoms = atoms
        self.attributes = frozenset(attribute_implications)

    def validate(self, implication, attributes=None):
        premise_theory = ImplicationTheory(implication.premise)
        for i in implication.conclusion:
            true_atoms = frozenset(premise_theory.closure(i.premise))
            if not i.conclusion <= true_atoms:
                positive = frozenset(
                    a
                    for a in self.attributes
                    if a.respected_by(true_atoms)
                )
                return PartialObject(
                    true_atoms,
                    positive,
                    self.attributes - positive
                )
        return None


@dataclass(frozen=True, slots=True)
class Substitution(Generic[A]):
    mapping: frozenset[tuple[A, A]]

    def __call__(self, variable: A) -> A:
        return dict(self.mapping)[variable]

    def __str__(self) -> str:
        return f"Substitution({sorted(self.mapping)})"

    def apply_to_implication(self, impl: Implication[A]) -> Implication[A]:
        return Implication(
            {self(a) for a in impl.premise},
            {self(a) for a in impl.conclusion},
        )


def all_substitutions(atoms):
    subs = []
    for images in product(atoms, repeat=len(atoms)):
        if images != atoms:
            mapping = frozenset(zip(atoms, images))
            subs.append(Substitution(mapping))
    return subs


def all_single_conclusion_implications(atoms):
    implications = []
    for size in range(len(atoms)):
        for premise in combinations(atoms, size):
            premise_set = set(premise)
            for a in atoms:
                if a not in premise_set:
                    implications.append(
                        Implication(premise_set, {a})
                    )
    return implications


n = 3
variables = tuple(f'x{i}' for i in range(1, n + 1))
attributes = all_single_conclusion_implications(variables)
substitutions = all_substitutions(variables)

mappings = []
for s in substitutions:
    for implication in attributes:
        if s.apply_to_implication(implication) not in attributes:
            break
    else:
        print(s)
        mappings.append(s.apply_to_implication)
print(len(mappings))

base = ExplorationBase[frozenset[str], Implication[str]](
    attributes=attributes,
    mappings=mappings
)
exploration = AttributeExploration(
    base,
    ImplicationExpert(variables, attributes),
    on_question=report_every()
)

exploration.run()

# The attributes are implications themselves, so each rule is printed as a
# block: its premise above the line and its conclusion below.
rules = reduced_basis(base)
print()
print(f'Accepted {len(base.accepted_implications)} implications, reduced to {len(rules)} rules:\n')
for rule in rules:
    for i in sorted(rule.premise):
        print(i)
    print('-' * 20)
    if rule.everything:
        print('everything')
    else:
        for i in sorted(rule.conclusion):
            print(i)
    print()
print()

# print(base.context)