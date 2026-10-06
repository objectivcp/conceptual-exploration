from collections.abc import Iterable
from itertools import product

from conceptual_exploration import reduced_basis, report_every
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.logic.predicate import EvaluatablePredicate, Notation
from conceptual_exploration.logic.variable import Variable
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.rule import RuleExploration


class NumberExpert(Expert[int, EvaluatablePredicate]):

    def __init__(self,
                 domain: Iterable[int],
                 predicates: list[EvaluatablePredicate],
                 variables: list[Variable]):
        self.domain = tuple(domain)
        self.predicates = predicates
        self.variables = variables

    def validate(self, implication, attributes=None):
        for values in product(
                self.domain,
                repeat=len(self.variables)
        ):
            assignment = dict(zip(self.variables, values))
            positive = set()
            for a in implication.premise:
                if a(assignment).holds():
                    positive.add(a)
                else:
                    break
            else:
                for a in implication.conclusion:
                    if a(assignment).holds():
                        positive.add(a)
                    else:
                        counterexample = PartialObject(
                            tuple(assignment.items()),
                            positive,
                            {a}
                        )
                        return counterexample
        return None


predicates = [
    EvaluatablePredicate(
        "> 0",
        1,
        function=lambda n: n > 0,
        notation=Notation.POSTFIX
    ),
    EvaluatablePredicate(
        "< 0",
        1,
        function=lambda n: n < 0,
        notation=Notation.POSTFIX
    ),
    EvaluatablePredicate(
        "<",
        2,
        function=lambda n, m: n < m,
        notation=Notation.INFIX,
        irreflexive=True
    ),
    EvaluatablePredicate(
        ">",
        2,
        function=lambda n, m: n > m,
        notation=Notation.INFIX,
        irreflexive=True
    ),
    EvaluatablePredicate(
        "=",
        2,
        function=lambda n, m: n == m,
        notation=Notation.INFIX,
        symmetric=True,
        reflexive=True
    )
]


variables = [Variable("x"), Variable("y"), Variable("z")]
# variables = [Variable("x"), Variable("y")]
expert = NumberExpert(range(-10, 11), predicates, variables)
exploration = RuleExploration(predicates,
                              variables,
                              expert,
                              substitutions=True,
                              on_question=report_every())
exploration.run()

base = exploration.base
rules = reduced_basis(base)
print()
print(f'Accepted {len(base.accepted_implications)} implications, reduced to {len(rules)} rules:\n')
for rule in rules:
    print(rule)
print()

# print(base.context)