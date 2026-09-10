from collections.abc import Iterable
from itertools import product

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.logic.predicate import EvaluatablePredicate, Notation
from conceptual_exploration.logic.variable import Variable
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.core.theory import ImplicationTheory


class NumberExpert(Expert[int, EvaluatablePredicate]):

    def __init__(self,
                 domain: Iterable[int],
                 predicates: list[EvaluatablePredicate],
                 variables: list[Variable]):
        self.domain = tuple(domain)
        self.predicates = predicates
        self.variables = variables

    def validate(self, impl, attributes=None):
        # print(f'Validating {impl}')
        for values in product(
                self.domain,
                repeat=len(self.variables)
        ):
            assignment = dict(zip(self.variables, values))
            positive = set()
            for a in impl.premise:
                if a(assignment).holds():
                    positive.add(a)
                else:
                    break
            else:
                for a in impl.conclusion:
                    if a(assignment).holds():
                        positive.add(a)
                    else:
                        counterexample = PartialObject(
                            tuple(assignment.items()),
                            positive,
                            {a}
                        )
                        # print(f'Counterexample found: {counterexample}')
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
        notation=Notation.INFIX
    ),
    EvaluatablePredicate(
        ">",
        2,
        function=lambda n, m: n > m,
        notation=Notation.INFIX
    ),
    EvaluatablePredicate(
        "=",
        2,
        function=lambda n, m: n == m,
        notation=Notation.INFIX
    )
]


variables = [Variable("x"), Variable("y"), Variable("z")]
# variables = [Variable("x"), Variable("y")]
expert = NumberExpert(range(-10, 11), predicates, variables)
exploration = RuleExploration(predicates,
                              variables,
                              expert,
                              substitutions=True)
exploration.run()

base = exploration.base
print()
print(f'Accepted {len(base.accepted_implications)} implications:\n')
theory = ImplicationTheory(base.implications)
for implication in base.accepted_implications:
    simplified = theory.simplify(implication)
    for i in simplified.premise:
        print(i)
    print('-' * 20)
    if len(implication.premise | implication.conclusion) == len(base.attributes):
        print('M\n')
        continue
    for i in simplified.conclusion:
        print(i)
    print()
print()

# print(base.context)