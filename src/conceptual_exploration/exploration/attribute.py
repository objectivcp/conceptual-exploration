from typing import TypeVar

from ..experts.base import Expert
from .base import ExplorationBase
from .state import ExplorationState
from ..algorithms.next_closure import NextClosure
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")

class AttributeExploration:

    def __init__(
            self,
            exploration_base: ExplorationBase[O, A],
            expert: Expert[O, A],
            evaluate_all: bool = False, # ask expert to evaluate all attributes
    ):
        self.base = exploration_base
        self.expert = expert
        self.state = ExplorationState()
        self.evaluate_all = evaluate_all

    def run(self):
        generator = NextClosure(self.base.attributes, self.base.implications.closure)
        premises = generator.generate()

        try:
            premise = next(premises)
            while True:
                closure = self.base.context.closure(premise)

                while closure != premise:
                    implication = Implication(premise=premise, conclusion=closure-premise)
                    counterexample = self.expert.validate(
                        implication,
                        self.base.attributes if self.evaluate_all else None
                    )
                    self.state.questions_asked += 1
                    if self.state.questions_asked % 20 == 0:
                        print()
                        print(f'Number of implications: {len(self.base.implications.implications)}')
                        print(f'Number of objects: {len(self.base.context.objects)}')
                        print(f'Question {self.state.questions_asked}: {implication}')
                    if counterexample:
                        if not counterexample.refutes(implication):
                            raise ValueError(
                                f'Counterexample {counterexample} does not refute {implication}'
                            )
                        if self.state.questions_asked % 20 == 0:
                            print(f'Counterexample found: {counterexample}\n')
                        self.base.add_counterexample(counterexample)
                        self.state.counterexamples.append(counterexample)
                        closure = self.base.context.closure(premise)
                    else:
                        if self.state.questions_asked % 20 == 0:
                            print(f'Confirmed\n')
                        self.base.accept(implication)
                        self.state.accepted_implications.append(implication)
                        premise = premises.send(True)
                        break
                else:
                    premise = next(premises)

        except StopIteration:
            pass

        return self.state
