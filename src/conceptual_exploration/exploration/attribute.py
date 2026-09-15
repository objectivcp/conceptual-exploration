from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from ..experts.base import Expert
from .base import ExplorationBase, ImplicationSource
from .state import ExplorationState
from ..algorithms.next_closure import NextClosure
from ..core.context import PartialObject
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True, slots=True)
class QuestionReport(Generic[O, A]):
    """One question put to the expert, together with the answer it gave.

    `source` is None exactly when the implication was refuted, in which case
    `counterexample` holds the refuting object. The counts describe the theory
    as it stood when the question was answered, before the answer was applied.
    """

    number: int
    implication: Implication[A]
    counterexample: PartialObject[O, A] | None
    source: ImplicationSource | None
    implication_count: int
    object_count: int


def report_every(n: int = 1) -> Callable[[QuestionReport[O, A]], None]:
    """Return a callback that prints every nth question and its outcome.

    `report_every(1)` prints every question; anything below 1 prints nothing.
    """

    def report(question: QuestionReport[O, A]) -> None:
        if n < 1 or question.number % n:
            return
        print()
        print(f'Number of implications: {question.implication_count}')
        print(f'Number of objects: {question.object_count}')
        print(f'Question {question.number}: {question.implication}')
        if question.counterexample is not None:
            print(f'Counterexample found: {question.counterexample}\n')
        else:
            print(f'{question.source.value.capitalize()}\n')

    return report


class AttributeExploration:

    def __init__(
            self,
            exploration_base: ExplorationBase[O, A],
            expert: Expert[O, A],
            evaluate_all: bool = False, # ask expert to evaluate all attributes
            on_question: Callable[[QuestionReport[O, A]], None] | None = None,
    ):
        self.base = exploration_base
        self.expert = expert
        self.state = ExplorationState()
        self.evaluate_all = evaluate_all
        self.on_question = on_question

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
                    if counterexample:
                        if not counterexample.refutes(implication):
                            raise ValueError(
                                f'Counterexample {counterexample} does not refute {implication}'
                            )
                        self._report(implication, counterexample, None)
                        self.base.add_counterexample(counterexample)
                        self.state.counterexamples.append(counterexample)
                        closure = self.base.context.closure(premise)
                    else:
                        source = (
                            ImplicationSource.CONFIRMED
                            if self.expert.is_conclusive()
                            else ImplicationSource.UNCONFIRMED
                        )
                        self._report(implication, None, source)
                        self.base.accept(implication, source)
                        self.state.accepted_implications.append(implication)
                        premise = premises.send(True)
                        break
                else:
                    premise = next(premises)

        except StopIteration:
            pass

        return self.state

    def _report(
            self,
            implication: Implication[A],
            counterexample: PartialObject[O, A] | None,
            source: ImplicationSource | None,
    ) -> None:
        if self.on_question is None:
            return
        self.on_question(
            QuestionReport(
                number=self.state.questions_asked,
                implication=implication,
                counterexample=counterexample,
                source=source,
                implication_count=len(self.base.implications.implications),
                object_count=len(self.base.context.objects),
            )
        )
