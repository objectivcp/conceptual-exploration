from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from ..experts.base import Expert, Undecided
from .base import ExplorationBase, ImplicationSource
from .state import ExplorationState
from ..algorithms.next_closure import NextClosure
from ..core.context import PartialObject
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True)
class Witness(Generic[A]):
    """An object known to exist because the expert showed `implication`
    false, its conclusion a single attribute, without giving a
    counterexample: it has the attributes of the premise and lacks the one of
    the conclusion, and nothing else is known about it."""

    implication: Implication[A]

    @property
    def name(self) -> str:
        return f"Witness against {self.implication}"


@dataclass(frozen=True, slots=True)
class QuestionReport(Generic[O, A]):
    """One question put to the expert, together with the answer it gave.

    `source` is None when the implication was refuted, in which case
    `counterexample` holds the refuting object, and when the expert left it
    undecided, in which case `undecided` holds its answer. The counts describe
    the theory as it stood when the question was answered, before the answer
    was applied.
    """

    number: int
    implication: Implication[A]
    counterexample: PartialObject[O, A] | None
    source: ImplicationSource | None
    implication_count: int
    object_count: int
    undecided: Undecided[O, A] | None = None


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
        elif question.undecided is not None:
            outcome = "Unconfirmed" if question.undecided.unconfirmed else "Rejected"
            proved = ", ".join(map(str, question.undecided.proved))
            print(f'{outcome}{f"; proved {proved}" if proved else ""}\n')
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

    def run(self, start=None):
        """Explore from the first closed set, or from the first closed set
        lectically at or after `start`, which resumes an exploration.

        The exploration stops early if an object refutes an implication
        accepted as unconfirmed: that implication has steered the enumeration,
        which has to be resumed from the question it was accepted at without
        it. `state.stopped_by` then holds it.
        """
        # Premises and closures are bitmasks over the base's index; only the
        # implication put to the expert is turned back into sets.
        index = self.base.index
        generator = NextClosure(
            self.base.attributes,
            mask_closure_operator=self.base.implications.closure_mask,
        )
        premises = self._premises = generator.generate_masks(
            None if start is None else index.encode(start)
        )

        try:
            premise = next(premises)
            while True:
                closure = self.base.context_closure_mask(premise)

                while closure != premise:
                    implication = Implication(
                        premise=index.decode(premise),
                        conclusion=index.decode(closure & ~premise),
                    )
                    counterexample = self.expert.validate(
                        implication,
                        self.base.attributes if self.evaluate_all else None
                    )
                    self.state.questions_asked += 1
                    if isinstance(counterexample, Undecided):
                        premise = self._leave_open(implication, counterexample)
                        if self._stopped():
                            return self.state
                        break
                    if counterexample:
                        if not counterexample.refutes(implication):
                            raise ValueError(
                                f'Counterexample {counterexample} does not refute {implication}'
                            )
                        self._report(implication, counterexample, None)
                        self.base.add_counterexample(counterexample)
                        self.state.counterexamples.append(counterexample)
                        if self._stopped():
                            return self.state
                        closure = self.base.context_closure_mask(premise)
                    else:
                        source = (
                            ImplicationSource.CONFIRMED
                            if self.expert.is_conclusive()
                            else ImplicationSource.UNCONFIRMED
                        )
                        self._report(implication, None, source)
                        if source is ImplicationSource.UNCONFIRMED and self._conflicts(implication):
                            premise = next(premises)
                            break
                        self.base.accept(implication, source)
                        self.state.accepted_implications.append(implication)
                        if self._stopped():
                            return self.state
                        premise = premises.send(True)
                        break
                else:
                    premise = next(premises)

        except StopIteration:
            pass

        return self.state

    def _conflicts(self, implication: Implication[A], proved: frozenset[A] = frozenset()) -> bool:
        """Whether accepting the unconfirmed `implication`, after the
        confirmed one with the conclusion `proved`, would make the theory
        entail a rejected implication; such an implication is recorded in
        `conflicts` instead."""
        premise = frozenset(implication.premise) | proved
        rejected = self.base.contradicted(Implication(premise, implication.conclusion))
        if rejected is None:
            return False
        self.base.conflicts.append((implication, rejected))
        return True

    def _stopped(self) -> bool:
        if not self.base.refuted:
            return False
        self.state.stopped_by = self.base.origin(next(iter(self.base.refuted)))
        return True

    def _leave_open(self, implication: Implication[A], answer: Undecided[O, A]) -> int:
        """Take an answer the expert could not decide: accept the part of the
        conclusion it did confirm, reject the rest or accept it as
        unconfirmed, and return the next premise.

        If nothing is accepted, the premise stays closed under the
        implications, and the enumeration goes on to the next closed set as
        if the context had no question about this one.
        """
        self._report(implication, None, None, answer)
        if answer.object is not None:
            if answer.object.refutes(implication):
                raise ValueError(
                    f'Undecided answer to {implication} carries a refuting object'
                )
            self.base.add_counterexample(answer.object)
        proved = answer.proved & implication.conclusion
        rest = Implication(implication.premise, implication.conclusion - proved)
        if not answer.unconfirmed and len(rest.conclusion) == 1:
            # Some object has the premise and what it implies, and lacks the
            # one attribute: a counterexample, if a partial one.
            witness = PartialObject(Witness(rest), set(implication.premise) | proved, set(rest.conclusion))
            self.base.add_counterexample(witness)
            self.state.counterexamples.append(witness)
        elif not answer.unconfirmed:
            self.base.reject(rest)
        accepted = []
        if proved:
            accepted.append((Implication(implication.premise, proved), ImplicationSource.CONFIRMED))
        if answer.unconfirmed and rest.conclusion and not self._conflicts(rest, proved):
            # After the confirmed part, which a resumed round then keeps.
            accepted.append((rest, ImplicationSource.UNCONFIRMED))
        if not accepted:
            return next(self._premises)
        for accepted_implication, source in accepted:
            self.base.accept(accepted_implication, source)
            self.state.accepted_implications.append(accepted_implication)
        return self._premises.send(True)

    def _report(
            self,
            implication: Implication[A],
            counterexample: PartialObject[O, A] | None,
            source: ImplicationSource | None,
            undecided: Undecided[O, A] | None = None,
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
                undecided=undecided,
            )
        )
