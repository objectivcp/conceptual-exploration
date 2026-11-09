from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, Literal, TypeVar

from ..experts.base import Expert, Undecided
from .base import ExplorationBase, ImplicationSource
from .state import ExplorationState
from ..algorithms.next_closure import NextClosure
from ..core.bitset import bits
from ..core.context import PartialObject
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True)
class Witness(Generic[A]):
    """An object known to exist because `implication`, its conclusion a
    single attribute, is false, though no counterexample is known: it has
    the attributes of the premise and lacks the one of the conclusion, and
    nothing else is known about it. The expert showed the implication false,
    or, if `derived`, the trusted knowledge does."""

    implication: Implication[A]
    derived: bool = False

    @property
    def name(self) -> str:
        return f"{'Derived' if self.derived else 'Witness'} against {self.implication}"


@dataclass(frozen=True)
class Tentative(Generic[A]):
    """An object taken to exist because `implication`, its conclusion a
    single attribute, is undecided and tentatively rejected: it has the
    attributes of the premise and lacks the one of the conclusion. It only
    steers the questions (see `ExplorationBase.add_tentative`)."""

    implication: Implication[A]

    @property
    def name(self) -> str:
        return f"Tentative against {self.implication}"


@dataclass(frozen=True, slots=True)
class QuestionReport(Generic[O, A]):
    """One question put to the expert, together with the answer it gave.

    `source` is None when the implication was refuted, in which case
    `counterexample` holds the refuting object, and when the expert left it
    undecided, in which case `undecided` holds its answer. The counts describe
    the theory as it stood when the question was answered, before the answer
    was applied. `added` holds the objects the expert gave besides its answer
    (`Expert.new_objects`), which are added after it.
    """

    number: int
    implication: Implication[A]
    counterexample: PartialObject[O, A] | None
    source: ImplicationSource | None
    implication_count: int
    object_count: int
    undecided: Undecided[O, A] | None = None
    added: tuple[PartialObject[O, A], ...] = ()


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
            print(f'Counterexample found: {question.counterexample}')
        elif question.undecided is not None:
            outcome = "Rejected" if question.undecided.rejected else "Unconfirmed"
            proved = ", ".join(map(str, question.undecided.proved))
            print(f'{outcome}{f"; proved {proved}" if proved else ""}')
        else:
            print(f'{question.source.value.capitalize()}')
        if question.added:
            print(f'Also added: {", ".join(str(o.object) for o in question.added)}')
        print()

    return report


class AttributeExploration:

    def __init__(
            self,
            exploration_base: ExplorationBase[O, A],
            expert: Expert[O, A],
            evaluate_all: bool = False, # ask expert to evaluate all attributes
            on_question: Callable[[QuestionReport[O, A]], None] | None = None,
            undecided: Literal["accept", "reject"] = "accept",
    ):
        """`undecided` says what becomes of what the expert leaves undecided
        and does not reject: it is accepted as unconfirmed, or each of its
        attributes is rejected tentatively, by a tentative object."""
        if undecided not in ("accept", "reject"):
            raise ValueError(f'undecided must be "accept" or "reject", not {undecided!r}')
        self.base = exploration_base
        self.expert = expert
        self.state = ExplorationState()
        self.evaluate_all = evaluate_all
        self.on_question = on_question
        self.undecided = undecided
        self._added: tuple[PartialObject[O, A], ...] = ()

    def run(self, start=None):
        """Explore from the first closed set, or from the first closed set
        lectically at or after `start`, which resumes an exploration.

        The exploration stops early if an object or a rejected implication
        refutes an implication accepted as unconfirmed: that implication has
        steered the enumeration, which has to be resumed from the question it
        was accepted at without it. `state.stopped_by` then holds it.

        A question the trusted knowledge already shows false is not asked
        (see `_question`). The objects the expert gives besides an answer
        (`Expert.new_objects`) are added once the answer has been applied.
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
                    conclusion = self._question(premise, closure & ~premise)
                    if self._stopped():
                        return self.state
                    if not conclusion:
                        closure = self.base.context_closure_mask(premise)
                        continue
                    implication = Implication(
                        premise=index.decode(premise),
                        conclusion=index.decode(conclusion),
                    )
                    counterexample = self.expert.validate(
                        implication,
                        self.base.attributes if self.evaluate_all else None
                    )
                    self.state.questions_asked += 1
                    self._added = tuple(self.expert.new_objects())
                    if isinstance(counterexample, Undecided):
                        premise = self._leave_open(implication, counterexample)
                        self._add_objects()
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
                        self._add_objects()
                        if self._stopped():
                            return self.state
                        closure = self.base.context_closure_mask(premise)
                    else:
                        source = (
                            ImplicationSource.CONFIRMED
                            if self.expert.is_conclusive()
                            else ImplicationSource.UNCONFIRMED
                        )
                        if source is ImplicationSource.UNCONFIRMED and self.undecided == "reject":
                            premise = self._leave_open(implication, Undecided())
                            self._add_objects()
                            if self._stopped():
                                return self.state
                            break
                        self._report(implication, None, source)
                        self.base.accept(implication, source)
                        self.state.accepted_implications.append(implication)
                        self._add_objects()
                        if self._stopped():
                            return self.state
                        premise = premises.send(True)
                        break
                else:
                    premise = next(premises)

        except StopIteration:
            pass

        return self.state

    def _question(self, premise: int, conclusion: int) -> int:
        """The conclusion to ask about with `premise`, or 0 if the context
        closure has to be computed again first.

        If the trusted knowledge shows the implication with the whole
        conclusion false, it is not asked. Each attribute of the conclusion
        that the trusted knowledge shows not to follow from the premise gets
        a derived witness, which takes it out of the context closure. If
        there is none, the attributes contradict only together, and the
        first of them is asked about alone.
        """
        if not self.base.known_false_mask(premise, conclusion):
            return conclusion
        if self._settle(premise, conclusion) != conclusion:
            return 0
        return conclusion & -conclusion

    def _settle(self, premise: int, conclusion: int) -> int:
        """Give each attribute of `conclusion` that the trusted knowledge
        shows not to follow from `premise`, and that no object refutes yet,
        a derived witness; return the other attributes, those not settled."""
        base = self.base
        closure = base.context_closure_mask(premise)
        left = 0
        for position in bits(conclusion & closure):
            if base.known_false_mask(premise, 1 << position):
                refuted = Implication(base.index.decode(premise), base.index.decode(1 << position))
                witness = PartialObject(Witness(refuted, derived=True), set(refuted.premise), set(refuted.conclusion))
                base.add_counterexample(witness)
                self.state.counterexamples.append(witness)
            else:
                left |= 1 << position
        return left

    def _add_objects(self) -> None:
        for obj in self._added:
            self.base.add_counterexample(obj)
            self.state.added_objects.append(obj)
        self._added = ()

    def _stopped(self) -> bool:
        refuted = self.base.earliest_refuted()
        if refuted is None:
            return False
        self.state.stopped_by = refuted[0]
        return True

    def _leave_open(self, implication: Implication[A], answer: Undecided[O, A]) -> int:
        """Take an answer the expert could not decide and return the next
        premise.

        The object the answer carries is added first, then the part of the
        conclusion the expert proved is accepted. What the trusted
        implications then entail is proved as well; the rest is rejected or,
        if the expert knows nothing against it, accepted as unconfirmed or,
        with `undecided="reject"`, rejected tentatively: each of its
        attributes gets a tentative object.

        The object, with what was proved, may show the rest false, although
        the question was not known false. Its attributes that an object now
        refutes, or that the trusted knowledge shows false on their own (see
        `_settle`), are then settled; the others, which the expert knows
        nothing against, are accepted as unconfirmed, together if they do
        not contradict anything together and one by one otherwise, or
        rejected tentatively. Nothing is asked again.

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
        index = self.base.index
        premise = index.encode(implication.premise)
        proved = index.encode(answer.proved & implication.conclusion)
        accepted = False
        if proved:
            # First, so that a resumed round keeps it.
            confirmed = Implication(implication.premise, index.decode(proved))
            self.base.accept(confirmed, ImplicationSource.CONFIRMED)
            self.state.accepted_implications.append(confirmed)
            accepted = True
        rest_mask = index.encode(implication.conclusion) & ~self.base.trusted_implications.closure_mask(premise | proved)
        rest = Implication(implication.premise, index.decode(rest_mask))
        if answer.rejected:
            if not rest_mask:
                raise ValueError(f'The expert rejects {implication} but proves all of it')
            if rest_mask & (rest_mask - 1) == 0:
                # Some object has the premise and what it implies, and lacks
                # the one attribute: a counterexample, if a partial one.
                witness = PartialObject(Witness(rest), index.decode(premise | proved), set(rest.conclusion))
                self.base.add_counterexample(witness)
                self.state.counterexamples.append(witness)
            else:
                self.base.reject(rest)
        elif rest_mask:
            together = True
            if answer.object is not None and self.base.known_false_mask(premise, rest_mask):
                rest_mask = self._settle(premise, rest_mask)
                together = not self.base.known_false_mask(premise, rest_mask)
            if self.undecided == "reject":
                for position in bits(rest_mask):
                    single = Implication(implication.premise, index.decode(1 << position))
                    self.base.add_tentative(single, Tentative(single))
            elif rest_mask:
                parts = [rest_mask] if together else [1 << position for position in bits(rest_mask)]
                for part in parts:
                    unconfirmed = Implication(implication.premise, index.decode(part))
                    self.base.accept(unconfirmed, ImplicationSource.UNCONFIRMED)
                    self.state.accepted_implications.append(unconfirmed)
                accepted = True
        if not accepted:
            return next(self._premises)
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
                added=self._added,
            )
        )
