from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from typing import Generic, TypeVar

from ..core.context import PartialObject
from ..core.implication import Implication
from ..experts.base import Expert
from .attribute import AttributeExploration, QuestionReport
from .base import ExplorationBase, ImplicationSource
from .state import ExplorationState

A = TypeVar("A")
O = TypeVar("O")


def lectically_before(x: int, y: int) -> bool:
    """Whether attribute mask x comes before y in the lectic order of
    NextClosure, where the attribute of the lowest bit weighs most."""
    difference = x ^ y
    return bool(difference & -difference & y)


@dataclass
class RoundsResult(Generic[O, A]):
    """The outcome of `explore_in_rounds`: the base and state of the last
    round, and totals over all rounds."""

    base: ExplorationBase[O, A]
    state: ExplorationState
    rounds: int = 1
    questions_asked: int = 0
    counterexamples: list = field(default_factory=list)
    # Each unconfirmed implication refuted, with the object refuting it.
    refuted: list[tuple[Implication[A], O]] = field(default_factory=list)


def explore_in_rounds(
        attributes: Iterable[A],
        expert: Expert[O, A],
        background_implications: Iterable[Implication[A]] = (),
        mappings: Iterable[Callable] = (),
        objects: Iterable[PartialObject[O, A]] = (),
        evaluate_all: bool = False,
        on_question: Callable[[QuestionReport[O, A]], None] | None = None,
        on_resume: Callable[[Implication[A], O], None] | None = None,
) -> RoundsResult[O, A]:
    """Explore, resuming whenever an object refutes an implication accepted
    as unconfirmed.

    Such an implication has steered the enumeration since it was accepted,
    so the exploration stops (see `AttributeExploration.run`) and the next
    round resumes at the question it was accepted at. Every closed set before
    that question was enumerated without it, so nothing before is repeated.
    The next round starts with the implications accepted before that
    question, whatever their source; the confirmed ones accepted after it,
    which are sound whatever steered the enumeration to them; every object
    found; and the open questions before it. It leaves out the refuted
    implication and the unconfirmed ones accepted after it, whose questions
    are asked again.

    The theory is then sound and complete but need not be a canonical basis,
    the confirmed implications kept having been found under a different
    theory.
    """
    attributes = tuple(attributes)
    background = tuple(background_implications)
    mappings = tuple(mappings)
    history: list[tuple[Implication[A], ImplicationSource]] = []
    kept: list[Implication[A]] = []
    objects = list(objects)
    open_before: list[Implication[A]] = []
    start = None
    result = None
    while True:
        base = ExplorationBase[O, A](
            attributes=attributes,
            background_implications=background,
            mappings=mappings,
        )
        for implication, source in history:
            base.accept(implication, source)
        for implication in kept:
            base.accept(implication, ImplicationSource.CONFIRMED)
        for obj in objects:
            base.add_counterexample(obj)
        base.open_questions.extend(open_before)
        exploration = AttributeExploration(base, expert, evaluate_all, on_question)
        if base.refuted:
            # An object of the last round refutes an earlier implication too.
            state = exploration.state
            state.stopped_by = base.origin(next(iter(base.refuted)))
        else:
            state = exploration.run(start)
        if result is None:
            result = RoundsResult(base, state, rounds=1)
        else:
            result.base, result.state = base, state
            result.rounds += 1
        result.questions_asked += state.questions_asked
        result.counterexamples += state.counterexamples
        if state.stopped_by is None:
            return result

        culprit = state.stopped_by
        refuter = next(iter(base.refuted.values())).original
        result.refuted.append((culprit, refuter))
        if on_resume is not None:
            on_resume(culprit, refuter)
        accepted = history + [
            (implication, base.implication_sources[implication])
            for implication in state.accepted_implications
        ]
        k = next(n for n, (implication, _) in enumerate(accepted) if implication == culprit)
        history = accepted[:k]
        kept += [i for i, source in accepted[k + 1:] if source is ImplicationSource.CONFIRMED]
        objects = [
            PartialObject(version.original, set(obj.positive), set(obj.negative))
            for version, obj in base.context.objects.items()
            if version.version == 0
        ]
        start = culprit.premise
        start_mask = base.index.encode(start)
        open_before = [
            question for question in base.open_questions
            if lectically_before(base.index.encode(question.premise), start_mask)
        ]
