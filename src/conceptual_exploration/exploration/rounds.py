from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from typing import Generic, Literal, TypeVar

from ..core.context import PartialObject
from ..core.implication import Implication
from ..experts.base import Expert
from .attribute import AttributeExploration, QuestionReport, Tentative
from .base import ExplorationBase, ImplicationSource, VersionedObject
from .state import ExplorationState

A = TypeVar("A")
O = TypeVar("O")


@dataclass
class RoundsResult(Generic[O, A]):
    """The outcome of `explore_in_rounds`: the base and state of the last
    round, and totals over all rounds."""

    base: ExplorationBase[O, A]
    state: ExplorationState
    rounds: int = 1
    questions_asked: int = 0
    counterexamples: list = field(default_factory=list)
    # Each unconfirmed implication refuted, with the object or the rejected
    # implication refuting it, and each tentative object refuted, with the
    # implication it stands for, which the trusted implications came to
    # entail.
    refuted: list[tuple[Implication[A] | Tentative[A], O | Implication[A]]] = field(default_factory=list)


def explore_in_rounds(
        attributes: Iterable[A],
        expert: Expert[O, A],
        background_implications: Iterable[Implication[A]] = (),
        mappings: Iterable[Callable] = (),
        objects: Iterable[PartialObject[O, A]] = (),
        evaluate_all: bool = False,
        on_question: Callable[[QuestionReport[O, A]], None] | None = None,
        on_resume: Callable[[Implication[A], O], None] | None = None,
        map_unconfirmed: bool = True,
        undecided: Literal["accept", "reject"] = "accept",
        confirmed: Iterable[Implication[A]] = (),
) -> RoundsResult[O, A]:
    """Explore, resuming whenever an object or a rejected implication
    refutes an implication accepted as unconfirmed, or the trusted
    implications contradict a tentative object.

    Such an implication or object has steered the enumeration since it was
    added, so the exploration stops (see `AttributeExploration.run`) and the
    next round resumes at the question it was added at. Every closed set
    before that question was enumerated without it, so nothing before is
    repeated. The next round starts with the implications accepted before
    that question, whatever their source; the confirmed ones accepted after
    it, which are sound whatever steered the enumeration to them; every
    object found; the tentative objects added before that question; and
    every rejected implication, which is false whatever steered the
    enumeration to it. It leaves out the refuted implication or object and
    the unconfirmed implications and tentative objects added after it, whose
    questions are asked again.

    `map_unconfirmed` is passed to `ExplorationBase`, and `undecided` to
    `AttributeExploration`. `confirmed` holds implications the expert
    confirmed in an earlier exploration: they are accepted as confirmed
    before anything else and kept in every round, and, unlike background
    implications, reported as found.

    The implications are then a sound and complete cover of the theory but
    need not be its canonical basis, the confirmed implications kept having
    been found under a different theory.
    """
    attributes = tuple(attributes)
    background = tuple(background_implications)
    mappings = tuple(mappings)
    history: list[tuple[Implication[A], ImplicationSource]] = []
    kept: list[Implication[A]] = list(confirmed)
    objects = list(objects)
    rejected: list[Implication[A]] = []
    # The implications the tentative objects kept stand for.
    tentative: list[Implication[A]] = []
    start = None
    result = None
    while True:
        base = ExplorationBase[O, A](
            attributes=attributes,
            background_implications=background,
            mappings=mappings,
            map_unconfirmed=map_unconfirmed,
        )
        for implication, source in history:
            base.accept(implication, source)
        for implication in kept:
            base.accept(implication, ImplicationSource.CONFIRMED)
        for obj in objects:
            base.add_counterexample(obj)
        for implication in tentative:
            base.add_tentative(implication, Tentative(implication))
        for implication in rejected:
            base.reject(implication)
        exploration = AttributeExploration(base, expert, evaluate_all, on_question, undecided)
        if base.refuted:
            # What the last round found refutes an earlier implication too.
            state = exploration.state
            state.stopped_by = base.earliest_refuted()[0]
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
        refuter = base.refuted[culprit]
        if isinstance(refuter, VersionedObject):
            refuter = refuter.original
        stands_for = base.tentative_objects.get(culprit)
        reported = culprit if stands_for is None else culprit.original
        result.refuted.append((reported, refuter))
        if on_resume is not None:
            on_resume(reported, refuter)
        # Unconfirmed implications and tentative objects come from different
        # modes, so the order of the two kinds never needs comparing beyond
        # a round.
        cut = base.added_at(culprit)
        accepted = history + [
            (implication, base.implication_sources[implication])
            for implication in state.accepted_implications
        ]
        history = [(i, source) for i, source in accepted if base.added_at(i) < cut]
        kept += [i for i, source in accepted if base.added_at(i) > cut and source is ImplicationSource.CONFIRMED]
        objects = [
            PartialObject(version.original, set(obj.positive), set(obj.negative))
            for version, obj in base.context.objects.items()
            if version.version == 0 and version not in base.tentative_objects
        ]
        tentative = [i for name, i in base.tentative_objects.items() if base.added_at(name) < cut]
        start = (culprit if stands_for is None else stands_for).premise
        rejected = list(base.rejected_implications)
