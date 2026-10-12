"""Unit tests for explorations resumed after an unconfirmed implication is refuted."""

from itertools import combinations

from conceptual_exploration import Expert, Implication, PartialObject, Undecided, explore_in_rounds
from conceptual_exploration.exploration.base import ImplicationSource

ATTRIBUTES = ["a", "b", "c"]
# The objects the expert knows, in the order it consults them.
WORLD = [("empty", set()), ("only b", {"b"}), ("a and c", {"a", "c"}), ("only a", {"a"})]


class Hiding(Expert):
    """Answers truthfully, except that it first leaves c -> a, b undecided,
    which the exploration accepts as unconfirmed although "a and c" refutes it."""

    def __init__(self):
        self.hidden = True
        self.inconclusive = False

    def validate(self, implication, attributes=None):
        self.inconclusive = False
        if implication.premise == {"c"} and self.hidden:
            self.hidden = False
            self.inconclusive = True
            return None
        for name, row in WORLD:
            if implication.premise <= row and not implication.conclusion <= row:
                return PartialObject(name, set(row), set(ATTRIBUTES) - row)
        return None

    def is_conclusive(self):
        return not self.inconclusive


def world_closure(attributes):
    rows = [row for _, row in WORLD if attributes <= row]
    return set(ATTRIBUTES).intersection(*rows) if rows else set(ATTRIBUTES)


def test_refuted_unconfirmed_implication_is_dropped_and_the_exploration_resumed():
    resumed = []
    result = explore_in_rounds(
        ATTRIBUTES, Hiding(), on_resume=lambda implication, obj: resumed.append((implication, obj))
    )
    culprit = Implication(frozenset({"c"}), frozenset({"a", "b"}))
    assert resumed == [(culprit, "a and c")]
    assert result.rounds == 2
    assert result.refuted == resumed
    assert culprit not in result.base.implications
    # The theory is that of the objects: sound and complete.
    for r in range(len(ATTRIBUTES) + 1):
        for subset in combinations(ATTRIBUTES, r):
            assert result.base.implications.closure(set(subset)) == world_closure(set(subset))


class Splitting(Hiding):
    """Like Hiding, but first answers c -> a, b by proving a and accepting b
    as unconfirmed, which "a and c" refutes."""

    def validate(self, implication, attributes=None):
        if implication.premise == {"c"} and self.hidden:
            self.hidden = False
            return Undecided(frozenset({"a"}), unconfirmed=True)
        return super().validate(implication, attributes)


def test_the_confirmed_part_of_a_split_answer_survives_its_unconfirmed_part():
    result = explore_in_rounds(ATTRIBUTES, Splitting())
    proved = Implication(frozenset({"c"}), frozenset({"a"}))
    culprit = Implication(frozenset({"c"}), frozenset({"b"}))
    assert [implication for implication, _ in result.refuted] == [culprit]
    assert result.rounds == 2
    assert result.base.implication_sources[proved] is ImplicationSource.CONFIRMED
    assert culprit not in result.base.implications
    for r in range(len(ATTRIBUTES) + 1):
        for subset in combinations(ATTRIBUTES, r):
            assert result.base.implications.closure(set(subset)) == world_closure(set(subset))
