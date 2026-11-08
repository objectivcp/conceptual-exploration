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
            return Undecided(frozenset({"a"}))
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


class Random(Expert):
    """Answers from a world closed under random rules and their images under
    `swap`: for a false implication, a refuting object with some values
    hidden, the rest rejected as a whole, or, the first time only, an
    unknown rest; for a true one, a confirmation or an unknown rest."""

    def __init__(self, attributes, swap, rules, seed):
        import random
        self.rng = random.Random(seed)
        self.attributes = attributes
        rows = [self._close({a for a in attributes if self.rng.random() < 0.3}, rules) for _ in range(12)]
        self.world = [frozenset(r) for row in rows for r in (row, {swap[a] for a in row})]
        self.hidden = set()

    @staticmethod
    def _close(row, rules):
        while True:
            new = {c for p, c in rules if p <= row} - row
            if not new:
                return row
            row |= new

    def validate(self, implication, attributes=None):
        for k, row in enumerate(self.world):
            if implication.premise <= row and not implication.conclusion <= row:
                if implication not in self.hidden and self.rng.random() < 0.3:
                    self.hidden.add(implication)
                    return Undecided()
                if self.rng.random() < 0.2:
                    return Undecided(rejected=True)
                failing = self.rng.choice(sorted(implication.conclusion - row))
                hidden = {a for a in self.attributes if self.rng.random() < 0.4} - implication.premise - {failing}
                return PartialObject(f"g{k}", set(row) - hidden, set(self.attributes) - row - hidden)
        if self.rng.random() < 0.4:
            return Undecided()
        return None


def test_no_unconfirmed_implication_contradicts_the_objects_or_the_rejected_ones_on_its_own():
    import random
    from conceptual_exploration.core.theory import ImplicationTheory

    # Over these seeds, about 60 rounds resume, two of them after a rejected
    # implication, and about ten witnesses are derived.
    attributes = list("abcdefgh")
    swap = dict(zip("abcdefgh", "efghabcd"))
    for seed in range(60):
        rng = random.Random(seed)
        rules = [(set(rng.sample(attributes, 2)), rng.choice(attributes)) for _ in range(5)]
        rules += [({swap[a] for a in p}, swap[c]) for p, c in rules]
        result = explore_in_rounds(attributes, Random(attributes, swap, rules, seed), mappings=[lambda a: swap[a]])
        base = result.base
        sources = base.implication_sources
        trusted = list(base.trusted_implications)
        rows = [(set(o.positive), set(o.negative)) for o in base.context.objects.values()]
        for unconfirmed in base.unconfirmed_implications:
            group = [i for i in base.implications if base.origin(i) == unconfirmed and sources[i] in (
                ImplicationSource.UNCONFIRMED, ImplicationSource.MAPPED_UNCONFIRMED)]
            theory = ImplicationTheory(trusted + group, index=base.index)
            for positive, negative in rows:
                assert not set(theory.closure(positive)) & negative, (seed, unconfirmed)
            for rejected in base.rejected_implications:
                assert not rejected.conclusion <= set(theory.closure(set(rejected.premise))), (seed, unconfirmed)
        for rejected in base.rejected_implications:
            assert not base.trusted_implications.entails(rejected), seed
