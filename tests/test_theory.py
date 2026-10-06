"""Unit tests for ImplicationTheory."""

import random

from conceptual_exploration import Implication
from conceptual_exploration.core.theory import ImplicationTheory, close_mask


def test_simplify_does_not_depend_on_insertion_order():
    """With a and b equivalent, either can be dropped from {a, b, c}; the one
    kept must not depend on how the theory or the premise was put together."""
    implications = [
        Implication({"a"}, {"b"}),
        Implication({"b"}, {"a"}),
    ]
    results = set()
    for theory_order in (implications, implications[::-1]):
        theory = ImplicationTheory(theory_order)
        for premise in (["a", "b", "c"], ["c", "b", "a"]):
            simplified = theory.simplify(Implication(premise, {"d"}))
            results.add(simplified.premise)

    assert results == {frozenset({"b", "c"})}


def test_closure_matches_the_reference_on_random_theories():
    """The transposed closure agrees with plain repeated passes, including
    for implications with empty premises or conclusions."""
    rng = random.Random(0)
    for _ in range(300):
        attributes = [f"a{i}" for i in range(rng.randrange(1, 12))]
        theory = ImplicationTheory()
        theory.index.encode(attributes)
        for _ in range(rng.randrange(0, 25)):
            theory.add(Implication(
                {a for a in attributes if rng.random() < 0.3},
                {a for a in attributes if rng.random() < 0.3},
            ))
        for _ in range(20):
            mask = rng.randrange(1 << len(attributes))
            assert theory.closure_mask(mask) == close_mask(mask, theory._masks)


if __name__ == "__main__":
    test_simplify_does_not_depend_on_insertion_order()
    test_closure_matches_the_reference_on_random_theories()
    print("All theory tests passed successfully!")
