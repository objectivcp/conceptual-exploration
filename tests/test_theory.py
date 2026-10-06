"""Unit tests for ImplicationTheory."""

from conceptual_exploration import Implication
from conceptual_exploration.core.theory import ImplicationTheory


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


if __name__ == "__main__":
    test_simplify_does_not_depend_on_insertion_order()
    print("All theory tests passed successfully!")
