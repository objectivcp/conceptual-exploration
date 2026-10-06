"""Unit tests for the reduced basis printed for reading."""

from conceptual_exploration import Implication, reduced_basis
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource


def _equivalent(base, rules):
    """Whether the rules, with the background and the mappings, entail
    exactly what the base's theory does."""
    background = [
        i for i, s in base.implication_sources.items() if s is ImplicationSource.BACKGROUND
    ]
    rebuilt = ExplorationBase(
        base.attributes, background_implications=background, mappings=base.mappings
    )
    for rule in rules:
        rebuilt.accept(
            Implication(rule.premise, base.attributes if rule.everything else rule.conclusion)
        )
    return (
        all(rebuilt.implications.entails(i) for i in base.implications)
        and all(base.implications.entails(i) for i in rebuilt.implications)
    )


def test_premises_and_conclusions_are_cut():
    base = ExplorationBase(
        attributes=["a", "b", "c", "d", "e"],
        background_implications=[Implication({"a"}, {"b"})],
    )
    base.accept(Implication({"c"}, {"a", "b"}))
    base.accept(Implication({"d"}, {"a", "b", "c", "e"}))
    base.accept(Implication({"e"}, {"c"}))
    # Everything this says follows from e -> c, c -> a and a -> b.
    base.accept(Implication({"e", "b"}, {"a"}))

    rules = reduced_basis(base)
    assert [str(rule) for rule in rules] == ["c -> a", "d -> everything", "e -> c"]
    assert rules[1].everything
    assert _equivalent(base, rules)


def test_a_rule_does_not_cut_itself_with_its_own_images():
    """r -> p, q is its own image under swapping p and q. Its images may stand
    in for half the conclusion, but not for all of it."""
    swap = {"p": "q", "q": "p", "r": "r", "s": "s"}
    base = ExplorationBase(attributes=["p", "q", "r", "s"], mappings=[lambda a: swap[a]])
    base.accept(Implication({"r"}, {"p", "q"}))

    rules = reduced_basis(base)
    assert len(rules) == 1
    assert len(rules[0].conclusion) == 1
    assert _equivalent(base, rules)


def test_rules_keep_the_attribute_the_others_follow_from():
    """Of the conclusion attributes, the one entailing the rest is kept."""
    base = ExplorationBase(
        attributes=["same", "row", "column", "cell", "x"],
        background_implications=[
            Implication({"cell"}, {"row", "column"}),
            Implication({"row", "column"}, {"cell"}),
        ],
    )
    base.accept(Implication({"x"}, {"row", "column", "cell"}))

    rules = reduced_basis(base)
    assert [str(rule) for rule in rules] == ["x -> cell"]


def test_format_uses_the_given_names():
    base = ExplorationBase(attributes=[1, 2])
    base.accept(Implication(set(), {1}))
    (rule,) = reduced_basis(base)
    assert rule.format(lambda a: f"law {a}") == "∅ -> law 1"


if __name__ == "__main__":
    test_premises_and_conclusions_are_cut()
    test_a_rule_does_not_cut_itself_with_its_own_images()
    test_rules_keep_the_attribute_the_others_follow_from()
    test_format_uses_the_given_names()
    print("All basis tests passed successfully!")
