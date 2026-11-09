"""Unit tests for the implications printed for reading."""

from conceptual_exploration import Implication, simplified_implications
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource


def _equivalent(base, implications):
    """Whether the implications, with the background and the mappings, entail
    exactly what the base's theory does."""
    background = [
        i for i, s in base.implication_sources.items() if s is ImplicationSource.BACKGROUND
    ]
    rebuilt = ExplorationBase(
        base.attributes, background_implications=background, mappings=base.mappings
    )
    for implication in implications:
        rebuilt.accept(
            Implication(implication.premise, base.attributes if implication.everything else implication.conclusion)
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

    implications = simplified_implications(base)
    assert [str(implication) for implication in implications] == ["c -> a", "d -> everything", "e -> c"]
    assert implications[1].everything
    assert _equivalent(base, implications)


def test_a_rule_does_not_cut_itself_with_its_own_images():
    """r -> p, q is its own image under swapping p and q. Its images may stand
    in for half the conclusion, but not for all of it."""
    swap = {"p": "q", "q": "p", "r": "r", "s": "s"}
    base = ExplorationBase(attributes=["p", "q", "r", "s"], mappings=[lambda a: swap[a]])
    base.accept(Implication({"r"}, {"p", "q"}))

    implications = simplified_implications(base)
    assert len(implications) == 1
    assert len(implications[0].conclusion) == 1
    assert _equivalent(base, implications)


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

    implications = simplified_implications(base)
    assert [str(implication) for implication in implications] == ["x -> cell"]


def _rules(base):
    return {str(implication): implication.source for implication in simplified_implications(base)}


def test_a_confirmed_rule_is_not_cut_by_unconfirmed_ones():
    """p -> c is confirmed, p -> e and c -> e unconfirmed: cut with every
    implication, p -> c would vanish into p -> c, e; it stays confirmed."""
    base = ExplorationBase(attributes=["p", "c", "e", "z"])
    base.accept(Implication({"p"}, {"c"}), ImplicationSource.CONFIRMED)
    base.accept(Implication({"p"}, {"e"}), ImplicationSource.UNCONFIRMED)
    base.accept(Implication({"c"}, {"e"}), ImplicationSource.UNCONFIRMED)

    assert _rules(base) == {
        "p -> c": ImplicationSource.CONFIRMED,
        "p -> e": ImplicationSource.UNCONFIRMED,
        "c -> e": ImplicationSource.UNCONFIRMED,
    }
    assert _equivalent(base, simplified_implications(base))


def test_a_confirmed_rule_keeps_what_only_unconfirmed_ones_would_give():
    """q -> p, e is confirmed; p gives e only by the unconfirmed c -> e, so
    the confirmed implication keeps e."""
    base = ExplorationBase(attributes=["p", "c", "e", "q", "z"])
    base.accept(Implication({"c"}, {"e"}), ImplicationSource.UNCONFIRMED)
    base.accept(Implication({"p"}, {"c"}), ImplicationSource.CONFIRMED)
    base.accept(Implication({"q"}, {"p", "e"}), ImplicationSource.CONFIRMED)

    assert _rules(base) == {
        "c -> e": ImplicationSource.UNCONFIRMED,
        "p -> c": ImplicationSource.CONFIRMED,
        "q -> e, p": ImplicationSource.CONFIRMED,
    }


def test_open_steps_are_not_merged():
    """a -> b and a, b -> c are both unconfirmed: a, b -> c is not cut to
    a -> c, which would hide that it rests on a -> b."""
    base = ExplorationBase(attributes=["a", "b", "c", "z"])
    base.accept(Implication({"a"}, {"b"}), ImplicationSource.UNCONFIRMED)
    base.accept(Implication({"a", "b"}, {"c"}), ImplicationSource.UNCONFIRMED)

    assert _rules(base) == {
        "a -> b": ImplicationSource.UNCONFIRMED,
        "a, b -> c": ImplicationSource.UNCONFIRMED,
    }


def test_format_uses_the_given_names():
    base = ExplorationBase(attributes=[1, 2])
    base.accept(Implication(set(), {1}))
    (implication,) = simplified_implications(base)
    assert implication.format(lambda a: f"law {a}") == "∅ -> law 1"


if __name__ == "__main__":
    test_premises_and_conclusions_are_cut()
    test_a_rule_does_not_cut_itself_with_its_own_images()
    test_rules_keep_the_attribute_the_others_follow_from()
    test_format_uses_the_given_names()
    print("All basis tests passed successfully!")
