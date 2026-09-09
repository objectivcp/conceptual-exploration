import random

from itertools import combinations

from conceptual_exploration.algorithms.next_closure import NextClosure
from conceptual_exploration.core.implication import Implication
from core.theory import ImplicationTheory


def powerset(attributes):
    attributes = tuple(attributes)

    for r in range(len(attributes) + 1):
        for subset in combinations(attributes, r):
            yield frozenset(subset)


def brute_force_closed_sets(
    attributes,
    closure_operator,
):
    closed = set()

    for subset in powerset(attributes):

        c = frozenset(
            closure_operator(subset)
        )

        closed.add(c)

    return closed


def random_theory(
    attributes,
    n_implications=10,
):
    theory = ImplicationTheory()

    attrs = tuple(attributes)

    for _ in range(n_implications):

        premise = frozenset(
            a
            for a in attrs
            if random.random() < 0.3
        )

        conclusion = frozenset(
            a
            for a in attrs
            if random.random() < 0.3
        )

        theory.add(
            Implication(
                premise,
                conclusion,
            )
        )

    return theory


def test_next_closure_one():

    attrs = ("a", "b", "c", "d")
    theory = ImplicationTheory()
    theory.add(Implication(frozenset({"c", "d"}), frozenset({"a"})))
    theory.add(Implication(frozenset({"a"}), frozenset({"c"})))
    theory.add(Implication(frozenset({"a", "b", "c"}), frozenset({"d"})))

    nc = set(
        NextClosure(
            attrs,
            theory.closure,
        ).generate()
    )

    assert nc == {frozenset(),
                  frozenset({"d"}),
                  frozenset({"c"}),
                  frozenset({"b"}),
                  frozenset({"b", "d"}),
                  frozenset({"b", "c"}),
                  frozenset({"a", "c"}),
                  frozenset({"a", "c", "d"}),
                  frozenset({"a", "b", "c", "d"})}


def test_next_closure_complete():

    attrs = ("a", "b", "c", "d")

    for _ in range(100):

        theory = random_theory(attrs)

        nc = set(
            NextClosure(
                attrs,
                theory.closure,
            ).generate()
        )

        brute = brute_force_closed_sets(
            attrs,
            theory.closure,
        )

        if nc != brute:
            print()
            print("=== FAILURE ===")
            print("Attributes:", attrs)
            print()

            print("Implications:")
            for implication in theory.implications:
                print(" ", implication)

            print()

            print("Generated:")
            for s in sorted(nc, key=lambda x: (len(x), sorted(x))):
                print(" ", s)

            print()

            print("Expected:")
            for s in sorted(brute, key=lambda x: (len(x), sorted(x))):
                print(" ", s)

        assert nc == brute

def test_all_generated_sets_are_closed():

    attrs = ("a", "b", "c", "d")

    for _ in range(100):

        theory = random_theory(attrs)

        for s in NextClosure(
            attrs,
            theory.closure,
        ).generate():

            assert (
                frozenset(
                    theory.closure(s)
                )
                == s
            )


def test_no_duplicates():

    attrs = ("a", "b", "c", "d")

    for _ in range(100):

        theory = random_theory(attrs)

        result = list(
            NextClosure(
                attrs,
                theory.closure,
            ).generate()
        )

        assert len(result) == len(set(result))


def test_first_element():

    attrs = ("a", "b", "c")

    theory = random_theory(attrs)

    result = list(
        NextClosure(
            attrs,
            theory.closure,
        ).generate()
    )

    assert result[0] == frozenset(
        theory.closure(frozenset())
    )


def test_last_element():

    attrs = ("a", "b", "c", "d")

    theory = random_theory(attrs)

    result = list(
        NextClosure(
            attrs,
            theory.closure,
        ).generate()
    )

    assert result[-1] == frozenset(attrs)


def lectic_less(
    x,
    y,
    attributes,
):
    for a in attributes:

        in_x = a in x
        in_y = a in y

        if in_x != in_y:
            return in_y

    return False


def test_lectic_order():

    attrs = ("a", "b", "c", "d")

    for _ in range(100):

        theory = random_theory(attrs)

        result = list(
            NextClosure(
                attrs,
                theory.closure,
            ).generate()
        )

        for x, y in zip(
            result,
            result[1:],
        ):
            assert lectic_less(
                x,
                y,
                attrs,
            )