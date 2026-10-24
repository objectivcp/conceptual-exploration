"""Unit tests for truncated free semigroups and their countermodels."""

from explorations.equational_theories.free_semigroup import Truncated, truncated_countermodels, words
from explorations.equational_theories.magma import Equation

ASSOCIATIVITY = Equation.parse("x * (y * z) = (x * y) * z")
law = lambda text: Equation.parse(text)


def test_a_truncated_free_semigroup_is_the_free_one_cut_at_a_length():
    # Commutative: of the words below length 3 on two generators, ab = ba,
    # leaving a, b, aa, ab, bb and the zero.
    commutative = Truncated([words(law("x * y = y * x"))], 2, 3)
    assert commutative.element("ab") == commutative.element("ba") != commutative.zero
    assert commutative.element("aab") == commutative.zero and len(commutative.names) == 6
    # Among bands, a = aa = aaaa, which is cut off: everything is the zero.
    assert len(Truncated([words(law("x = x * x"))], 2, 3).names) == 1


def test_the_countermodel_to_question_266_is_found_and_checked():
    premise = [ASSOCIATIVITY, law("x * (x * x) = x * (x * (x * x))"), law("x * (x * x) = y * (x * (x * x))"),
               law("x * (x * y) = y * (x * (y * y))")]
    goal = law("x * (x * x) = y * (y * (z * x))")
    [model] = truncated_countermodels(premise, [goal], max_words=4000)
    assert model.size == 39
    assert all(model.holds(eq) for eq in premise) and not model.holds(goal)


def test_a_law_that_follows_gets_no_countermodel():
    # x = xy implies x = xyz.
    assert truncated_countermodels([ASSOCIATIVITY, law("x = x * y")], [law("x = x * (y * z)")], max_words=500) == []


def test_the_search_gives_up_at_its_time_limit():
    import time
    # x = yzwuvt has millions of instances on four generators below length 7.
    premise = [ASSOCIATIVITY, law("x = y * (z * (w * (u * (v * t))))")]
    start = time.monotonic()
    assert truncated_countermodels(premise, [law("x = x * (y * (z * w))")], max_words=6000, time_limit=1) == []
    assert time.monotonic() - start < 5
