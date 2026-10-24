"""Unit tests for semigroup laws as words and their classes."""

import random
import shutil

import pytest

from explorations.equational_theories import semigroup
from explorations.equational_theories.magma import Equation, Magma
from explorations.equational_theories.semigroup import (
    Evaluator,
    canonical,
    classes,
    equation,
    law_of,
    laws,
    reversal,
    text,
)


def test_a_law_has_one_form_up_to_renaming_and_sides():
    assert canonical((2, 1), (1, 2, 2)) == canonical((0, 1, 1), (1, 0)) == ((0, 1), (1, 0, 0))
    assert text(canonical((1,), (1, 0, 1))) == "x = xyx"


def test_the_laws_up_to_order_four_are_le_flochs_653():
    assert [len(laws(k)) for k in range(5)] == [2, 7, 31, 135, 653]


def test_the_reversal_reverses_both_words():
    assert reversal(canonical((0,), (0, 1))) == canonical((0,), (1, 0))
    assert reversal(canonical((0, 1), (1, 0))) == canonical((0, 1), (1, 0))


def test_a_law_and_its_magma_form_correspond():
    law = canonical((0, 1, 0), (1, 0))
    eq = equation(law)
    assert (eq.lhs.factors(), eq.rhs.factors()) == (["x", "y"], ["y", "x", "y"])
    assert eq.rhs == eq.rhs.right_associated()
    assert law_of(eq) == law
    assert law_of(Equation.parse("(y * x) * y = x * y")) == law


def test_the_evaluator_agrees_with_the_magma_laws():
    rng = random.Random(1)
    semigroups = semigroup.small_semigroups(3) if shutil.which("mace4") else [Magma.left_projection(3)]
    for magma in semigroups:
        evaluator = Evaluator(magma.table, samples=4)
        for law in rng.sample(laws(4), 60):
            assert evaluator.holds(law) == magma.holds(equation(law))


def test_a_law_with_too_many_assignments_is_unknown_unless_it_fails():
    left_zero = Magma.left_projection(4)
    evaluator = Evaluator(left_zero.table, budget=4 ** 3)
    assert evaluator.holds(canonical((0, 1, 2, 3), (0, 3))) is None
    assert evaluator.holds(canonical((0, 1, 2, 3), (1,))) is False


@pytest.mark.skipif(shutil.which("mace4") is None, reason="Mace4 not installed")
def test_the_small_semigroups_up_to_isomorphism():
    assert [len([m for m in semigroup.small_semigroups(3) if m.size == n]) for n in (1, 2, 3)] == [1, 5, 24]


def test_laws_join_a_class_when_proved_equivalent_and_never_when_separated():
    x_xy, x_yx, xy_yx = canonical((0,), (0, 1)), canonical((0,), (1, 0)), canonical((0, 1), (1, 0))
    x_yxx, xyz_xzy = canonical((0,), (1, 0, 0)), canonical((0, 1, 2), (0, 2, 1))
    found_laws = [x_xy, x_yx, xy_yx, x_yxx, xyz_xzy]
    # One semigroup separates x = xy from the others; no other is known.
    rows = [[True, False, False, False, False], [None] * 5]
    asked = []

    def status(a, b):
        asked.append((a, b))
        if {a, b} == {xy_yx, x_yx}:
            return "CounterSatisfiable"
        return "Timeout" if xyz_xzy in (a, b) else "Theorem"
    found, unresolved = classes(found_laws, rows, status)
    assert sorted(found) == sorted([[x_xy], [x_yx, x_yxx], [xy_yx], [xyz_xzy]])
    assert all(x_xy not in pair for pair in asked)
    assert unresolved and all(xyz_xzy in pair for pair in unresolved)


def test_a_law_reads_back_from_its_text():
    law = canonical((0, 1, 2), (2, 0))
    assert semigroup.parse_law(text(law)) == law


def test_the_second_pass_merges_the_pairs_proved_and_separates_by_the_models_found():
    x_yx, x_yxx, x_xy, xy_yx = (canonical((0,), (1, 0)), canonical((0,), (1, 0, 0)),
                                canonical((0,), (0, 1)), canonical((0, 1), (1, 0)))
    representatives = [x_yx, x_yxx, x_xy, xy_yx]
    right_zero = Magma.right_projection(2)  # x = yx holds, x = xy fails

    def refute(a, b):
        return right_zero if (a, b) == (x_yx, x_xy) else None

    def prove(a, b):
        return "Theorem" if {a, b} == {x_yx, x_yxx} else "Timeout"
    equivalent, models, undecided = semigroup.settle(
        representatives, [(0, 1), (0, 2), (2, 3)], [[None] * 4], refute, prove
    )
    assert equivalent == [(0, 1)] and models == [right_zero] and undecided == [(2, 3)]
    found = semigroup.merged([[x_yx], [x_yxx], [x_xy], [xy_yx]], equivalent)
    assert found == [[x_xy], [x_yx, x_yxx], [xy_yx]]


@pytest.mark.skipif(shutil.which("mace4") is None, reason="Mace4 not installed")
def test_mace4_finds_a_checked_countermodel():
    model = semigroup.mace4_model(shutil.which("mace4"), canonical((0,), (1, 0)), canonical((0,), (0, 1)), 5)
    assert model is not None and model.size == 2
    # No semigroup of fewer than five elements satisfies x = x^6 but not x = xx.
    model = semigroup.mace4_model(shutil.which("mace4"), semigroup.parse_law("x = xxxxxx"), semigroup.parse_law("x = xx"), 10)
    assert model is not None and model.size == 5


def test_the_exploration_inputs_are_closed_under_reversal_with_the_order4_theory_mapped():
    entry = lambda law, etp=None: {"law": law, "order": 0, **({"etp": etp} if etp else {})}
    classes = [
        [entry("x = xy", 4), entry("x = xyy", 8)],  # dual to the next class
        [entry("x = yx", 5)],
        [entry("x = xx", 3)],
        # Self-dual: xy = yx is its own reversal, though not the smallest law.
        [entry("x = xxy"), entry("x = yxx"), entry("xy = yx", 43)],
        # Self-dual with no law its own reversal: both laws are taken.
        [entry("x = xyz", 6), entry("x = yzx", 7)],
    ]
    order4 = [{"premise": [8], "conclusion": [3], "source": "confirmed"}]
    laws, background = semigroup.exploration_inputs(classes, order4)
    idents = [law.get("id", law.get("name")) for law in laws]
    assert idents == [4, 5, 3, 43, 6, 7, 4512]
    assert {"premise": [6], "conclusion": [7]} in background and {"premise": [7], "conclusion": [6]} in background
    # Mapped to the law taken from the class, and reversed.
    assert {"premise": [4], "conclusion": [3]} in background
    assert {"premise": [5], "conclusion": [3]} in background


def test_the_commutative_form_sorts_the_words_up_to_renaming():
    assert semigroup.commutative_form(semigroup.parse_law("xy = yx")) == semigroup.TRIVIAL
    assert semigroup.commutative_form(semigroup.parse_law("x = xyx")) == semigroup.commutative_form(
        semigroup.parse_law("x = yxx")
    )
    assert text(semigroup.commutative_form(semigroup.parse_law("xy = yyx"))) == "xxy = xy"
    forms = {semigroup.commutative_form(law) for law in laws(5)}
    assert len(forms) == 246


class FakeEtp:
    """ETP numbers for the laws of order at most 4, as the ETP numbers them."""

    def __init__(self):
        self.numbers = {law: k for k, law in enumerate(laws(4), start=1)}

    def id_of(self, eq):
        return self.numbers.get(law_of(eq))


def test_the_commutative_inputs_merge_laws_equivalent_among_semigroups_or_commutatively_equal():
    etp = FakeEtp()
    n = lambda line: etp.numbers[semigroup.parse_law(line)]
    every = list(etp.numbers.values())
    # One class per law, except that x = xy and x = xyy are equivalent.
    order4_laws = [{"id": k, "equation": str(equation(law)), "class": [k]} for law, k in etp.numbers.items()]
    order4 = [{"premise": [n("x = xy")], "conclusion": [n("x = xyy")]},
              {"premise": [n("x = xyy")], "conclusion": [n("x = xy")]},
              {"premise": [n("x = yx")], "conclusion": [n("x = xx")]}]
    entries, background = semigroup.commutative_inputs(5, order4_laws, order4, etp)
    idents = [e.get("id", e.get("name")) for e in entries]
    assert n("x = xy") in idents and n("x = xyy") not in idents
    # x = yx is x = xy among commutative semigroups.
    assert n("x = yx") not in idents
    assert {"premise": [n("x = xy")], "conclusion": [n("x = xx")]} in background
    assert idents[-2:] == [4512, 43] and all(isinstance(i, str) for i in idents if i not in every + [4512, 43])


def test_the_square_free_monomials_on_five_generators_refute_what_no_smaller_semigroup_does():
    magma = semigroup.monomial_semigroup(5, lambda v: max(v) < 2, "square-free")
    assert magma.size == 32 and magma.holds(semigroup.ASSOCIATIVITY) and magma.holds(semigroup.COMMUTATIVITY)
    assert magma.holds(equation(semigroup.parse_law("xx = yyzwu")))
    assert not magma.holds(equation(semigroup.parse_law("xx = xyzwu")))
    assert semigroup.monomial_semigroup(5, lambda v: max(v) < 2, "too big", max_size=31) is None


def test_the_heisenberg_group_over_z5_has_exponent_5_and_does_not_commute():
    group = semigroup.heisenberg_group(5)
    assert group.size == 125 and group.holds(semigroup.ASSOCIATIVITY)
    assert group.holds(equation(semigroup.parse_law("x = yyyyyx")))
    assert not group.holds(equation(semigroup.parse_law("xy = yx")))
