"""Tests for background implications derived by bounded equational reasoning."""

from itertools import combinations, product
from pathlib import Path

import pytest

from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from explorations.equational_theories.background import BoundedDerivation, background_implications
from explorations.equational_theories.magma import ETP, Equation, Magma

EQUATIONS = Path(__file__).resolve().parent.parent / "explorations" / "equational_theories" / "equations_1var_order4.json"


def derives(max_order: int, premises: list[str], conclusion: str) -> bool:
    derivation = BoundedDerivation(max_order)
    derived = derivation.closure(derivation.pair(Equation.parse(p)) for p in premises)
    return derivation.pair(Equation.parse(conclusion)) in derived.pairs


def test_multiplying_both_sides():
    assert derives(3, ["x = x * x"], "x * x = (x * x) * x")
    assert derives(3, ["x = x * x"], "x * x = x * (x * x)")


def test_substituting_for_the_variable():
    assert derives(4, ["x = x * x"], "x * x = (x * x) * (x * x)")


def test_replacing_a_subterm():
    # Eq4065 and Eq4380 give Eq3862 by rewriting (x * x) * x to x * (x * x).
    assert derives(
        4,
        ["x * x = ((x * x) * x) * x", "x * (x * x) = (x * x) * x"],
        "x * x = (x * (x * x)) * x",
    )


def test_transitivity_and_symmetry():
    assert derives(4, ["x = x * (x * x)", "x * (x * x) = (x * x) * x"], "(x * x) * x = x")


def test_order_bounds_the_equations_used():
    premises = [
        "x = (x * x) * (x * x)",
        "x = (((x * x) * x) * x) * x",
        "x * x = ((x * x) * x) * x",
    ]
    assert not derives(4, premises, "x * x = x * (x * x)")
    assert derives(6, premises, "x * x = x * (x * x)")


def test_derivation_stays_within_the_order():
    derivation = BoundedDerivation(1)
    derived = derivation.closure([derivation.pair(Equation.parse("x = x * x"))])
    assert len(derived.pairs) == 1


def test_basis_entails_exactly_what_is_derivable():
    attributes = ETP.load_equations(EQUATIONS)[:10] + ETP.load_equations(EQUATIONS)[-3:]
    derivation = BoundedDerivation(4)
    pairs = [derivation.pair(eq) for eq in attributes]
    theory = ImplicationTheory(background_implications(attributes, 4))
    for size in range(4):
        for chosen in combinations(range(len(attributes)), size):
            derived = derivation.closure(pairs[i] for i in chosen).pairs
            expected = {eq for eq, p in zip(attributes, pairs) if p[0] == p[1] or p in derived}
            assert theory.closure({attributes[i] for i in chosen}) == expected | {
                attributes[i] for i in chosen
            }


def test_background_holds_in_all_small_magmas():
    attributes = ETP.load_equations(EQUATIONS)[:12]
    magmas = [
        Magma(2, (entries[:2], entries[2:]))
        for entries in product(range(2), repeat=4)
    ] + [Magma.rock_paper_scissors(), Magma.cyclic_subtraction(3), Magma.cyclic_multiplication(3)]
    for implication in background_implications(attributes, 5):
        for magma in magmas:
            holding = frozenset(eq for eq in attributes if magma.holds(eq))
            assert implication.respected_by(holding), (implication, magma)


def test_background_is_accepted_as_such():
    attributes = ETP.load_equations(EQUATIONS)[:6]
    background = background_implications(attributes, 4)
    base = ExplorationBase(attributes, background_implications=background)
    assert all(base.implication_sources[i] is ImplicationSource.BACKGROUND for i in background)
    assert base.accepted_implications == ()


def test_rejects_equations_outside_the_derivation():
    with pytest.raises(ValueError, match="one variable"):
        background_implications([Equation.parse("x * y = y * x"), Equation.parse("x = x")], 4)
    with pytest.raises(ValueError, match="above max_order"):
        background_implications([Equation.parse("x = x * (x * x)")], 1)
