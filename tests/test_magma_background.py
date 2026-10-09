"""Unit tests for background implications derived between one-variable magma laws."""

from itertools import product
from pathlib import Path

import pytest

from conceptual_exploration.core.theory import ImplicationTheory
from explorations.equational_theories.background import Derivations, background_implications
from explorations.equational_theories.magma import ETP, Equation, Magma

EQUATIONS_PATH = (
    Path(__file__).resolve().parent.parent
    / "explorations" / "equational_theories" / "equations_1var_order4.json"
)


def derives(order: int, premises: list[str], conclusion: str) -> bool:
    derivations = Derivations("x", order)
    seeds = [derivations.pair(eq.lhs, eq.rhs) for eq in map(Equation.parse, premises)]
    target = Equation.parse(conclusion)
    return derivations.pair(target.lhs, target.rhs) in derivations.closure(seeds)


def magmas_up_to(size: int):
    for n in range(1, size + 1):
        for entries in product(range(n), repeat=n * n):
            yield Magma(n, tuple(tuple(entries[i * n:(i + 1) * n]) for i in range(n)))


def test_multiplying_both_sides():
    assert derives(3, ["x = x * x"], "x * x = x * (x * x)")
    assert derives(3, ["x = x * x"], "x * x = (x * x) * x")


def test_substituting_for_the_variable():
    # One step of rule 2; rules 1 and 3 need several steps for this.
    derivations = Derivations("x", 4)
    premise, conclusion = (
        derivations.pair(eq.lhs, eq.rhs)
        for eq in map(Equation.parse, ["x = x * x", "x * x = (x * x) * (x * x)"])
    )
    numbers = {equation: i for i, equation in enumerate(derivations.equations)}
    assert numbers[conclusion] in derivations._derives[numbers[premise]]


def test_replacing_a_subterm_and_transitivity():
    assert derives(4, ["x = x * (x * x)", "x * (x * x) = (x * x) * x"], "x = (x * x) * x")
    assert derives(4, ["x * x = x", "x = x * (x * x)"], "x * x = x * x * x")


def test_derivations_stay_within_the_order():
    # Multiplying x = x * x by x gives an equation of order 3.
    assert not derives(2, ["x = x * x"], "x * x = x * (x * x)")
    # Rule 2 alone takes x * x = x * (x * x) to order 3 + 5 = 8 at the least.
    assert not derives(4, ["x * x = x * (x * x)"], "x = x * x")


def test_background_implications_hold_in_small_magmas():
    equations = ETP.load_equations(EQUATIONS_PATH)
    background = background_implications(equations, order=4)
    assert background
    for magma in magmas_up_to(2):
        holds = frozenset(eq for eq in equations if magma.holds(eq))
        assert all(implication.respected_by(holds) for implication in background)


def test_trivial_law_has_an_empty_premise():
    equations = ETP.load_equations(EQUATIONS_PATH)
    trivial = next(eq for eq in equations if eq.id == 1)
    theory = ImplicationTheory(background_implications(equations, order=4))
    assert trivial in theory.closure(set())


def test_premise_size_bound():
    equations = ETP.load_equations(EQUATIONS_PATH)
    background = background_implications(equations, order=4, max_premise_size=1)
    assert max(len(implication.premise) for implication in background) <= 1


def test_canonical_basis_entails_bounded_premises():
    equations = [
        eq for eq in ETP.load_equations(EQUATIONS_PATH)
        if eq.lhs.op_count() + eq.rhs.op_count() <= 3
    ]
    exact = ImplicationTheory(background_implications(equations, order=3, max_premise_size=None))
    bounded = background_implications(equations, order=3, max_premise_size=2)
    assert all(exact.entails(implication) for implication in bounded)


def test_rejects_unsupported_input():
    with pytest.raises(ValueError, match="one variable"):
        background_implications([Equation.parse("x * y = y * x")], order=4)
    with pytest.raises(ValueError, match="below the order"):
        background_implications([Equation.parse("x = x * (x * x)")], order=1)
