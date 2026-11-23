"""Tests for classical entailment between implications."""

import pytest

pytest.importorskip("pysat")

from conceptual_exploration import (
    ClassicalTheory,
    Implication,
    classically_irredundant,
    simplified_implications,
)
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from conceptual_exploration.logic.atom import Atom
from conceptual_exploration.logic.predicate import Predicate
from conceptual_exploration.logic.variable import Variable

x = Variable("x")
p, not_p, r, not_r = (
    Atom(Predicate(name, 1, complement=complement), (x,))
    for name, complement in (("P", "NotP"), ("NotP", "P"), ("R", "NotR"), ("NotR", "R"))
)
ATOMS = [p, not_p, r, not_r]
# What the rule exploration adds for complements: no object has both.
EXCLUSIVE = [Implication({p, not_p}, ATOMS), Implication({r, not_r}, ATOMS)]


def test_complements_give_contrapositives_and_cases():
    theory = ClassicalTheory()
    theory.add({p}, {r})
    assert theory.entails({not_r}, {not_p})
    assert not theory.entails({not_p}, {not_r})
    theory.add({not_p}, {r})
    assert theory.entails(set(), {r})


def test_attributes_without_complements_are_plain_variables():
    theory = ClassicalTheory()
    theory.add({"a"}, {"b"})
    theory.add({"b"}, {"c"})
    assert theory.entails({"a"}, {"c"})
    assert not theory.entails({"c"}, {"a"})


def test_guarded_clauses_count_only_when_assumed():
    theory = ClassicalTheory()
    guard = theory.guard()
    theory.add({"a"}, {"b"}, guard)
    assert not theory.entails({"a"}, {"b"})
    assert theory.entails({"a"}, {"b"}, [guard])


def _base(*implications, source=ImplicationSource.CONFIRMED):
    base = ExplorationBase(ATOMS, background_implications=EXCLUSIVE)
    for implication in implications:
        base.accept(implication, source)
    return base


def test_a_contrapositive_form_is_dropped():
    base = _base(Implication({p}, {r}), Implication({not_r}, {not_p}))
    implications = simplified_implications(base)
    # By Horn closure neither follows from the other.
    assert len(implications) == 2
    assert [str(i) for i in classically_irredundant(base, implications)] == ["P(x) -> R(x)"]
    kept = classically_irredundant(base, implications, drop_first=lambda i: p not in i.premise)
    assert [str(i) for i in kept] == ["NotR(x) -> NotP(x)"]


def test_unconfirmed_implications_are_neither_dropped_nor_used():
    base = _base(Implication({p}, {r}), source=ImplicationSource.UNCONFIRMED)
    base.accept(Implication({not_r}, {not_p}))
    implications = simplified_implications(base)
    assert len(implications) == 2
    assert classically_irredundant(base, implications) == implications


def test_images_under_the_mappings_are_used():
    """Swapping P and R (and their complements) maps P -> R to R -> P, so
    with it NotP -> NotR is the contrapositive of an image."""
    swap = {p: r, r: p, not_p: not_r, not_r: not_p}
    base = ExplorationBase(ATOMS, background_implications=EXCLUSIVE, mappings=[swap.__getitem__])
    base.accept(Implication({p}, {r}))
    base.accept(Implication({not_p}, {not_r}))
    implications = simplified_implications(base)
    assert len(implications) == 2
    assert [str(i) for i in classically_irredundant(base, implications)] == ["P(x) -> R(x)"]
