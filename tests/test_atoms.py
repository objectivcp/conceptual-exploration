"""Unit tests for atoms, predicate properties and their normalization."""

import pytest

from conceptual_exploration import Implication
from conceptual_exploration.core.truth import Truth
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.atom import Atom, atoms_over, normalize_implication
from conceptual_exploration.logic.predicate import Predicate
from conceptual_exploration.logic.variable import Variable

x, y, z = Variable("x"), Variable("y"), Variable("z")
equal = Predicate("Equal", 2, symmetric=True, reflexive=True, complement="Unequal")
unequal = Predicate("Unequal", 2, symmetric=True, irreflexive=True, complement="Equal")
less = Predicate("Less", 2, irreflexive=True)


def test_normalize():
    assert Atom(equal, (y, x)).normalize() == Atom(equal, (x, y))
    canonical = Atom(equal, (x, y))
    assert canonical.normalize() is canonical
    assert Atom(equal, (x, x)).normalize() is Truth.TRUE
    assert Atom(unequal, (y, y)).normalize() is Truth.FALSE
    # Not symmetric, so both orders stay.
    assert Atom(less, (y, x)).normalize() == Atom(less, (y, x))


def test_atoms_over_keeps_canonical_atoms_only():
    atoms = atoms_over([equal, less], [x, y, z])
    assert set(map(str, atoms)) == {
        "Equal(x, y)", "Equal(x, z)", "Equal(y, z)",
        "Less(x, y)", "Less(x, z)", "Less(y, x)",
        "Less(y, z)", "Less(z, x)", "Less(z, y)",
    }


def test_inconsistent_properties_are_rejected():
    with pytest.raises(ValueError):
        Predicate("P", 3, symmetric=True)
    with pytest.raises(ValueError):
        Predicate("P", 2, reflexive=True, irreflexive=True)


def test_normalize_implication():
    atoms = atoms_over([equal, unequal], [x, y])
    e, u = Atom(equal, (x, y)), Atom(unequal, (x, y))

    # True atoms drop out, and non-canonical ones are rewritten.
    assert normalize_implication(
        Implication({Atom(equal, (x, x)), Atom(equal, (y, x))}, {Atom(unequal, (y, x))}),
        atoms,
    ) == Implication({e}, {u})
    # A false premise atom makes the implication say nothing.
    assert normalize_implication(Implication({Atom(unequal, (x, x))}, {e}), atoms) is None
    # So does a conclusion that is true or already in the premise.
    assert normalize_implication(Implication({e}, {Atom(equal, (y, y)), e}), atoms) is None
    # A false conclusion atom means the premise cannot hold.
    assert normalize_implication(Implication({e}, {Atom(unequal, (x, x))}), atoms) == Implication({e}, {u})


class _EqualityExpert(Expert):
    """Answers questions about Equal/Unequal over x, y, z by enumerating the
    ways of assigning them to three points."""

    def validate(self, implication, attributes=None):
        from itertools import product
        for values in product(range(3), repeat=3):
            assignment = dict(zip((x, y, z), values))
            holds = lambda a: (
                (assignment[a.arguments[0]] == assignment[a.arguments[1]])
                == (a.predicate.name == "Equal")
            )
            if all(map(holds, implication.premise)) and not all(map(holds, implication.conclusion)):
                from conceptual_exploration.core.context import PartialObject
                atoms = set(attributes or implication.premise | implication.conclusion)
                positive = {a for a in atoms if holds(a)}
                return PartialObject(values, positive, atoms - positive)
        return None


def test_rule_exploration_uses_the_declared_properties():
    exploration = RuleExploration(
        [equal, unequal],
        [x, y, z],
        _EqualityExpert(),
        substitutions=True,
        evaluate_all=True,
    )
    # Complements give {Equal(a), Unequal(a)} -> ⊥, once per pair.
    assert len(exploration.background) == 3
    assert all(len(i.premise) == 2 for i in exploration.background)

    exploration.run()
    base = exploration.base
    # Symmetry, reflexivity and the complements are built in, so what is left
    # is transitivity, and its contrapositive form for Unequal, which Horn
    # rules cannot derive from it; the substitutions map one confirmed
    # instance of each onto the others.
    assert len(base.accepted_implications) == 2
    assert base.implications.entails(
        Implication({Atom(equal, (x, z)), Atom(equal, (y, z))}, {Atom(equal, (x, y))})
    )
    assert base.implications.entails(
        Implication({Atom(equal, (x, y)), Atom(unequal, (y, z))}, {Atom(unequal, (x, z))})
    )
