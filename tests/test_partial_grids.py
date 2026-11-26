"""Tests for the exploration of partial 4x4 grids with Forced, Excluded and
Possible."""

import random

import pytest

from conceptual_exploration import (
    Implication,
    classically_irredundant,
    simplified_implications,
    trusted_theory,
)
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from conceptual_exploration.logic.atom import Atom
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku import (
    CONFINEMENT_PREDICATES,
    GEOMETRIC_PREDICATES,
    PAIR_CONFINEMENT_PREDICATES,
    PARTIAL_PREDICATES,
    ExplorationConfig,
    PartialGridExpert,
    SatSudokuRuleExpert,
    SudokuSort,
    confinement_cells,
    pair_confinement_cells,
    sudoku_background,
    sudoku_predicates,
    sudoku_solutions,
)

SOLUTIONS = sudoku_solutions(2)


def _completions(grid):
    return [
        s for s in SOLUTIONS
        if all(grid[r][c] in (0, s[r][c]) for r in range(4) for c in range(4))
    ]


def _holds(atom, grid, assignment):
    """Evaluate an atom on a partial grid from the solved grids directly,
    without the SAT encoding."""
    values = dict(assignment)
    args = [values[v.name] for v in atom.arguments]
    name = atom.predicate.name
    completions = _completions(grid)
    if name in PARTIAL_PREDICATES:
        (r, c), digit = args
        has = [s[r][c] == digit for s in completions]
        return {"Forced": all(has), "Excluded": not any(has), "Possible": any(has)}[name]
    if name in PAIR_CONFINEMENT_PREDICATES:
        cell, other, digit = args
        kept_out = pair_confinement_cells(name, cell, other, 2)
        return all(s[r][c] != digit for s in completions for r, c in kept_out)
    if name in CONFINEMENT_PREDICATES:
        cell, digit = args
        kept_out = confinement_cells(name, cell, 2)
        return all(s[r][c] != digit for s in completions for r, c in kept_out)
    if name in ("SameNumber", "DifferentNumbers"):
        return (args[0] == args[1]) == (name == "SameNumber")
    (r1, c1), (r2, c2) = args
    same_block = (r1 // 2, c1 // 2) == (r2 // 2, c2 // 2)
    return {
        "SameCell": (r1, c1) == (r2, c2),
        "DifferentCells": (r1, c1) != (r2, c2),
        "SameRow": r1 == r2,
        "DifferentRows": r1 != r2,
        "SameColumn": c1 == c2,
        "DifferentColumns": c1 != c2,
        "SameBlock": same_block,
        "DifferentBlocks": not same_block,
    }[name]


def _random_state(variables, rng):
    """A partial grid with at least one completion, and values for the
    variables."""
    solution = rng.choice(SOLUTIONS)
    density = rng.choice((0.2, 0.4, 0.6))
    grid = tuple(
        tuple(solution[r][c] if rng.random() < density else 0 for c in range(4))
        for r in range(4)
    )
    assignment = tuple(
        (v.name, (rng.randrange(4), rng.randrange(4)))
        if v.sort is SudokuSort.CELL
        else (v.name, rng.randrange(1, 5))
        for v in variables
    )
    return grid, assignment


def _atom(name, *args):
    (predicate,) = sudoku_predicates([name])
    return Atom(predicate, args).normalize()


_CELL = {
    "grid": "partial", "cells": ["x"], "numbers": ["n1", "n2", "n3", "n4"],
    "predicates": ["Forced", "Excluded", "Possible", "SameNumber", "DifferentNumbers"],
}
_ROW = {
    "grid": "partial", "cells": ["w", "x", "y", "z"], "numbers": ["n"],
    "predicates": ["SameCell", "DifferentCells", "SameRow", "Forced", "Excluded", "Possible"],
}
_UNITS = {
    "grid": "partial", "cells": ["x", "y", "z"], "numbers": ["n"],
    "predicates": ["SameCell", "DifferentCells", "SameRow", "SameColumn", "SameBlock",
                   "Forced", "Excluded", "Possible"],
}


@pytest.mark.parametrize("settings", [_CELL, _UNITS], ids=["cell", "units"])
def test_counterexamples_and_rules_are_right(settings):
    """Every counterexample refutes its question and has the attributes the
    expert claims for it, and the accepted rules hold on random grids."""
    config = ExplorationConfig.from_dict(settings)
    exploration = config.rule_exploration()
    validate = exploration.expert.validate

    def checked(implication, attributes=None):
        counterexample = validate(implication, attributes)
        if counterexample is not None:
            witness = counterexample.object
            holds = lambda a: _holds(a, witness.grid, witness.assignment)
            assert _completions(witness.grid)
            assert all(map(holds, implication.premise))
            assert not all(map(holds, implication.conclusion))
            assert all(holds(a) == (a in counterexample.positive) for a in attributes)
        return counterexample

    exploration.expert.validate = checked
    exploration.run()

    rng = random.Random(0)
    for _ in range(300):
        grid, assignment = _random_state(config.variables, rng)
        holds = lambda a: _holds(a, grid, assignment)
        for implication in exploration.base.accepted_implications:
            if all(map(holds, implication.premise)):
                assert all(map(holds, implication.conclusion)), str(implication)


def test_background_holds_on_partial_grids():
    cells = [SortedVariable(v, SudokuSort.CELL) for v in "xy"]
    numbers = [SortedVariable(v, SudokuSort.NUMBER) for v in "nm"]
    variables = cells + numbers
    # The pair predicates are left out: deciding them over every solved grid
    # takes a minute, and their background, without Possible, holds on
    # partial grids if it does on solved ones (test_sudoku_techniques).
    predicates = sudoku_predicates(
        GEOMETRIC_PREDICATES + PARTIAL_PREDICATES + ("SameNumber", "DifferentNumbers")
        + CONFINEMENT_PREDICATES
    )
    expert = PartialGridExpert(variables)
    background = sudoku_background(predicates, variables)
    assert background
    for implication in background:
        assert expert.validate(implication) is None, str(implication)


def test_possible_makes_partial_grids_objects_of_their_own():
    """A cell holds one digit, but may have two possible ones."""
    x = SortedVariable("x", SudokuSort.CELL)
    n, m = (SortedVariable(v, SudokuSort.NUMBER) for v in "nm")
    one_value = lambda name: Implication({_atom(name, x, n), _atom(name, x, m)}, {_atom("SameNumber", n, m)})
    assert SatSudokuRuleExpert(2, [x, n, m]).validate(one_value("Contains")) is None
    assert PartialGridExpert([x, n, m]).validate(one_value("Forced")) is None
    assert PartialGridExpert([x, n, m]).validate(one_value("Possible")) is not None


def test_contrapositives_are_dropped_classically():
    """With Possible, the contrapositive of elimination is accepted too;
    read classically it says nothing new, and elimination is kept."""
    exploration = ExplorationConfig.from_dict(_ROW).rule_exploration()
    exploration.run()
    base = exploration.base
    w, x, y, z, n = ExplorationConfig.from_dict(_ROW).variables
    elimination = Implication(
        {_atom("Forced", z, n), _atom("DifferentCells", y, z), _atom("SameRow", y, z)},
        {_atom("Excluded", y, n)},
    )
    contrapositive = Implication(
        {_atom("Forced", z, n), _atom("Possible", y, n), _atom("SameRow", y, z)},
        {_atom("SameCell", y, z)},
    )
    assert base.implications.entails(elimination)
    assert base.implications.entails(contrapositive)
    rules = simplified_implications(base)
    about_digits = lambda rule: any(a.predicate.name in PARTIAL_PREDICATES for a in rule.conclusion)
    kept = classically_irredundant(base, rules, drop_first=about_digits)
    assert len(kept) < len(rules)
    assert any(rule.premise == elimination.premise for rule in kept)
    assert not any(rule.premise == contrapositive.premise for rule in kept)
    # What is kept, with the background and the images, entails every rule
    # classically.
    background = [i for i, s in base.implication_sources.items() if s is ImplicationSource.BACKGROUND]
    rebuilt = ExplorationBase(base.attributes, background_implications=background, mappings=base.mappings)
    for rule in kept:
        rebuilt.accept(Implication(rule.premise, base.attributes if rule.everything else rule.conclusion))
    theory = trusted_theory(rebuilt)
    for rule in rules:
        assert theory.entails(rule.premise, base.attributes if rule.everything else rule.conclusion), str(rule)
