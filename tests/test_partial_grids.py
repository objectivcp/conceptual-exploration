"""Tests for the exploration of deduction rules on partial 4x4 grids."""

import random

import pytest

from itertools import product

from conceptual_exploration import Implication, reduced_basis
from conceptual_exploration.logic.atom import Atom
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku import (
    ExplorationConfig,
    GEOMETRIC_PREDICATES,
    PartialGridExpert,
    SudokuSort,
    confinement_cells,
    geometry_basis,
    load_config,
    partial_grid_exploration,
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
    if name in ("Forced", "Excluded"):
        (r, c), digit = args
        completions = _completions(grid)
        if name == "Forced":
            return all(s[r][c] == digit for s in completions)
        return all(s[r][c] != digit for s in completions)
    if name.startswith("Confined"):
        cell, digit = args
        kept_out = confinement_cells(name, cell, 2)
        return all(s[r][c] != digit for s in _completions(grid) for r, c in kept_out)
    if name in ("SameNumber", "DifferentNumbers"):
        return (args[0] == args[1]) == (name == "SameNumber")
    (r1, c1), (r2, c2) = args
    return {
        "SameCell": (r1, c1) == (r2, c2),
        "DifferentCells": (r1, c1) != (r2, c2),
        "SameRow": r1 == r2,
        "DifferentRows": r1 != r2,
        "SameColumn": c1 == c2,
        "DifferentColumns": c1 != c2,
        "SameBlock": (r1 // 2, c1 // 2) == (r2 // 2, c2 // 2),
        "DifferentBlocks": (r1 // 2, c1 // 2) != (r2 // 2, c2 // 2),
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


@pytest.mark.parametrize("preset", ["cell", "units"])
def test_counterexamples_and_rules_are_right(preset):
    """Every counterexample refutes its question and has the attributes the
    expert claims for it, and the accepted rules hold on random grids."""
    exploration = partial_grid_exploration(preset)
    expert = exploration.expert
    validate = expert.validate

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

    expert.validate = checked
    exploration.run()

    variables = load_config(f"partial-{preset}").variables
    rng = random.Random(0)
    for _ in range(500):
        grid, assignment = _random_state(variables, rng)
        for implication in exploration.base.accepted_implications:
            holds = lambda a: _holds(a, grid, assignment)
            if all(map(holds, implication.premise)):
                assert all(map(holds, implication.conclusion)), str(implication)


@pytest.mark.parametrize("preset", ["cell", "units"])
def test_background_holds_on_partial_grids(preset):
    config = load_config(f"partial-{preset}")
    variables, names = config.variables, config.predicates
    predicates = sudoku_predicates(names)
    expert = PartialGridExpert(variables)
    background = sudoku_background(predicates, variables)
    assert background
    for implication in background:
        assert expert.validate(implication) is None, str(implication)


def _atom(name, *args):
    (predicate,) = sudoku_predicates([name])
    return Atom(predicate, args)


def test_naked_and_hidden_singles_are_found():
    x, n1, n2, n3, n4 = load_config("partial-cell").variables
    cell = partial_grid_exploration("cell")
    cell.run()
    naked_single = Implication(
        {_atom("Excluded", x, n) for n in (n2, n3, n4)}
        | {_atom("DifferentNumbers", a, b) for a, b in
           [(n1, n2), (n1, n3), (n1, n4), (n2, n3), (n2, n4), (n3, n4)]},
        {_atom("Forced", x, n1)},
    )
    assert cell.base.implications.entails(naked_single)

    w, x, y, z, n = load_config("partial-row").variables
    row = partial_grid_exploration("row")
    row.run()
    cells = (w, x, y, z)
    distinct_in_row = (
        {_atom("DifferentCells", a, b) for i, a in enumerate(cells) for b in cells[i + 1:]}
        | {_atom("SameRow", w, c) for c in (x, y, z)}
    )
    hidden_single = Implication(
        distinct_in_row | {_atom("Excluded", c, n) for c in (x, y, z)},
        {_atom("Forced", w, n)},
    )
    elimination = Implication(
        {_atom("Forced", w, n), _atom("SameRow", w, x), _atom("DifferentCells", w, x)},
        {_atom("Excluded", x, n)},
    )
    assert row.base.implications.entails(hidden_single)
    assert row.base.implications.entails(elimination)
    # Neither is background: the exploration had to find them.
    background_only = partial_grid_exploration("row").base.implications
    assert not background_only.entails(hidden_single)
    assert not background_only.entails(elimination)


def test_geometry_basis_holds_on_every_placement():
    config = load_config("partial-units")
    variables, names = config.variables, config.predicates
    cells = [v for v in variables if v.sort is SudokuSort.CELL]
    basis = geometry_basis(variables, names)
    assert basis
    assert all(a.predicate.name in GEOMETRIC_PREDICATES for i in basis for a in i.premise | i.conclusion)
    empty = ((0,) * 4,) * 4
    for positions in product(product(range(4), repeat=2), repeat=len(cells)):
        assignment = tuple((v.name, p) for v, p in zip(cells, positions))
        for implication in basis:
            if all(_holds(a, empty, assignment) for a in implication.premise):
                assert all(_holds(a, empty, assignment) for a in implication.conclusion)


def test_exploring_geometry_first_reports_only_deductions():
    """The two-stage exploration has the same theory as the one-stage one,
    but leaves the geometry to the background."""
    one = partial_grid_exploration("units", geometry_first=False)
    two = partial_grid_exploration("units", geometry_first=True)
    one.run()
    two.run()
    assert all(two.base.implications.entails(i) for i in one.base.implications)
    assert all(one.base.implications.entails(i) for i in two.base.implications)

    geometric = lambda rule: not any(
        a.predicate.name in ("Forced", "Excluded") for a in rule.premise | rule.conclusion
    )
    assert any(map(geometric, reduced_basis(one.base)))
    assert not any(map(geometric, reduced_basis(two.base)))


def test_only_4x4_grids_are_supported():
    with pytest.raises(ValueError):
        PartialGridExpert([SortedVariable("x", SudokuSort.CELL)], block_size=3)


@pytest.mark.parametrize("name", ["partial-cell", "partial-units"])
def test_cegar_expert_agrees_with_enumeration(name):
    """On 4x4 grids, where every solved grid can be listed, the CEGAR expert
    reaches the same theory."""
    from conceptual_exploration.exploration.rule import RuleExploration
    from explorations.sudoku.sudoku import CegarPartialGridExpert

    config = load_config(name)
    variables, predicates = config.variables, sudoku_predicates(config.predicates)
    theories = []
    for expert in (PartialGridExpert(variables), CegarPartialGridExpert(variables, 2)):
        exploration = RuleExploration(
            predicates,
            variables,
            expert,
            background=sudoku_background(predicates, variables),
            substitutions=True,
            evaluate_all=True,
        )
        exploration.run()
        theories.append({str(i) for i in exploration.base.implications})
    assert theories[0] == theories[1]


_LOCKED = {
    "grid": "partial",
    "cells": ["x", "y"],
    "numbers": ["n"],
    "predicates": [
        "SameRow", "DifferentRows", "SameBlock", "DifferentBlocks",
        "Excluded", "ConfinedToRowInBlock", "ConfinedToBlockInRow",
    ],
}


@pytest.mark.parametrize("expert", ["sat", "cegar"])
def test_confinement_is_decided_right(expert):
    """Both experts' counterexamples have the attributes they claim, checked
    against the solved grids directly, and the pointing rule is found."""
    exploration = ExplorationConfig.from_dict({**_LOCKED, "expert": expert}).rule_exploration()
    validate = exploration.expert.validate

    def checked(implication, attributes=None):
        counterexample = validate(implication, attributes)
        if counterexample is not None:
            witness = counterexample.object
            holds = lambda a: _holds(a, witness.grid, witness.assignment)
            assert all(map(holds, implication.premise))
            assert not all(map(holds, implication.conclusion))
            assert all(holds(a) == (a in counterexample.positive) for a in attributes)
        return counterexample

    exploration.expert.validate = checked
    exploration.run()

    x, y, n = ExplorationConfig.from_dict(_LOCKED).variables
    pointing = Implication(
        {
            _atom("ConfinedToRowInBlock", y, n),
            _atom("SameRow", x, y),
            _atom("DifferentBlocks", x, y),
        },
        {_atom("Excluded", x, n)},
    )
    assert exploration.base.implications.entails(pointing)


def test_cegar_agrees_with_enumeration_on_confinement():
    theories = []
    for expert in ("sat", "cegar"):
        exploration = ExplorationConfig.from_dict({**_LOCKED, "expert": expert}).rule_exploration()
        exploration.run()
        theories.append({str(i) for i in exploration.base.implications})
    assert theories[0] == theories[1]
