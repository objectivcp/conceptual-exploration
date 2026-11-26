"""Tests for the deduction techniques found on solved grids, with NotContains
and the confinement predicates."""

import random
from itertools import product

import pytest

from conceptual_exploration import Implication, simplified_implications
from conceptual_exploration.logic.atom import Atom
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku import (
    CONFINEMENT_PREDICATES,
    GEOMETRIC_PREDICATES,
    PAIR_CONFINEMENT_PREDICATES,
    ExplorationConfig,
    SatSudokuRuleExpert,
    SudokuSort,
    check_rules,
    confinement_cells,
    geometry_basis,
    load_config,
    pair_confinement_cells,
    sudoku_background,
    sudoku_predicates,
    sudoku_solutions,
)

SOLUTIONS = sudoku_solutions(2)


def _holds(atom, grid, assignment, block_size=2):
    """Evaluate an atom on a solved grid directly, without the SAT encoding."""
    k = block_size
    values = dict(assignment)
    args = [values[v.name] for v in atom.arguments]
    name = atom.predicate.name
    if name in ("Contains", "NotContains"):
        (r, c), digit = args
        return (grid[r][c] == digit) == (name == "Contains")
    if name in PAIR_CONFINEMENT_PREDICATES:
        cell, other, digit = args
        return all(grid[r][c] != digit for r, c in pair_confinement_cells(name, cell, other, k))
    if name in CONFINEMENT_PREDICATES:
        cell, digit = args
        return all(grid[r][c] != digit for r, c in confinement_cells(name, cell, k))
    if name in ("SameNumber", "DifferentNumbers"):
        return (args[0] == args[1]) == (name == "SameNumber")
    (r1, c1), (r2, c2) = args
    same_block = (r1 // k, c1 // k) == (r2 // k, c2 // k)
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


def _checked(exploration, block_size=2):
    """The exploration, with each counterexample checked against its grid
    directly: it refutes the question and has the attributes claimed."""
    validate = exploration.expert.validate

    def checked(implication, attributes=None):
        counterexample = validate(implication, attributes)
        if counterexample is not None:
            witness = counterexample.object
            holds = lambda a: _holds(a, witness.grid, witness.assignment, block_size)
            assert all(map(holds, implication.premise))
            assert not all(map(holds, implication.conclusion))
            assert all(holds(a) == (a in counterexample.positive) for a in attributes)
        return counterexample

    exploration.expert.validate = checked
    return exploration


def _atom(name, *args):
    (predicate,) = sudoku_predicates([name])
    return Atom(predicate, args)


@pytest.mark.parametrize("name", ["solved-cell", "solved-units"])
def test_counterexamples_and_rules_are_right(name):
    """Every counterexample is right, and the accepted rules hold on random
    grids, cells and digits."""
    config = load_config(name)
    exploration = _checked(config.rule_exploration())
    exploration.run()

    rng = random.Random(0)
    for _ in range(500):
        grid = rng.choice(SOLUTIONS)
        assignment = tuple(
            (v.name, (rng.randrange(4), rng.randrange(4)))
            if v.sort is SudokuSort.CELL
            else (v.name, rng.randrange(1, 5))
            for v in config.variables
        )
        holds = lambda a: _holds(a, grid, assignment)
        for implication in exploration.base.accepted_implications:
            if all(map(holds, implication.premise)):
                assert all(map(holds, implication.conclusion)), str(implication)


# Three cells take 45 s on 9x9 grids, the pair predicates most of it.
@pytest.mark.parametrize("block_size, cell_names", [(2, "xyz"), (3, "xy")])
def test_background_holds_with_the_techniques_vocabulary(block_size, cell_names):
    cells = [SortedVariable(v, SudokuSort.CELL) for v in cell_names]
    numbers = [SortedVariable(v, SudokuSort.NUMBER) for v in "nm"]
    variables = cells + numbers
    predicates = sudoku_predicates(
        GEOMETRIC_PREDICATES
        + ("Contains", "NotContains", "SameNumber", "DifferentNumbers")
        + CONFINEMENT_PREDICATES
        + PAIR_CONFINEMENT_PREDICATES
    )
    expert = SatSudokuRuleExpert(block_size, variables)
    background = sudoku_background(predicates, variables)
    assert background
    for implication in background:
        assert expert.validate(implication) is None, str(implication)


def _hidden_single_and_elimination():
    w, x, y, z, n = load_config("solved-row").variables
    cells = (w, x, y, z)
    distinct_in_row = (
        {_atom("DifferentCells", a, b) for i, a in enumerate(cells) for b in cells[i + 1:]}
        | {_atom("SameRow", w, c) for c in (x, y, z)}
    )
    hidden_single = Implication(
        distinct_in_row | {_atom("NotContains", c, n) for c in (x, y, z)},
        {_atom("Contains", w, n)},
    )
    elimination = Implication(
        {_atom("Contains", w, n), _atom("SameRow", w, x), _atom("DifferentCells", w, x)},
        {_atom("NotContains", x, n)},
    )
    return hidden_single, elimination


def test_naked_and_hidden_singles_are_found():
    x, n1, n2, n3, n4 = load_config("solved-cell").variables
    cell = load_config("solved-cell").rule_exploration()
    cell.run()
    naked_single = Implication(
        {_atom("NotContains", x, n) for n in (n2, n3, n4)}
        | {_atom("DifferentNumbers", a, b) for a, b in
           [(n1, n2), (n1, n3), (n1, n4), (n2, n3), (n2, n4), (n3, n4)]},
        {_atom("Contains", x, n1)},
    )
    assert cell.base.implications.entails(naked_single)

    hidden_single, elimination = _hidden_single_and_elimination()
    row = load_config("solved-row").rule_exploration()
    # Neither is background: the exploration has to find them.
    assert not row.base.implications.entails(hidden_single)
    assert not row.base.implications.entails(elimination)
    row.run()
    assert row.base.implications.entails(hidden_single)
    assert row.base.implications.entails(elimination)


def test_singles_over_four_cells_fail_on_9x9_grids():
    """A row of a 4x4 grid has four cells, one of a 9x9 grid nine: the
    hidden single over four cells holds only on the small grids, while
    elimination holds on both."""
    hidden_single, elimination = _hidden_single_and_elimination()
    variables = load_config("solved-row").variables
    results = dict(check_rules([hidden_single, elimination], 3, variables))
    assert results[elimination] is None
    witness = results[hidden_single].object
    holds = lambda a: _holds(a, witness.grid, witness.assignment, 3)
    assert all(map(holds, hidden_single.premise))
    assert not all(map(holds, hidden_single.conclusion))


def test_geometry_basis_holds_on_every_placement():
    config = load_config("solved-units")
    variables, names = config.variables, config.predicates
    cells = [v for v in variables if v.sort is SudokuSort.CELL]
    basis = geometry_basis(variables, names)
    assert basis
    assert all(a.predicate.name in GEOMETRIC_PREDICATES for i in basis for a in i.premise | i.conclusion)
    for positions in product(product(range(4), repeat=2), repeat=len(cells)):
        assignment = tuple((v.name, p) for v, p in zip(cells, positions))
        holds = lambda a: _holds(a, SOLUTIONS[0], assignment)
        for implication in basis:
            if all(map(holds, implication.premise)):
                assert all(map(holds, implication.conclusion))


def test_exploring_geometry_first_reports_only_deductions():
    """The two-stage exploration has the same theory as the one-stage one,
    but leaves the geometry to the background."""
    config = load_config("solved-units")
    one = config.with_overrides(geometry_first=False).rule_exploration()
    two = config.with_overrides(geometry_first=True).rule_exploration()
    one.run()
    two.run()
    assert all(two.base.implications.entails(i) for i in one.base.implications)
    assert all(one.base.implications.entails(i) for i in two.base.implications)

    geometric = lambda rule: not any(
        a.predicate.name in ("Contains", "NotContains") for a in rule.premise | rule.conclusion
    )
    assert any(map(geometric, simplified_implications(one.base)))
    assert not any(map(geometric, simplified_implications(two.base)))


_LOCKED = {
    "grid": "solved",
    "cells": ["x", "y"],
    "numbers": ["n"],
    "predicates": [
        "SameRow", "DifferentRows", "SameBlock", "DifferentBlocks",
        "NotContains", "ConfinedToRowInBlock", "ConfinedToBlockInRow",
    ],
}


@pytest.mark.parametrize("block_size", [2, 3])
def test_confinement_is_decided_right(block_size):
    """Counterexamples have the attributes claimed, checked against the
    grid directly, and the pointing rule is found."""
    config = ExplorationConfig.from_dict({**_LOCKED, "block_size": block_size})
    exploration = _checked(config.rule_exploration(), block_size)
    exploration.run()

    x, y, n = config.variables
    pointing = Implication(
        {
            _atom("ConfinedToRowInBlock", y, n),
            _atom("SameRow", x, y),
            _atom("DifferentBlocks", x, y),
        },
        {_atom("NotContains", x, n)},
    )
    assert exploration.base.implications.entails(pointing)


@pytest.mark.parametrize("line", ["Row", "Column"])
def test_pair_confinement_is_decided_right(line):
    """Counterexamples have the attributes claimed, checked against the
    grid directly."""
    config = ExplorationConfig.from_dict({
        "grid": "solved",
        "cells": ["x", "y"],
        "numbers": ["n"],
        "predicates": [f"Same{line}", "NotContains", f"ConfinedToPairIn{line}"],
    })
    _checked(config.rule_exploration()).run()


def test_the_x_wing_holds_on_9x9_grids():
    """In two rows where n can only go in the same two columns, n is excluded
    from the rest of those columns; without one of the premises about the
    columns or rows, or without the second row, it is not."""
    a, b, c, d, e = (SortedVariable(v, SudokuSort.CELL) for v in "abcde")
    n = SortedVariable("n", SudokuSort.NUMBER)
    xwing = [
        _atom("ConfinedToPairInRow", a, b, n), _atom("ConfinedToPairInRow", c, d, n),
        _atom("SameColumn", a, c), _atom("SameColumn", b, d), _atom("DifferentRows", a, c),
        _atom("SameColumn", a, e), _atom("DifferentRows", a, e), _atom("DifferentRows", c, e),
    ]
    conclusion = [_atom("NotContains", e, n)]
    expert = SatSudokuRuleExpert(3, [a, b, c, d, e, n])
    assert expert.validate(Implication(xwing, conclusion)) is None
    for dropped in (
        _atom("DifferentRows", a, c),
        _atom("SameColumn", b, d),
        _atom("ConfinedToPairInRow", c, d, n),
    ):
        premise = [p for p in xwing if p != dropped]
        assert expert.validate(Implication(premise, conclusion)) is not None
