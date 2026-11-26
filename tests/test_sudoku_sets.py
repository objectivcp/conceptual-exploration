"""Tests for the exploration of solved grids with sets of cells and digits."""

import random

import pytest

from conceptual_exploration import Implication, simplified_implications
from conceptual_exploration.logic.atom import Atom
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku import (
    ExplorationConfig,
    SatSudokuRuleExpert,
    SudokuSort,
    load_config,
    sudoku_background,
    sudoku_predicates,
    sudoku_solutions,
)

SOLUTIONS = sudoku_solutions(2)


def _units(k):
    n = k * k
    rows = [{(r, c) for c in range(n)} for r in range(n)]
    columns = [{(r, c) for r in range(n)} for c in range(n)]
    blocks = [
        {(r, c) for r in range(br * k, br * k + k) for c in range(bc * k, bc * k + k)}
        for br in range(k) for bc in range(k)
    ]
    return rows + columns + blocks


def _holds(atom, grid, assignment, k=2):
    """Evaluate an atom on a solved grid directly, without the SAT encoding."""
    values = dict(assignment)
    args = [values[v.name] for v in atom.arguments]
    name = atom.predicate.name
    value = lambda cell: grid[cell[0]][cell[1]]
    if name in ("Contains", "NotContains"):
        return (value(args[0]) == args[1]) == (name == "Contains")
    if name in ("CellIn", "NumberIn"):
        return args[0] in args[1]
    if name in ("CellNotIn", "NumberNotIn"):
        return args[0] not in args[1]
    if name == "DigitsWithin":
        cells, digits = args
        return all(value(cell) in digits for cell in cells)
    if name == "DigitsInclude":
        cells, digits = args
        return set(digits) <= {value(cell) for cell in cells}
    if name == "SameSize":
        return len(args[0]) == len(args[1])
    if name == "WithinUnit":
        (cells,) = args
        return any(set(cells) <= unit for unit in _units(k))
    if name == "SharesUnit":
        cells, z = args
        return any(set(cells) | {z} <= unit for unit in _units(k))
    first, second = args
    return {"SameCell": first == second, "DifferentCells": first != second}[name]


def _checked(exploration, k):
    """The exploration, with each counterexample checked against its grid
    directly: it refutes the question and has the attributes claimed."""
    validate = exploration.expert.validate

    def checked(implication, attributes=None):
        counterexample = validate(implication, attributes)
        if counterexample is not None:
            witness = counterexample.object
            values = dict(witness.assignment)
            assert all(values[v.name] for v in exploration.expert.variables), "a set is empty"
            holds = lambda a: _holds(a, witness.grid, witness.assignment, k)
            assert all(map(holds, implication.premise))
            assert not all(map(holds, implication.conclusion))
            assert all(holds(a) == (a in counterexample.positive) for a in attributes)
        return counterexample

    exploration.expert.validate = checked
    return exploration


def _random_value(sort, rng, k=2):
    n = k * k
    if sort is SudokuSort.CELL:
        return rng.randrange(n), rng.randrange(n)
    if sort is SudokuSort.NUMBER:
        return rng.randrange(1, n + 1)
    if sort is SudokuSort.NUMBERSET:
        return tuple(sorted(rng.sample(range(1, n + 1), rng.randrange(1, n + 1))))
    # Sets within a unit matter most, so half of them are drawn from one.
    pool = sorted(rng.choice(_units(k))) if rng.random() < 0.5 else [(r, c) for r in range(n) for c in range(n)]
    return tuple(sorted(rng.sample(pool, rng.randrange(1, n + 1))))


@pytest.mark.parametrize("k", [2, 3])
def test_counterexamples_are_right(k):
    config = load_config("solved-sets").with_overrides(block_size=k)
    _checked(config.rule_exploration(), k).run()


def test_rules_hold_on_random_grids():
    config = load_config("solved-sets")
    exploration = config.rule_exploration()
    exploration.run()
    rng = random.Random(0)
    for _ in range(2000):
        grid = rng.choice(SOLUTIONS)
        assignment = tuple((v.name, _random_value(v.sort, rng)) for v in config.variables)
        holds = lambda a: _holds(a, grid, assignment)
        for implication in exploration.base.accepted_implications:
            if all(map(holds, implication.premise)):
                assert all(map(holds, implication.conclusion)), str(implication)


@pytest.mark.parametrize("k", [2, 3])
def test_background_holds(k):
    config = load_config("solved-sets")
    predicates = sudoku_predicates(config.predicates + ("Peers", "SameNumber", "DifferentNumbers"))
    variables = config.variables + [SortedVariable("m", SudokuSort.NUMBER)]
    expert = SatSudokuRuleExpert(k, variables)
    background = sudoku_background(predicates, variables)
    assert background
    for implication in background:
        assert expert.validate(implication) is None, str(implication)


def _atom(name, *args):
    (predicate,) = sudoku_predicates([name])
    return Atom(predicate, args).normalize()


def test_naked_and_hidden_subsets_follow_on_9x9_grids():
    """Of any size: the naked subset by DigitsWithin -> DigitsInclude and
    elimination over the set, the hidden subset by DigitsInclude ->
    DigitsWithin and the definition of DigitsWithin."""
    config = load_config("solved-sets").with_overrides(block_size=3)
    exploration = config.rule_exploration()
    exploration.run()
    x, z, n, cells, digits = config.variables
    naked = Implication(
        {
            _atom("DigitsWithin", cells, digits), _atom("SameSize", cells, digits),
            _atom("SharesUnit", cells, z), _atom("CellNotIn", z, cells), _atom("NumberIn", n, digits),
        },
        {_atom("NotContains", z, n)},
    )
    hidden = Implication(
        {
            _atom("DigitsInclude", cells, digits), _atom("SameSize", cells, digits),
            _atom("CellIn", x, cells), _atom("NumberNotIn", n, digits),
        },
        {_atom("NotContains", x, n)},
    )
    assert exploration.base.implications.entails(naked)
    assert exploration.base.implications.entails(hidden)
    # Neither holds without the sizes.
    for subset in (naked, hidden):
        weaker = Implication(subset.premise - {_atom("SameSize", cells, digits)}, subset.conclusion)
        assert not exploration.base.implications.entails(weaker)


def test_the_rules_are_the_same_on_4x4_and_9x9_grids():
    rules = []
    for k in (2, 3):
        exploration = load_config("solved-sets").with_overrides(block_size=k).rule_exploration()
        exploration.run()
        rules.append(sorted(map(str, simplified_implications(exploration.base))))
    assert rules[0] == rules[1]


@pytest.mark.parametrize("settings, message", [
    ({"cells": ["x"], "cell_sets": ["C"], "predicates": ["CellIn"], "expert": "z3"}, "no Z3 encoding"),
    ({"cells": ["x"], "predicates": ["CellIn"]}, "needs a cell set variable"),
    ({"cells": ["x"], "numbers": ["n"], "cell_sets": ["C"], "predicates": ["DigitsWithin"]}, "needs a number set variable"),
    ({"cells": ["C"], "cell_sets": ["C"], "predicates": ["CellIn"]}, "distinct"),
    ({"grid": "partial", "cells": ["x"], "cell_sets": ["C"], "predicates": ["CellIn"]}, "do not apply to partial grids"),
])
def test_set_settings_that_cannot_run_say_why(settings, message):
    with pytest.raises(ValueError, match=message):
        ExplorationConfig.from_dict({"grid": "solved", **settings})
