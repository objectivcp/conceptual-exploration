"""Unit tests for the Sudoku exploration domain."""

import pytest

from conceptual_exploration import AttributeExploration, Implication
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku import (
    SudokuExpert,
    SudokuSort,
    Z3SudokuExpert,
    assemble_solution,
    get_coords,
    get_sudoku_attributes,
    get_sudoku_predicates,
    get_sudoku_symmetries,
    get_var,
    print_solution,
    solve_sudoku,
    sudoku2sat,
)


def test_get_var_and_coords():
    n = 4
    for r in range(n):
        for c in range(n):
            for num in range(1, n + 1):
                v = get_var(r, c, num, n)
                assert v >= 1
                r2, c2, num2 = get_coords(v, n)
                assert (r, c, num) == (r2, c2, num2)


def test_sudoku2sat_and_solve_4x4():
    grid = [
        [4, 3, 0, 0],
        [2, 0, 0, 3],
        [0, 4, 3, 0],
        [3, 0, 0, 0],
    ]
    sol = solve_sudoku(grid, k=2)
    assert sol is not None
    assert len(sol) == 4
    assert all(len(row) == 4 for row in sol)

    # Check that initial clues are preserved
    assert sol[0][0] == 4 and sol[0][1] == 3
    assert sol[1][0] == 2 and sol[1][3] == 3

    # Check valid row & column entries
    for row in sol:
        assert set(row) == {1, 2, 3, 4}
    for c in range(4):
        assert set(sol[r][c] for r in range(4)) == {1, 2, 3, 4}


def test_sudoku_unsat():
    # Impossible grid: two identical numbers in same row
    invalid_grid = [
        [4, 4, 0, 0],
        [2, 0, 0, 3],
        [0, 4, 3, 0],
        [3, 0, 0, 0],
    ]
    sol = solve_sudoku(invalid_grid, k=2)
    assert sol is None


def test_sudoku_expert_sat():
    expert = SudokuExpert(block_size=2)

    # In 4x4 Sudoku, if (0,0)=1, (0,1)=2, (0,2)=3, then (0,3) must be 4
    premise = frozenset([(0, 0, 1), (0, 1, 2), (0, 2, 3)])
    conclusion = frozenset([(0, 3, 4)])
    impl = Implication(premise, conclusion)

    # This is valid, so expert returns None (no counterexample)
    cex = expert.validate(impl)
    assert cex is None

    # False implication: (0,0)=1 implies (0,3)=4 (not necessarily true)
    false_impl = Implication(frozenset([(0, 0, 1)]), frozenset([(0, 3, 4)]))
    cex2 = expert.validate(false_impl)
    assert cex2 is not None
    assert (0, 0, 1) in cex2.positive
    assert (0, 3, 4) in cex2.negative


def test_sudoku_symmetries():
    symmetries = get_sudoku_symmetries(block_size=2, include_rotations=True, include_reflections=True)
    assert len(symmetries) > 0

    attr = (0, 1, 2)
    for sym in symmetries:
        mapped = sym(attr)
        assert len(mapped) == 3
        r, c, num = mapped
        assert 0 <= r < 4
        assert 0 <= c < 4
        assert 1 <= num <= 4


def test_z3_sudoku_expert_and_predicates():
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
    ]
    expert = Z3SudokuExpert(block_size=2, variables=variables)
    preds = get_sudoku_predicates(block_size=2, expert=expert)
    pred_map = {p.name: p for p in preds}

    assert "Peers" in pred_map
    assert "Apart" in pred_map
    assert "Same" in pred_map
    assert "Different" in pred_map
    assert "Contains" in pred_map


def test_sudoku_rule_exploration():
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
    ]
    expert = Z3SudokuExpert(block_size=2, variables=variables)
    preds = get_sudoku_predicates(block_size=2, expert=expert)

    # Explore with basic cell relation predicates
    selected = [preds[0], preds[1], preds[2], preds[3]]  # Peers, Apart, Same, Different
    exploration = RuleExploration(
        selected,
        variables,
        expert,
        substitutions=True,
        evaluate_all=True,
    )
    exploration.run()
    base = exploration.base
    assert len(base.accepted_implications) > 0


if __name__ == "__main__":
    test_get_var_and_coords()
    test_sudoku2sat_and_solve_4x4()
    test_sudoku_unsat()
    test_sudoku_expert_sat()
    test_sudoku_symmetries()
    test_z3_sudoku_expert_and_predicates()
    test_sudoku_rule_exploration()
    print("All Sudoku tests passed successfully!")
