"""Unit tests for the Sudoku exploration domain."""

import pytest

from conceptual_exploration import AttributeExploration, Implication, reduced_basis
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.variable import SortedVariable
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.logic.atom import Atom, atoms_over
from explorations.sudoku import (
    CELL_EQUIVALENCES,
    PREDICATE_PROPERTIES,
    PREDICATE_SORTS,
    PRIMITIVE_PREDICATES,
    SatSudokuRuleExpert,
    SudokuExpert,
    SudokuRuleWitness,
    SudokuSort,
    Z3SudokuExpert,
    assemble_solution,
    check_rules,
    get_coords,
    get_sudoku_attributes,
    get_sudoku_predicates,
    get_sudoku_symmetries,
    get_var,
    print_solution,
    select_predicates,
    solve_sudoku,
    sudoku2sat,
    sudoku_background,
    sudoku_predicates,
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


@pytest.mark.parametrize("block_size", [2, 3])
def test_background_holds_in_every_grid(block_size):
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
        SortedVariable("m", SudokuSort.NUMBER),
    ]
    expert = Z3SudokuExpert(block_size=block_size, variables=variables)
    predicates = select_predicates(
        get_sudoku_predicates(block_size=block_size, expert=expert),
        PRIMITIVE_PREDICATES,
    )
    atoms = atoms_over(predicates, variables)

    background = sudoku_background(predicates, variables)
    assert background
    for implication in background:
        assert expert.validate(implication, atoms) is None, str(implication)


@pytest.mark.parametrize("block_size", [2, 3])
def test_primitive_exploration_finds_the_sudoku_rules(block_size):
    """Given what holds in any grid, what is left are the rules themselves:
    two cells holding the same digit in a row, column or block coincide."""
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
    ]
    expert = SatSudokuRuleExpert(block_size=block_size, variables=variables)
    predicates = sudoku_predicates(CELL_EQUIVALENCES)
    exploration = RuleExploration(
        predicates,
        variables,
        expert,
        background=sudoku_background(predicates, variables),
        substitutions=True,
        evaluate_all=True,
    )
    exploration.run()
    base = exploration.base

    assert sorted(str(rule) for rule in reduced_basis(base)) == [
        "Same(x, y), SameBlock(x, y) -> SameCell(x, y)",
        "Same(x, y), SameColumn(x, y) -> SameCell(x, y)",
        "Same(x, y), SameRow(x, y) -> SameCell(x, y)",
    ]


def _declaration(p):
    return (p.name, p.sorts, p.symmetric, p.reflexive, p.irreflexive, p.complement)


def test_plain_predicates_match_the_z3_predicates():
    variables = [SortedVariable("x", SudokuSort.CELL)]
    expert = Z3SudokuExpert(block_size=2, variables=variables)
    z3_predicates = get_sudoku_predicates(block_size=2, expert=expert)
    z3_names = {p.name for p in z3_predicates}
    # Forced and Excluded quantify over a partial grid's completions, which
    # only the partial-grid expert evaluates.
    assert set(PREDICATE_SORTS) - z3_names == {"Forced", "Excluded"}
    assert sorted(map(_declaration, z3_predicates)) == sorted(
        map(_declaration, sudoku_predicates(z3_names))
    )


@pytest.mark.parametrize("block_size", [2, 3])
def test_declared_properties_hold_on_a_solved_grid(block_size):
    """Check the properties against a grid directly, not through an expert."""
    n = block_size**2
    grid = solve_sudoku([[0] * n for _ in range(n)], k=block_size)
    cells = [(r, c) for r in range(n) for c in range(n)]
    numbers = range(1, n + 1)
    witness = lambda first, second: SudokuRuleWitness((("u", first), ("v", second)), grid)
    u = {sort: SortedVariable("u", sort) for sort in SudokuSort}
    v = {sort: SortedVariable("v", sort) for sort in SudokuSort}
    predicates = {p.name: p for p in sudoku_predicates(PREDICATE_SORTS)}

    for name, properties in PREDICATE_PROPERTIES.items():
        p = predicates[name]
        if not properties:
            continue
        domain = cells if p.sorts[0] is SudokuSort.CELL else numbers
        sort = p.sorts[0]
        holds = lambda q, a, b: _holds(Atom(q, (u[sort], v[sort])), witness(a, b), block_size)
        for a in domain:
            if p.reflexive:
                assert holds(p, a, a), name
            if p.irreflexive:
                assert not holds(p, a, a), name
            for b in domain:
                if p.symmetric:
                    assert holds(p, a, b) == holds(p, b, a), name
                if p.complement:
                    assert holds(p, a, b) != holds(predicates[p.complement], a, b), name


def test_sat_rule_expert_agrees_with_z3():
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
    ]
    theories = []
    for make_expert in (
        lambda z3_expert: z3_expert,
        lambda z3_expert: SatSudokuRuleExpert(block_size=2, variables=variables),
    ):
        z3_expert = Z3SudokuExpert(block_size=2, variables=variables)
        predicates = get_sudoku_predicates(block_size=2, expert=z3_expert)
        exploration = RuleExploration(
            predicates,
            variables,
            make_expert(z3_expert),
            substitutions=True,
            evaluate_all=True,
        )
        exploration.run()
        theories.append({str(i) for i in exploration.base.implications})

    assert theories[0] == theories[1]


def _holds(atom, witness, block_size):
    """Evaluate an atom on a witness directly, without the SAT encoding."""
    k = block_size
    values = dict(witness.assignment)
    args = [values[v.name] for v in atom.arguments]
    value = lambda cell: witness.grid[cell[0]][cell[1]]
    name = atom.predicate.name
    if name == "Contains":
        return value(args[0]) == args[1]
    if name == "SameNumber":
        return args[0] == args[1]
    if name == "DifferentNumbers":
        return args[0] != args[1]
    (r1, c1), (r2, c2) = args
    together = r1 == r2 or c1 == c2 or (r1 // k, c1 // k) == (r2 // k, c2 // k)
    return {
        "Peers": together and (r1, c1) != (r2, c2),
        "Apart": not together,
        "Different": value(args[0]) != value(args[1]),
        "Same": value(args[0]) == value(args[1]),
        "SameCell": (r1, c1) == (r2, c2),
        "DifferentCells": (r1, c1) != (r2, c2),
        "SameRow": r1 == r2,
        "SameColumn": c1 == c2,
        "SameBand": r1 // k == r2 // k,
        "SameStack": c1 // k == c2 // k,
        "SameBlock": (r1 // k, c1 // k) == (r2 // k, c2 // k),
    }[name]


def test_rules_are_checked_on_9x9_grids():
    w, x, y, z = (SortedVariable(v, SudokuSort.CELL) for v in "wxyz")
    expert = Z3SudokuExpert(block_size=2, variables=[w, x, y, z])
    p = {pred.name: pred for pred in get_sudoku_predicates(block_size=2, expert=expert)}
    atom = lambda name, *args: Atom(p[name], args)

    sudoku_rule = Implication(
        {atom("Same", x, y), atom("SameBlock", x, y)},
        {atom("SameCell", x, y)},
    )
    # Two digit pairs in two blocks: in 4x4 a block has only two columns, so
    # this is forced there and nowhere else.
    small_grid_rule = Implication(
        {
            atom("Same", y, w), atom("Same", z, x), atom("SameBlock", x, w),
            atom("SameBlock", z, y), atom("SameColumn", z, w),
        },
        {atom("SameColumn", x, y)},
    )
    assert SatSudokuRuleExpert(block_size=2, variables=[w, x, y, z]).validate(small_grid_rule) is None

    results = dict(check_rules([sudoku_rule, small_grid_rule], 3, [w, x, y, z]))
    assert results[sudoku_rule] is None

    witness = results[small_grid_rule].object
    digits = set(range(1, 10))
    grid = witness.grid
    assert all(set(row) == digits for row in grid)
    assert all({row[c] for row in grid} == digits for c in range(9))
    assert all(
        {grid[r][c] for r in range(br, br + 3) for c in range(bc, bc + 3)} == digits
        for br in (0, 3, 6)
        for bc in (0, 3, 6)
    )
    assert all(_holds(a, witness, 3) for a in small_grid_rule.premise)
    assert not all(_holds(a, witness, 3) for a in small_grid_rule.conclusion)


if __name__ == "__main__":
    test_get_var_and_coords()
    test_sudoku2sat_and_solve_4x4()
    test_sudoku_unsat()
    test_sudoku_expert_sat()
    test_sudoku_symmetries()
    test_z3_sudoku_expert_and_predicates()
    test_sudoku_rule_exploration()
    for block_size in (2, 3):
        test_background_holds_in_every_grid(block_size)
    for block_size in (2, 3):
        test_primitive_exploration_finds_the_sudoku_rules(block_size)
    test_plain_predicates_match_the_z3_predicates()
    for block_size in (2, 3):
        test_declared_properties_hold_on_a_solved_grid(block_size)
    test_sat_rule_expert_agrees_with_z3()
    test_rules_are_checked_on_9x9_grids()
    print("All Sudoku tests passed successfully!")
