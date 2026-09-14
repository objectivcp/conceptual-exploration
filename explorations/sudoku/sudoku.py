"""Sudoku exploration domain models, experts, predicates, and symmetries.

Provides SAT-based (PySAT) and SMT-based (Z3) representations of Sudoku puzzles,
automated counterexample search, symmetry transformations, and first-order
relational predicates for conceptual exploration.
"""

from __future__ import annotations

from enum import auto
from itertools import combinations, permutations
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple

import z3
from pysat.formula import CNF
from pysat.solvers import Solver

from conceptual_exploration import AttributeExploration, Implication
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.predicate import EvaluatablePredicate
from conceptual_exploration.logic.variable import Sort, SortedVariable


# ---------------------------------------------------------------------------
# 1. SAT-based Sudoku Representation & Solving (PySAT)
# ---------------------------------------------------------------------------

def get_var(r: int, c: int, num: int, n: int) -> int:
    """Map (row, column, number) to a unique positive 1-based variable index."""
    return r * n**2 + c * n + num


def get_coords(var_index: int, n: int) -> Tuple[int, int, int]:
    """Map a 1-based variable index back to (row, column, number)."""
    num = (var_index - 1) % n + 1
    c = ((var_index - 1) // n) % n
    r = (var_index - 1) // (n**2)
    return r, c, num


def sudoku2sat(grid: List[List[int]], k: int) -> CNF:
    """Reduce a Sudoku puzzle to a SAT CNF formula.

    Args:
        grid: A square matrix of size k² × k² with 0 representing empty cells.
        k: Block size (e.g. 2 for 4x4 Sudoku, 3 for 9x9 Sudoku).

    Returns:
        A CNF formula that is satisfiable if and only if
        the unspecified entries can be filled in to form a valid Sudoku solution.
    """
    n = len(grid)
    if n != k**2 or any(len(row) != n for row in grid):
        raise ValueError(f"Invalid Sudoku grid dimensions: expected {k**2}x{k**2}")

    f = CNF()

    def var(r: int, c: int, num: int) -> int:
        return get_var(r, c, num, n)

    # Initial grid clues
    for r in range(n):
        for c in range(n):
            if 1 <= grid[r][c] <= n:
                f.append([var(r, c, grid[r][c])])

    # Cell constraint: each cell must contain exactly one number
    for r in range(n):
        for c in range(n):
            # At least one number
            f.append([var(r, c, num) for num in range(1, n + 1)])
            # At most one number
            for num1 in range(1, n + 1):
                for num2 in range(num1 + 1, n + 1):
                    f.append([-var(r, c, num1), -var(r, c, num2)])

    # Row constraint: each row must contain each number exactly once
    for r in range(n):
        for num in range(1, n + 1):
            f.append([var(r, c, num) for c in range(n)])
            for c1 in range(n):
                for c2 in range(c1 + 1, n):
                    f.append([-var(r, c1, num), -var(r, c2, num)])

    # Column constraint: each column must contain each number exactly once
    for c in range(n):
        for num in range(1, n + 1):
            f.append([var(r, c, num) for r in range(n)])
            for r1 in range(n):
                for r2 in range(r1 + 1, n):
                    f.append([-var(r1, c, num), -var(r2, c, num)])

    # Block constraint: each k x k block must contain each number exactly once
    for br in range(k):
        for bc in range(k):
            cells = [
                (r, c)
                for r in range(br * k, (br + 1) * k)
                for c in range(bc * k, (bc + 1) * k)
            ]
            for num in range(1, n + 1):
                f.append([var(r, c, num) for (r, c) in cells])
                for i in range(len(cells)):
                    for j in range(i + 1, len(cells)):
                        r1, c1 = cells[i]
                        r2, c2 = cells[j]
                        f.append([-var(r1, c1, num), -var(r2, c2, num)])

    return f


def assemble_solution(model: Optional[List[int]], k: int) -> Optional[List[List[int]]]:
    """Extract a Sudoku solution grid from a satisfying SAT assignment."""
    if model is None:
        return None

    n = k**2
    grid = [[0] * n for _ in range(n)]
    for v in model:
        if v > 0:
            r, c, num = get_coords(v, n)
            grid[r][c] = num
    return grid


def solve_sudoku(
    grid: List[List[int]],
    k: int,
    solver_name: str = "g3",
) -> Optional[List[List[int]]]:
    """Solve a Sudoku puzzle using a SAT solver."""
    f = sudoku2sat(grid, k)
    with Solver(name=solver_name, bootstrap_with=f.clauses) as s:
        if s.solve():
            return assemble_solution(s.get_model(), k)
    return None


def print_solution(grid: Optional[List[List[int]]]) -> None:
    """Pretty-print a solved Sudoku grid."""
    if grid is None:
        print("No solution found")
        return
    for row in grid:
        print(" ".join(str(cell) for cell in row))


# ---------------------------------------------------------------------------
# 2. SAT-based Sudoku Expert for Attribute Exploration
# ---------------------------------------------------------------------------

class SudokuExpert(Expert):
    """SAT-based Expert for propositional Sudoku attribute exploration."""

    def __init__(self, block_size: int, solver_name: str = "g3"):
        self.block_size = block_size
        self.grid_size = block_size**2
        self.solver_name = solver_name

    def validate(
        self,
        implication: Implication,
        attributes: Optional[Iterable[Tuple[int, int, int]]] = None,
    ) -> Optional[PartialObject]:
        n = self.grid_size
        grid = [[0] * n for _ in range(n)]

        # Check for immediate contradiction in premise (multiple digits in same cell)
        for (r, c, num) in implication.premise:
            if grid[r][c] == 0:
                grid[r][c] = num
            else:
                return None

        f = sudoku2sat(grid, self.block_size)
        f.append([-get_var(r, c, num, n) for (r, c, num) in implication.conclusion])

        with Solver(name=self.solver_name, bootstrap_with=f.clauses) as s:
            if s.solve():
                model = s.get_model()
                if model:
                    return PartialObject(
                        str(implication),
                        set(get_coords(a, n) for a in model if a > 0),
                        set(get_coords(abs(a), n) for a in model if a < 0),
                    )
        return None


# ---------------------------------------------------------------------------
# 3. Sudoku Background Knowledge & Symmetries
# ---------------------------------------------------------------------------

def get_sudoku_attributes(block_size: int) -> List[Tuple[int, int, int]]:
    """Return all propositional attributes (r, c, num) for a k x k block Sudoku."""
    n = block_size**2
    return [
        (r, c, num)
        for r in range(n)
        for c in range(n)
        for num in range(1, n + 1)
    ]


def row_cells(r: int, c: int, n: int) -> List[Tuple[int, int]]:
    return [(r, y) for y in range(n) if y != c]


def column_cells(r: int, c: int, n: int) -> List[Tuple[int, int]]:
    return [(x, c) for x in range(n) if x != r]


def block_cells(r: int, c: int, k: int) -> List[Tuple[int, int]]:
    return [
        (x, y)
        for x in range((r // k) * k, (r // k + 1) * k)
        for y in range((c // k) * k, (c // k + 1) * k)
        if x != r or y != c
    ]


def _n_1_implications(
    cells: List[Tuple[int, int]],
    r: int,
    c: int,
    num: int,
    numbers: List[int],
) -> Iterable[Implication]:
    for p in permutations(cells):
        premise = frozenset(
            (r1, c1, num1)
            for (r1, c1), num1 in zip(p, numbers)
        )
        yield Implication(premise, frozenset([(r, c, num)]))


def get_sudoku_background_implications(block_size: int) -> List[Implication]:
    """Generate canonical background implications for Sudoku rules."""
    k = block_size
    n = k**2
    attributes = get_sudoku_attributes(block_size)
    all_attrs_set = frozenset(attributes)

    background: List[Implication] = [
        Implication(frozenset([(r1, c1, n1), (r2, c2, n2)]), all_attrs_set)
        for ((r1, c1, n1), (r2, c2, n2)) in combinations(attributes, 2)
        if (r1 == r2 and c1 == c2)  # at most one digit per cell
        or (
            n1 == n2  # digits within row / col / block differ
            and (r1 == r2 or c1 == c2 or (r1 // k == r2 // k and c1 // k == c2 // k))
        )
    ]

    for (r, c, num) in attributes:
        numbers = [m for m in range(1, n + 1) if m != num]
        for impl in _n_1_implications(row_cells(r, c, n), r, c, num, numbers):
            background.append(impl)
        for impl in _n_1_implications(column_cells(r, c, n), r, c, num, numbers):
            background.append(impl)
        for impl in _n_1_implications(block_cells(r, c, k), r, c, num, numbers):
            background.append(impl)

    return background


def make_number_mapping(permutation: Tuple[int, ...]) -> Callable[[Tuple[int, int, int]], Tuple[int, int, int]]:
    """Create a symmetry mapping for a digit permutation."""
    return lambda r_c_num: (
        r_c_num[0],
        r_c_num[1],
        permutation[r_c_num[2] - 1],
    )


def get_sudoku_symmetries(
    block_size: int,
    include_rotations: bool = True,
    include_reflections: bool = True,
) -> List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]]:
    """Generate symmetry transformations (digit permutations, rotations, reflections)."""
    n = block_size**2
    numbers = tuple(range(1, n + 1))

    number_mappings = [
        make_number_mapping(perm)
        for perm in permutations(numbers)
        if perm != numbers
    ]

    mappings: List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]] = list(number_mappings)

    if include_rotations:
        rotations: List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]] = [
            lambda t, n=n: (t[1], n - 1 - t[0], t[2]),
            lambda t, n=n: (n - 1 - t[0], n - 1 - t[1], t[2]),
            lambda t, n=n: (n - 1 - t[1], t[0], t[2]),
        ]
        mappings.extend(rotations)

    if include_reflections:
        reflections: List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]] = [
            lambda t, n=n: (n - 1 - t[0], t[1], t[2]),
            lambda t, n=n: (t[0], n - 1 - t[1], t[2]),
        ]
        mappings.extend(reflections)

    return mappings


# ---------------------------------------------------------------------------
# 4. Z3 First-Order Relational Sudoku Domain & Expert
# ---------------------------------------------------------------------------

class SudokuSort(Sort):
    """Sorts for multi-sorted first-order Sudoku variables."""
    CELL = auto()
    NUMBER = auto()


def z3_variables(variables: Iterable[SortedVariable]) -> Dict[SortedVariable, Any]:
    """Map SortedVariables to corresponding Z3 AST variables."""
    return {
        v: (z3.Int(f"{v.name}.row"), z3.Int(f"{v.name}.col"))
        if v.sort is SudokuSort.CELL
        else z3.Int(v.name)
        for v in variables
    }


class Z3SudokuExpert(Expert):
    """Z3 SMT-based expert for validating first-order Sudoku rules."""

    def __init__(self, block_size: int, variables: List[SortedVariable]):
        self.block_size = block_size
        self.grid_size = block_size**2
        self.value = z3.Function(
            "value",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort(),
        )
        self.zvars = z3_variables(variables)

        self.solver = z3.Solver()
        self.solver.add(*self._domain_constraints(self.zvars))
        self.solver.add(*self._sudoku_axioms())

    def validate(
        self,
        implication: Implication,
        attributes: Optional[Iterable[Any]] = None,
    ) -> Optional[PartialObject]:
        assert attributes is not None, "Attributes must be provided for Z3 rule validation"

        if self.solver.check([
            self._compile(implication.premise),
            z3.Not(self._compile(implication.conclusion)),
        ]) == z3.unsat:
            return None

        model = self.solver.model()
        assignment = self._eval(model)
        positive, negative = set(), set()
        for a in attributes:
            if model.evaluate(a(self.zvars).holds()):
                positive.add(a)
            else:
                negative.add(a)

        return PartialObject(model, positive, negative)

    def _domain_constraints(self, zvars: Dict[SortedVariable, Any]) -> List[z3.BoolRef]:
        constraints = []
        for v in zvars.values():
            if isinstance(v, tuple):
                row, col = v
                constraints.extend([
                    row >= 0,
                    row < self.grid_size,
                    col >= 0,
                    col < self.grid_size,
                ])
            else:
                constraints.append(1 <= v)
                constraints.append(v <= self.grid_size)
        return constraints

    def _sudoku_axioms(self) -> List[z3.BoolRef]:
        axioms = []

        # Number range
        for r in range(self.grid_size):
            for c in range(self.grid_size):
                axioms.append(
                    z3.And(
                        self.value(r, c) >= 1,
                        self.value(r, c) <= self.grid_size,
                    )
                )

        # Rows
        for r in range(self.grid_size):
            axioms.append(
                z3.Distinct(*[self.value(r, c) for c in range(self.grid_size)])
            )

        # Columns
        for c in range(self.grid_size):
            axioms.append(
                z3.Distinct(*[self.value(r, c) for r in range(self.grid_size)])
            )

        # Blocks
        for br in range(self.block_size):
            for bc in range(self.block_size):
                block = []
                for r in range(br * self.block_size, (br + 1) * self.block_size):
                    for c in range(bc * self.block_size, (bc + 1) * self.block_size):
                        block.append(self.value(r, c))
                axioms.append(z3.Distinct(*block))

        return axioms

    def _compile(self, atoms: Iterable[Any]) -> z3.BoolRef:
        return z3.And(*[a(self.zvars).holds() for a in atoms])

    def _eval(self, model: z3.ModelRef) -> Dict[SortedVariable, Any]:
        return {
            v: (
                model.eval(zv[0], model_completion=True).as_long(),
                model.eval(zv[1], model_completion=True).as_long(),
            )
            if v.sort is SudokuSort.CELL
            else model.eval(zv, model_completion=True).as_long()
            for v, zv in self.zvars.items()
        }


# ---------------------------------------------------------------------------
# 5. First-Order Sudoku Predicates
# ---------------------------------------------------------------------------

def z3_same_block_coords(i: Any, j: Any, block_size: int) -> z3.BoolRef:
    return i / block_size == j / block_size


def z3_same_block(x: Tuple[Any, Any], y: Tuple[Any, Any], block_size: int) -> z3.BoolRef:
    return z3.And(*(z3_same_block_coords(x[i], y[i], block_size) for i in range(2)))


def z3_together(x: Tuple[Any, Any], y: Tuple[Any, Any], block_size: int) -> z3.BoolRef:
    return z3.Or(
        x[0] == y[0],
        x[1] == y[1],
        z3_same_block(x, y, block_size),
    )


def z3predicates(block_size: int, expert: Z3SudokuExpert) -> List[EvaluatablePredicate]:
    """Return standard first-order Sudoku evaluatable predicates."""
    return [
        EvaluatablePredicate(
            "Peers",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.And(
                z3.Or(x[0] != y[0], x[1] != y[1]),
                z3_together(x, y, block_size),
            ),
        ),
        EvaluatablePredicate(
            "Apart",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.Not(z3_together(x, y, block_size)),
        ),
        EvaluatablePredicate(
            "Same",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: expert.value(x[0], x[1]) == expert.value(y[0], y[1]),
        ),
        EvaluatablePredicate(
            "Different",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: expert.value(x[0], x[1]) != expert.value(y[0], y[1]),
        ),
        EvaluatablePredicate(
            "Contains",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.NUMBER),
            function=lambda c, n: expert.value(c[0], c[1]) == n,
        ),
        EvaluatablePredicate(
            "SameNumber",
            2,
            sorts=(SudokuSort.NUMBER, SudokuSort.NUMBER),
            function=lambda m, n: m == n,
        ),
        EvaluatablePredicate(
            "DifferentNumbers",
            2,
            sorts=(SudokuSort.NUMBER, SudokuSort.NUMBER),
            function=lambda m, n: m != n,
        ),
        EvaluatablePredicate(
            "SameBlock",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3_same_block(x, y, block_size),
        ),
        EvaluatablePredicate(
            "SameRow",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[0] == y[0],
        ),
        EvaluatablePredicate(
            "SameColumn",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[1] == y[1],
        ),
    ]


get_sudoku_predicates = z3predicates


# ---------------------------------------------------------------------------
# 6. Exploration Runner Helpers
# ---------------------------------------------------------------------------

def cell_exploration(block_size: int = 2) -> ExplorationBase:
    """Run relational rule exploration over cell variables (x, y, z, w)."""
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("w", SudokuSort.CELL),
    ]
    expert = Z3SudokuExpert(block_size, variables)
    exploration = RuleExploration(
        z3predicates(block_size, expert)[:4],
        variables,
        expert,
        substitutions=True,
        evaluate_all=True,
    )
    exploration.run()
    return exploration.base


def cell_number_exploration(block_size: int = 2) -> ExplorationBase:
    """Run relational rule exploration over cell and number variables."""
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
        SortedVariable("m", SudokuSort.NUMBER),
    ]
    expert = Z3SudokuExpert(block_size, variables)
    predicates = z3predicates(block_size, expert)
    selected_predicates = (
        predicates[0],  # Peers
        predicates[1],  # Apart
        predicates[2],  # Same
        predicates[3],  # Different
        predicates[4],  # Contains
        predicates[5],  # SameNumber
        predicates[6],  # DifferentNumbers
        predicates[8],  # SameRow
        predicates[9],  # SameColumn
    )
    exploration = RuleExploration(
        selected_predicates,
        variables,
        expert,
        substitutions=True,
        evaluate_all=True,
    )
    exploration.run()
    return exploration.base


run_sudoku_rule_exploration = cell_number_exploration


def run_sudoku_sat_exploration(
    block_size: int = 2,
    use_symmetries: bool = True,
) -> Tuple[Any, ExplorationBase]:
    """Run propositional attribute exploration using SAT expert and symmetries."""
    attributes = get_sudoku_attributes(block_size)
    mappings = get_sudoku_symmetries(block_size) if use_symmetries else []

    base = ExplorationBase(
        attributes=attributes,
        mappings=mappings,
    )
    expert = SudokuExpert(block_size)
    exploration = AttributeExploration(base, expert)
    state = exploration.run()
    return state, base
