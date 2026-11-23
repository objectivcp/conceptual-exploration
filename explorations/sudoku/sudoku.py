"""Sudoku exploration domain models, experts, predicates, and symmetries.

Provides SAT-based (PySAT) and SMT-based (Z3) representations of Sudoku puzzles,
automated counterexample search, symmetry transformations, and first-order
relational predicates for conceptual exploration.
"""

from __future__ import annotations

from dataclasses import replace
from enum import auto
from itertools import combinations, permutations, product
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple

import z3
from pysat.formula import CNF
from pysat.solvers import Solver

from conceptual_exploration import AttributeExploration, Implication, classically_irredundant, report_every
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.atom import Atom, atoms_over
from conceptual_exploration.logic.predicate import EvaluatablePredicate, Predicate
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
    """The rules of Sudoku as implications between cell assignments.

    Two digits in one cell, or one digit twice in a row, column or block,
    imply every attribute: no grid has them. And when the other cells of a
    unit hold the other digits, the remaining cell holds the remaining digit.
    There are (n - 1)! such premises per cell, digit and unit for n = k * k,
    which is practical for 4x4 grids but not for 9x9 ones.
    """
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


def _line_permutations(block_size: int) -> List[Tuple[int, ...]]:
    """Permutations of the rows (or columns) that keep the bands (or stacks)
    together: the bands are permuted, and the lines within each band."""
    k = block_size
    return [
        tuple(band_order[line // k] * k + inner[line // k][line % k] for line in range(k * k))
        for band_order in permutations(range(k))
        for inner in product(permutations(range(k)), repeat=k)
    ]


def get_sudoku_symmetries(
    block_size: int,
    include_digit_permutations: bool = True,
    include_geometry: bool = True,
) -> List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]]:
    """Every symmetry of the Sudoku grids but the identity, as maps of the
    attributes (row, column, digit).

    The geometric symmetries permute the bands and the rows within each
    band, and likewise the stacks and columns, and may transpose the grid;
    rotations and reflections are among them. `ExplorationBase` maps each
    implication and counterexample once by each mapping, without composing
    them, so the mappings must form a group rather than generate one. For 4x4
    grids it has 8 * 8 * 2 * 24 = 3072 elements; for 9x9 grids about 1.2e12,
    which is too many, so only block size 2 is supported.
    """
    if block_size != 2:
        raise ValueError(
            "The symmetry group of Sudoku grids with block size "
            f"{block_size} is too large to list; only block size 2 is supported"
        )
    n = block_size**2
    identity = tuple(range(n))
    lines = _line_permutations(block_size) if include_geometry else [identity]
    transpositions = (False, True) if include_geometry else (False,)
    digits = (
        list(permutations(range(1, n + 1)))
        if include_digit_permutations
        else [tuple(range(1, n + 1))]
    )

    mappings: List[Callable[[Tuple[int, int, int]], Tuple[int, int, int]]] = []
    for rows, columns, transpose, digit in product(lines, lines, transpositions, digits):
        if rows == columns == identity and not transpose and digit == tuple(range(1, n + 1)):
            continue
        if transpose:
            mappings.append(
                lambda t, rows=rows, columns=columns, digit=digit:
                    (columns[t[1]], rows[t[0]], digit[t[2] - 1])
            )
        else:
            mappings.append(
                lambda t, rows=rows, columns=columns, digit=digit:
                    (rows[t[0]], columns[t[1]], digit[t[2] - 1])
            )
    return mappings


# ---------------------------------------------------------------------------
# 4. Z3 First-Order Relational Sudoku Domain & Expert
# ---------------------------------------------------------------------------

class SudokuSort(Sort):
    """Sorts for multi-sorted first-order Sudoku variables: cells, numbers,
    and non-empty sets of each."""
    CELL = auto()
    NUMBER = auto()
    CELLSET = auto()
    NUMBERSET = auto()


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
    """Return standard first-order Sudoku evaluatable predicates, with the
    properties `PREDICATE_PROPERTIES` declares for them."""
    predicates = [
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
            "NotContains",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.NUMBER),
            function=lambda c, n: expert.value(c[0], c[1]) != n,
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
        EvaluatablePredicate(
            "SameCell",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.And(x[0] == y[0], x[1] == y[1]),
        ),
        EvaluatablePredicate(
            "DifferentCells",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.Or(x[0] != y[0], x[1] != y[1]),
        ),
        EvaluatablePredicate(
            "DifferentRows",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[0] != y[0],
        ),
        EvaluatablePredicate(
            "DifferentColumns",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[1] != y[1],
        ),
        EvaluatablePredicate(
            "DifferentBlocks",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.Not(z3_same_block(x, y, block_size)),
        ),
        EvaluatablePredicate(
            "SameBand",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3_same_block_coords(x[0], y[0], block_size),
        ),
        EvaluatablePredicate(
            "SameStack",
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3_same_block_coords(x[1], y[1], block_size),
        ),
    ]
    return [replace(p, **PREDICATE_PROPERTIES[p.name]) for p in predicates]


get_sudoku_predicates = z3predicates


# Equivalence relations on cells: the five from the grid's geometry and
# `Same`, equality of the values the cells hold.
CELL_EQUIVALENCES = (
    "SameCell",
    "SameRow",
    "SameColumn",
    "SameBlock",
    "SameBand",
    "SameStack",
    "Same",
)

# The vocabulary the rule explorations use by default. `Peers`, `Apart`,
# `Different` and `DifferentNumbers` are left out: each is a negation or a
# disjunction of these, which Horn rules cannot define, so exploring them
# mostly rediscovers how they relate to the primitives.
PRIMITIVE_PREDICATES = CELL_EQUIVALENCES + ("Contains", "SameNumber")


def select_predicates(
    predicates: Iterable[EvaluatablePredicate],
    names: Iterable[str],
) -> List[EvaluatablePredicate]:
    """Pick predicates by name, in the order the names are given."""
    by_name = {p.name: p for p in predicates}
    return [by_name[name] for name in names]


_CELL_PAIR = (SudokuSort.CELL, SudokuSort.CELL)
_NUMBER_PAIR = (SudokuSort.NUMBER, SudokuSort.NUMBER)

# The sorts of each predicate's arguments, as `z3predicates` declares them.
PREDICATE_SORTS: Dict[str, Tuple[Sort, ...]] = {
    "Peers": _CELL_PAIR,
    "Apart": _CELL_PAIR,
    "Same": _CELL_PAIR,
    "Different": _CELL_PAIR,
    "Contains": (SudokuSort.CELL, SudokuSort.NUMBER),
    "NotContains": (SudokuSort.CELL, SudokuSort.NUMBER),
    "SameNumber": _NUMBER_PAIR,
    "DifferentNumbers": _NUMBER_PAIR,
    "SameBlock": _CELL_PAIR,
    "SameRow": _CELL_PAIR,
    "SameColumn": _CELL_PAIR,
    "SameCell": _CELL_PAIR,
    "DifferentCells": _CELL_PAIR,
    "DifferentRows": _CELL_PAIR,
    "DifferentColumns": _CELL_PAIR,
    "DifferentBlocks": _CELL_PAIR,
    "SameBand": _CELL_PAIR,
    "SameStack": _CELL_PAIR,
    # Where a digit lies relative to a cell, which only `SatSudokuRuleExpert`
    # evaluates; see `CONFINEMENT_PREDICATES`.
    "ConfinedToRowInBlock": (SudokuSort.CELL, SudokuSort.NUMBER),
    "ConfinedToColumnInBlock": (SudokuSort.CELL, SudokuSort.NUMBER),
    "ConfinedToBlockInRow": (SudokuSort.CELL, SudokuSort.NUMBER),
    "ConfinedToBlockInColumn": (SudokuSort.CELL, SudokuSort.NUMBER),
    "ConfinedToPairInRow": (SudokuSort.CELL, SudokuSort.CELL, SudokuSort.NUMBER),
    "ConfinedToPairInColumn": (SudokuSort.CELL, SudokuSort.CELL, SudokuSort.NUMBER),
    # Predicates of partial grids, which only `PartialGridExpert` evaluates;
    # see `PARTIAL_PREDICATES`.
    "Forced": (SudokuSort.CELL, SudokuSort.NUMBER),
    "Excluded": (SudokuSort.CELL, SudokuSort.NUMBER),
    "Possible": (SudokuSort.CELL, SudokuSort.NUMBER),
    # Predicates of sets of cells and of numbers; see `SET_PREDICATES`.
    "DigitsWithin": (SudokuSort.CELLSET, SudokuSort.NUMBERSET),
    "DigitsInclude": (SudokuSort.CELLSET, SudokuSort.NUMBERSET),
    "SameSize": (SudokuSort.CELLSET, SudokuSort.NUMBERSET),
    "WithinUnit": (SudokuSort.CELLSET,),
    "SharesUnit": (SudokuSort.CELLSET, SudokuSort.CELL),
    "CellIn": (SudokuSort.CELL, SudokuSort.CELLSET),
    "CellNotIn": (SudokuSort.CELL, SudokuSort.CELLSET),
    "NumberIn": (SudokuSort.NUMBER, SudokuSort.NUMBERSET),
    "NumberNotIn": (SudokuSort.NUMBER, SudokuSort.NUMBERSET),
}

# Predicates of a non-empty set of cells C and a non-empty set of numbers D:
# DigitsWithin(C, D), that the digits of C's cells all lie in D;
# DigitsInclude(C, D), that they include every digit of D; SameSize(C, D),
# that C and D have as many elements; WithinUnit(C), that some unit holds
# all of C; SharesUnit(C, z), that some unit holds all of C together with
# the cell z; and membership with its complement.
# Read on a partial grid as holding in all completions, DigitsWithin says
# that the candidates of C's cells lie in D, and DigitsInclude that every
# digit of D is forced into C, which for C within a unit means that its
# places there all lie in C. Like the Confined predicates, they keep
# Proposition 1 of the write-up: solved grids are the only objects needed.
SET_PREDICATES = (
    "DigitsWithin", "DigitsInclude", "SameSize", "WithinUnit", "SharesUnit",
    "CellIn", "CellNotIn", "NumberIn", "NumberNotIn",
)

# Predicates of a partial grid's cell x and a number n: Forced, that every
# completion has n in x; Excluded, that none does; Possible, that some does,
# the complement of Excluded. On a solved grid, Forced and Possible are
# Contains and Excluded is NotContains, but on a partial grid a cell may be
# neither forced nor excluded, so Contains and NotContains, complements on
# solved grids, do not apply. Possible is the one predicate not read as
# holding in all completions, which makes partial grids objects of their
# own: a grid with two possible digits in a cell is no solved grid.
PARTIAL_PREDICATES = ("Forced", "Excluded", "Possible")

# Predicates of a cell x and a number n saying where n lies: that its place
# in x's block lies in x's row (column), or its place in x's row (column)
# lies in x's block. "Only place" and "only digit" predicates would be
# Contains again: a digit kept out of every other cell of x's row is in x.
#
# Read on a partial grid as holding in all its completions (Contains as
# forced by the givens, NotContains as excluded by them), these predicates
# give a partial grid exactly the properties its completions share. It then
# refutes no rule that every solved grid satisfies, and the rules found on
# solved grids are the deduction techniques.
CONFINEMENT_PREDICATES = (
    "ConfinedToRowInBlock",
    "ConfinedToColumnInBlock",
    "ConfinedToBlockInRow",
    "ConfinedToBlockInColumn",
)

# Confinement predicates of two cells and a number: P(x, y, n) says that n's
# place in x's row (column) is x or y, the premise of an X-wing. It is about
# x's row, so it is symmetric only for y in that row, and P(x, x, n) is
# Contains(x, n).
PAIR_CONFINEMENT_PREDICATES = ("ConfinedToPairInRow", "ConfinedToPairInColumn")


def pair_confinement_cells(
    name: str,
    cell: Tuple[int, int],
    other: Tuple[int, int],
    block_size: int,
) -> List[Tuple[int, int]]:
    """The cells a ConfinedToPair predicate keeps n out of, for x in `cell`
    and y in `other`: the cells of x's row (column) other than x and y."""
    n = block_size**2
    r, c = cell
    line = (
        [(r, cc) for cc in range(n)]
        if name == "ConfinedToPairInRow"
        else [(rr, c) for rr in range(n)]
    )
    return [p for p in line if p not in (cell, other)]


def confinement_cells(name: str, cell: Tuple[int, int], block_size: int) -> List[Tuple[int, int]]:
    """The cells a Confined predicate keeps n out of, for x in `cell`: the
    cells of x's block outside x's row or column, or the cells of x's row or
    column outside x's block."""
    k, n = block_size, block_size**2
    r, c = cell
    block = [
        (rr, cc)
        for rr in range((r // k) * k, (r // k + 1) * k)
        for cc in range((c // k) * k, (c // k + 1) * k)
    ]
    in_block = lambda rr, cc: (rr // k, cc // k) == (r // k, c // k)
    return {
        "ConfinedToRowInBlock": [(rr, cc) for rr, cc in block if rr != r],
        "ConfinedToColumnInBlock": [(rr, cc) for rr, cc in block if cc != c],
        "ConfinedToBlockInRow": [(r, cc) for cc in range(n) if not in_block(r, cc)],
        "ConfinedToBlockInColumn": [(rr, c) for rr in range(n) if not in_block(rr, c)],
    }[name]


_EQUIVALENCE = {"symmetric": True, "reflexive": True}
_DISTINCTION = {"symmetric": True, "irreflexive": True}

# What the exploration may assume of each predicate without asking: the
# equivalences are symmetric and reflexive; peers, apart cells, the
# Different predicates are symmetric and never relate a cell to itself;
# and each Different predicate is the complement of the Same one.
PREDICATE_PROPERTIES: Dict[str, Dict[str, Any]] = {
    "Peers": _DISTINCTION,
    "Apart": _DISTINCTION,
    "Same": {**_EQUIVALENCE, "complement": "Different"},
    "Different": {**_DISTINCTION, "complement": "Same"},
    "Contains": {"complement": "NotContains"},
    "NotContains": {"complement": "Contains"},
    "SameNumber": {**_EQUIVALENCE, "complement": "DifferentNumbers"},
    "DifferentNumbers": {**_DISTINCTION, "complement": "SameNumber"},
    "SameBlock": {**_EQUIVALENCE, "complement": "DifferentBlocks"},
    "SameRow": {**_EQUIVALENCE, "complement": "DifferentRows"},
    "SameColumn": {**_EQUIVALENCE, "complement": "DifferentColumns"},
    "SameCell": {**_EQUIVALENCE, "complement": "DifferentCells"},
    "DifferentCells": {**_DISTINCTION, "complement": "SameCell"},
    "DifferentRows": {**_DISTINCTION, "complement": "SameRow"},
    "DifferentColumns": {**_DISTINCTION, "complement": "SameColumn"},
    "DifferentBlocks": {**_DISTINCTION, "complement": "SameBlock"},
    "SameBand": _EQUIVALENCE,
    "SameStack": _EQUIVALENCE,
    **{name: {} for name in CONFINEMENT_PREDICATES + PAIR_CONFINEMENT_PREDICATES},
    "Forced": {},
    "Excluded": {"complement": "Possible"},
    "Possible": {"complement": "Excluded"},
    "DigitsWithin": {},
    "DigitsInclude": {},
    "SameSize": {},
    "WithinUnit": {},
    "SharesUnit": {},
    "CellIn": {"complement": "CellNotIn"},
    "CellNotIn": {"complement": "CellIn"},
    "NumberIn": {"complement": "NumberNotIn"},
    "NumberNotIn": {"complement": "NumberIn"},
}


def sudoku_predicates(names: Iterable[str] = PRIMITIVE_PREDICATES) -> List[Predicate]:
    """The named predicates as plain symbols, for experts that interpret
    atoms by predicate name, as `SatSudokuRuleExpert` does; unlike
    `z3predicates`, they need no Z3 expert to be built."""
    return [
        Predicate(
            name,
            len(PREDICATE_SORTS[name]),
            sorts=PREDICATE_SORTS[name],
            **PREDICATE_PROPERTIES[name],
        )
        for name in names
    ]


def sudoku_background(
    predicates: Iterable[Predicate],
    variables: Iterable[SortedVariable],
) -> List[Implication]:
    """Implications that hold in every grid whatever its digits.

    They say that the equivalences are equivalences, how the grid's regions
    nest, and that a cell holds a single value, which for partial grids
    means a single forced digit, never also excluded; none of them depends on
    a Sudoku rule. Given as background, they leave the exploration to find
    only what the rules add. Implications mentioning a predicate not in
    `predicates` are left out.
    """
    predicates = tuple(predicates)
    by_name = {p.name: p for p in predicates}
    variables = tuple(variables)
    cells = [v for v in variables if v.sort is SudokuSort.CELL]
    numbers = [v for v in variables if v.sort is SudokuSort.NUMBER]
    atoms = atoms_over(predicates, variables)
    background: List[Implication] = []

    def rule(premise, conclusion=None) -> None:
        """Add premise -> conclusion, or premise -> ⊥ without a conclusion."""
        names = [name for name, _ in premise + (conclusion or [])]
        if all(name in by_name for name in names):
            background.append(Implication(
                (Atom(by_name[name], args) for name, args in premise),
                atoms if conclusion is None else
                (Atom(by_name[name], args) for name, args in conclusion),
            ))

    equivalences = [(name, cells) for name in CELL_EQUIVALENCES]
    equivalences.append(("SameNumber", numbers))
    for name, terms in equivalences:
        for u in terms:
            rule([], [(name, (u, u))])
        for u, v in product(terms, repeat=2):
            rule([(name, (u, v))], [(name, (v, u))])
        for u, v, w in product(terms, repeat=3):
            rule([(name, (u, v)), (name, (v, w))], [(name, (u, w))])

    for u, v in product(cells, repeat=2):
        for name in CELL_EQUIVALENCES[1:]:
            rule([("SameCell", (u, v))], [(name, (u, v))])
        rule([("SameRow", (u, v)), ("SameColumn", (u, v))], [("SameCell", (u, v))])
        rule([("SameRow", (u, v))], [("SameBand", (u, v))])
        rule([("SameColumn", (u, v))], [("SameStack", (u, v))])
        rule([("SameBlock", (u, v))], [("SameBand", (u, v))])
        rule([("SameBlock", (u, v))], [("SameStack", (u, v))])
        rule([("SameBand", (u, v)), ("SameStack", (u, v))], [("SameBlock", (u, v))])
        for n in numbers:
            rule([("Contains", (u, n)), ("Same", (u, v))], [("Contains", (v, n))])
            rule([("NotContains", (u, n)), ("Same", (u, v))], [("NotContains", (v, n))])
            rule([("Contains", (u, n)), ("Contains", (v, n))], [("Same", (u, v))])

    # Distinctness passes along equalities. Horn rules cannot get this from
    # the complements, since it is their contrapositive.
    for u, v, w in product(cells, repeat=3):
        for same, different in (
            ("SameCell", "DifferentCells"),
            ("SameRow", "DifferentRows"),
            ("SameColumn", "DifferentColumns"),
            ("SameBlock", "DifferentBlocks"),
        ):
            rule([(same, (u, v)), (different, (v, w))], [(different, (u, w))])
    for n, m, k in product(numbers, repeat=3):
        rule([("SameNumber", (n, m)), ("DifferentNumbers", (m, k))], [("DifferentNumbers", (n, k))])

    # A cell holds one digit, so a digit it holds differs from one it does
    # not; and equal cells and numbers are interchangeable. Contains and
    # NotContains exclude each other as complements (see `RuleExploration`).
    per_cell = ("Contains", "NotContains") + PARTIAL_PREDICATES + CONFINEMENT_PREDICATES
    for u in cells:
        for n, m in product(numbers, repeat=2):
            rule([("Contains", (u, n)), ("Contains", (u, m))], [("SameNumber", (n, m))])
            rule([("Contains", (u, n)), ("NotContains", (u, m))], [("DifferentNumbers", (n, m))])
            rule([("Contains", (u, n)), ("DifferentNumbers", (n, m))], [("NotContains", (u, m))])
            for name in per_cell:
                rule([(name, (u, n)), ("SameNumber", (n, m))], [(name, (u, m))])
    for u, v in product(cells, repeat=2):
        for n in numbers:
            for name in per_cell:
                rule([(name, (u, n)), ("SameCell", (u, v))], [(name, (v, n))])
            rule([("Contains", (u, n)), ("NotContains", (v, n))], [("DifferentCells", (u, v))])
        for n, m in product(numbers, repeat=2):
            rule(
                [("Contains", (u, n)), ("Contains", (v, m)), ("DifferentNumbers", (n, m))],
                [("DifferentCells", (u, v))],
            )

    # On a partial grid, a forced digit is possible, and a cell has at most
    # one, which is not also excluded: the facts above with Forced for
    # Contains and Excluded for NotContains. Possible and Excluded are
    # complements, and the contrapositive forms with Possible are given too,
    # since Horn rules cannot derive them.
    for u in cells:
        for n in numbers:
            rule([("Forced", (u, n)), ("Excluded", (u, n))])
            rule([("Forced", (u, n))], [("Possible", (u, n))])
        for n, m in product(numbers, repeat=2):
            rule([("Forced", (u, n)), ("Forced", (u, m))], [("SameNumber", (n, m))])
            rule([("Forced", (u, n)), ("Excluded", (u, m))], [("DifferentNumbers", (n, m))])
            rule([("Forced", (u, n)), ("DifferentNumbers", (n, m))], [("Excluded", (u, m))])
            rule([("Forced", (u, n)), ("Possible", (u, m))], [("SameNumber", (n, m))])
            rule([("Possible", (u, n)), ("Excluded", (u, m))], [("DifferentNumbers", (n, m))])
    for u, v in product(cells, repeat=2):
        for n in numbers:
            rule([("Forced", (u, n)), ("Excluded", (v, n))], [("DifferentCells", (u, v))])
            rule([("Possible", (u, n)), ("Excluded", (v, n))], [("DifferentCells", (u, v))])
        for n, m in product(numbers, repeat=2):
            rule(
                [("Forced", (u, n)), ("Forced", (v, m)), ("DifferentNumbers", (n, m))],
                [("DifferentCells", (u, v))],
            )

    # Membership and SharesUnit do not tell equal cells or numbers apart; a
    # member and a non-member differ; a set shares a unit with a cell just
    # when it lies within a unit, if the cell is a member, and then the
    # member shares a unit with the other cells there. A cell of C, whose
    # digits lie within D, holds no digit outside D. These follow from the definitions; how the size of a
    # set bears on its digits is left to the exploration.
    cell_sets = [v for v in variables if v.sort is SudokuSort.CELLSET]
    number_sets = [v for v in variables if v.sort is SudokuSort.NUMBERSET]
    for c in cell_sets:
        for u, v in product(cells, repeat=2):
            for name in ("CellIn", "CellNotIn"):
                rule([(name, (u, c)), ("SameCell", (u, v))], [(name, (v, c))])
            rule([("CellIn", (u, c)), ("CellNotIn", (v, c))], [("DifferentCells", (u, v))])
            rule([("SharesUnit", (c, u)), ("SameCell", (u, v))], [("SharesUnit", (c, v))])
            rule([("CellIn", (u, c)), ("SharesUnit", (c, v)), ("DifferentCells", (u, v))], [("Peers", (u, v))])
        for u in cells:
            rule([("SharesUnit", (c, u))], [("WithinUnit", (c,))])
            rule([("WithinUnit", (c,)), ("CellIn", (u, c))], [("SharesUnit", (c, u))])
        for numbers_set in number_sets:
            for u in cells:
                for m in numbers:
                    rule(
                        [("DigitsWithin", (c, numbers_set)), ("CellIn", (u, c)), ("NumberNotIn", (m, numbers_set))],
                        [("NotContains", (u, m))],
                    )
                    rule(
                        [("DigitsWithin", (c, numbers_set)), ("CellIn", (u, c)), ("Contains", (u, m))],
                        [("NumberIn", (m, numbers_set))],
                    )
    for numbers_set in number_sets:
        for m1, m2 in product(numbers, repeat=2):
            for name in ("NumberIn", "NumberNotIn"):
                rule([(name, (m1, numbers_set)), ("SameNumber", (m1, m2))], [(name, (m2, numbers_set))])
            rule([("NumberIn", (m1, numbers_set)), ("NumberNotIn", (m2, numbers_set))], [("DifferentNumbers", (m1, m2))])
    for c1, c2 in product(cell_sets, repeat=2):
        for d1, d2 in product(number_sets, repeat=2):
            rule([("SameSize", (c1, d1)), ("SameSize", (c2, d1)), ("SameSize", (c2, d2))], [("SameSize", (c1, d2))])

    # A pair in one row (column) confines n there whichever way round it is
    # named; a pair of one cell puts n there; and equal cells and numbers
    # are interchangeable.
    for name, same_line in zip(PAIR_CONFINEMENT_PREDICATES, ("SameRow", "SameColumn")):
        for u, v in product(cells, repeat=2):
            for n in numbers:
                rule([(name, (u, v, n)), (same_line, (u, v))], [(name, (v, u, n))])
                for w in cells:
                    rule([(name, (u, v, n)), ("SameCell", (u, w))], [(name, (w, v, n))])
                    rule([(name, (u, v, n)), ("SameCell", (v, w))], [(name, (u, w, n))])
                for m in numbers:
                    rule([(name, (u, v, n)), ("SameNumber", (n, m))], [(name, (u, v, m))])
        for u in cells:
            for n in numbers:
                for one_place in ("Contains", "Forced"):
                    rule([(name, (u, u, n))], [(one_place, (u, n))])
                    rule([(one_place, (u, n))], [(name, (u, u, n))])

    return background


# ---------------------------------------------------------------------------
# 6. SAT-based First-Order Rule Expert & Checking Across Grid Sizes
# ---------------------------------------------------------------------------

class _Definitions:
    """Fresh SAT variables defined as conjunctions and disjunctions of literals.

    Each definition is an equivalence, so a defined literal may be used
    negated as well as plain. Clauses collect in `pending` until the owner
    hands them to its solver.
    """

    def __init__(self, first_var: int) -> None:
        self.top = first_var - 1
        self.pending: List[List[int]] = []

    def var(self) -> int:
        self.top += 1
        return self.top

    def conj(self, literals: Iterable[int]) -> int:
        literals = list(literals)
        if len(literals) == 1:
            return literals[0]
        v = self.var()
        self.pending.extend([-v, a] for a in literals)
        self.pending.append([v] + [-a for a in literals])
        return v

    def disj(self, literals: Iterable[int]) -> int:
        literals = list(literals)
        if len(literals) == 1:
            return literals[0]
        v = self.var()
        self.pending.extend([v, -a] for a in literals)
        self.pending.append([-v] + literals)
        return v

    def exactly_one(self, literals: List[int]) -> None:
        self.pending.append(list(literals))
        self.pending.extend([-a, -b] for a, b in combinations(literals, 2))


class SudokuRuleWitness:
    """A grid together with the cells and numbers a rule's variables denote.

    In a partial grid, 0 stands for an empty cell.
    """

    def __init__(
        self,
        assignment: Tuple[Tuple[str, Any], ...],
        grid: Tuple[Tuple[int, ...], ...],
    ) -> None:
        self.assignment = assignment
        self.grid = grid

    def _key(self):
        return self.assignment, self.grid

    def __eq__(self, other: object) -> bool:
        return isinstance(other, SudokuRuleWitness) and self._key() == other._key()

    def __hash__(self) -> int:
        return hash(self._key())

    def __str__(self) -> str:
        values = ", ".join(f"{name}={value}" for name, value in self.assignment)
        rows = "\n".join(" ".join(str(d) if d else "." for d in row) for row in self.grid)
        return f"{values}\n{rows}"


class _SatRuleExpert(Expert):
    """What the SAT experts for first-order Sudoku rules share: one-hot rows
    and columns for the cell variables and digits for the number variables,
    the predicates of the grid's geometry and of numbers, and the search for
    a counterexample. Atoms are interpreted by the name of their predicate.

    Subclasses supply the clauses that describe the grids, a witness built
    from a model, and the predicates about the grid's contents.
    """

    def __init__(
        self,
        block_size: int,
        variables: Iterable[SortedVariable],
        clauses: Iterable[List[int]],
        first_var: int,
        solver_name: str = "g3",
    ) -> None:
        self.block_size = block_size
        self.grid_size = n = block_size**2
        self._defs = _Definitions(first_var)
        self._solver = Solver(name=solver_name, bootstrap_with=clauses)

        self._rows: Dict[SortedVariable, List[int]] = {}
        self._columns: Dict[SortedVariable, List[int]] = {}
        self._digits: Dict[SortedVariable, List[int]] = {}
        # Membership of each cell (r * n + c) or digit (d - 1) in a set
        # variable, which must not be empty.
        self._members: Dict[SortedVariable, List[int]] = {}
        self.variables = tuple(variables)
        for v in self.variables:
            if v.sort is SudokuSort.CELL:
                self._rows[v] = [self._defs.var() for _ in range(n)]
                self._columns[v] = [self._defs.var() for _ in range(n)]
                self._defs.exactly_one(self._rows[v])
                self._defs.exactly_one(self._columns[v])
            elif v.sort is SudokuSort.NUMBER:
                self._digits[v] = [self._defs.var() for _ in range(n)]
                self._defs.exactly_one(self._digits[v])
            else:
                size = n * n if v.sort is SudokuSort.CELLSET else n
                self._members[v] = [self._defs.var() for _ in range(size)]
                self._defs.pending.append(list(self._members[v]))

        self._memo: Dict[Tuple[Any, ...], Any] = {}

    def validate(
        self,
        implication: Implication,
        attributes: Optional[Iterable[Any]] = None,
    ) -> Optional[PartialObject]:
        premise = [self._literal(a) for a in implication.premise]
        conclusion = [self._literal(a) for a in implication.conclusion]
        # Only the call that assumes `active` needs a conclusion atom false.
        active = self._defs.var()
        self._defs.pending.append([-active] + [-c for c in conclusion])

        if attributes is None:
            attributes = implication.premise | implication.conclusion
        literals = {a: self._literal(a) for a in attributes}

        self._solver.append_formula(self._defs.pending)
        self._defs.pending = []
        if not self._solver.solve(assumptions=premise + [active]):
            return None

        true = {v for v in self._solver.get_model() if v > 0}
        positive = {
            a for a, lit in literals.items()
            if (lit in true if lit > 0 else -lit not in true)
        }
        return PartialObject(
            self._witness(true),
            positive,
            set(literals) - positive,
        )

    def _witness(self, true: Set[int]) -> SudokuRuleWitness:
        raise NotImplementedError

    def _assignment(self, true: Set[int]) -> Tuple[Tuple[str, Any], ...]:
        n = self.grid_size
        index = lambda literals: next(i for i, v in enumerate(literals) if v in true)
        members = lambda v: [i for i, lit in enumerate(self._members[v]) if lit in true]

        def value(v: SortedVariable) -> Any:
            if v.sort is SudokuSort.CELL:
                return index(self._rows[v]), index(self._columns[v])
            if v.sort is SudokuSort.NUMBER:
                return index(self._digits[v]) + 1
            if v.sort is SudokuSort.CELLSET:
                return tuple(divmod(i, n) for i in members(v))
            return tuple(i + 1 for i in members(v))

        return tuple((v.name, value(v)) for v in self.variables)

    def _at_least(self, bits: List[int], limit: int) -> List[int]:
        """Literals saying that at least k of `bits` are true, for k from 0
        to `limit`: a unary counter, with each count an equivalence."""
        d = self._defs
        true = d.conj(())
        false = -true
        counts = [true] + [false] * limit
        for bit in bits:
            new = [true]
            for k in range(1, limit + 1):
                below, before = counts[k - 1], counts[k]
                with_bit = false if below == false else bit if below == true else d.conj((below, bit))
                if before == false or with_bit == true:
                    new.append(with_bit)
                elif with_bit == false or before == true:
                    new.append(before)
                else:
                    new.append(d.disj((before, with_bit)))
            counts = new
        return counts

    def _units(self) -> List[Tuple[str, int, List[int]]]:
        """The rows, columns and blocks, each as its kind, its index and the
        positions r * n + c of its cells."""
        k, n = self.block_size, self.grid_size
        rows = [("row", r, [r * n + c for c in range(n)]) for r in range(n)]
        columns = [("column", c, [r * n + c for r in range(n)]) for c in range(n)]
        blocks = [
            ("block", b, [
                r * n + c
                for r in range((b // k) * k, (b // k + 1) * k)
                for c in range((b % k) * k, (b % k + 1) * k)
            ])
            for b in range(n)
        ]
        return rows + columns + blocks

    def _grid(self, true: Set[int], empty: Optional[int] = None) -> Tuple[Tuple[int, ...], ...]:
        """The digits that the grid variables get_var(r, c, d) set true,
        with `empty` where a cell has none."""
        n = self.grid_size
        return tuple(
            tuple(
                next((d for d in range(1, n + 1) if get_var(r, c, d, n) in true), empty)
                for c in range(n)
            )
            for r in range(n)
        )

    def _literal(self, atom: Any) -> int:
        return self._defined((atom.predicate.name,) + tuple(atom.arguments))

    def _defined(self, key: Tuple[Any, ...]):
        if key not in self._memo:
            self._memo[key] = self._define(*key)
        return self._memo[key]

    def _same(self, xs: List[int], ys: List[int]) -> int:
        """True where two one-hot encodings pick the same position."""
        d = self._defs
        return d.disj(d.conj((a, b)) for a, b in zip(xs, ys))

    def _lines(self, name: str, x: Any, y: Any):
        """For a ConfinedToPair predicate, the one-hot encodings of x's and
        y's line (row or column) and of their place across it."""
        if name == "ConfinedToPairInRow":
            return self._rows[x], self._columns[x], self._rows[y], self._columns[y]
        return self._columns[x], self._rows[x], self._columns[y], self._rows[y]

    def _define(self, name: str, *args: Any):
        d = self._defs
        k, n = self.block_size, self.grid_size
        regions = lambda literals: [
            d.disj(literals[i * k:(i + 1) * k]) for i in range(k)
        ]

        # Per-variable encodings, memoised under keys of their own.
        if name == "band":
            return regions(self._rows[args[0]])
        if name == "stack":
            return regions(self._columns[args[0]])
        if name == "position":
            (x,) = args
            return [
                d.conj((self._rows[x][r], self._columns[x][c]))
                for r in range(n)
                for c in range(n)
            ]

        if name in ("SameNumber", "DifferentNumbers"):
            lit = self._same(self._digits[args[0]], self._digits[args[1]])
            return lit if name == "SameNumber" else -lit
        if name in ("CellIn", "CellNotIn"):
            x, cells = args
            lit = self._same(self._defined(("position", x)), self._members[cells])
            return lit if name == "CellIn" else -lit
        if name in ("NumberIn", "NumberNotIn"):
            m, numbers = args
            lit = self._same(self._digits[m], self._members[numbers])
            return lit if name == "NumberIn" else -lit
        if name == "count":
            # At least k members, for k up to one more than a unit holds.
            (v,) = args
            return self._at_least(self._members[v], n + 1)
        if name == "SameSize":
            cells, numbers = args
            c, m = self._defined(("count", cells)), self._defined(("count", numbers))
            return d.disj(
                d.conj((c[size], -c[size + 1], m[size], -m[size + 1]))
                for size in range(1, n + 1)
            )
        if name == "inside":
            # Whether every member of the cell set lies in unit u.
            cells, u = args
            positions = set(self._units()[u][2])
            return d.conj(-lit for p, lit in enumerate(self._members[cells]) if p not in positions)
        if name == "WithinUnit":
            (cells,) = args
            return d.disj(self._defined(("inside", cells, u)) for u in range(len(self._units())))
        if name == "SharesUnit":
            cells, z = args
            placed = {
                "row": lambda i: self._rows[z][i],
                "column": lambda i: self._columns[z][i],
                "block": lambda i: d.conj((
                    self._defined(("band", z))[i // k], self._defined(("stack", z))[i % k],
                )),
            }
            return d.disj(
                d.conj((self._defined(("inside", cells, u)), placed[kind](i)))
                for u, (kind, i, _) in enumerate(self._units())
            )

        x, y = args
        if name == "SameRow":
            return self._same(self._rows[x], self._rows[y])
        if name == "SameColumn":
            return self._same(self._columns[x], self._columns[y])
        if name == "SameBand":
            return self._same(self._defined(("band", x)), self._defined(("band", y)))
        if name == "SameStack":
            return self._same(self._defined(("stack", x)), self._defined(("stack", y)))
        if name == "SameBlock":
            return d.conj((self._defined(("SameBand", x, y)), self._defined(("SameStack", x, y))))
        if name == "SameCell":
            return d.conj((self._defined(("SameRow", x, y)), self._defined(("SameColumn", x, y))))
        if name == "DifferentCells":
            return -self._defined(("SameCell", x, y))
        if name == "DifferentRows":
            return -self._defined(("SameRow", x, y))
        if name == "DifferentColumns":
            return -self._defined(("SameColumn", x, y))
        if name == "DifferentBlocks":
            return -self._defined(("SameBlock", x, y))

        together = d.disj((
            self._defined(("SameRow", x, y)),
            self._defined(("SameColumn", x, y)),
            self._defined(("SameBlock", x, y)),
        ))
        if name == "Apart":
            return -together
        if name == "Peers":
            return d.conj((together, -self._defined(("SameCell", x, y))))
        raise ValueError(f"No SAT encoding for predicate {name!r}")


class SatSudokuRuleExpert(_SatRuleExpert):
    """SAT-based expert for first-order Sudoku rules, complete at any block size.

    A counterexample is a solved grid together with a cell for each cell
    variable and a digit for each number variable. Atoms are interpreted by
    the name of their predicate, so the atoms of an exploration run with
    `Z3SudokuExpert`, at any block size, can be checked here unchanged.
    """

    def __init__(
        self,
        block_size: int,
        variables: Iterable[SortedVariable],
        solver_name: str = "g3",
    ) -> None:
        n = block_size**2
        formula = sudoku2sat([[0] * n for _ in range(n)], block_size)
        super().__init__(block_size, variables, formula.clauses, n**3 + 1, solver_name)

    def _witness(self, true: Set[int]) -> SudokuRuleWitness:
        return SudokuRuleWitness(self._assignment(true), self._grid(true))

    def _define(self, name: str, *args: Any):
        d = self._defs
        k, n = self.block_size, self.grid_size
        if name == "value":
            (x,) = args
            position = self._defined(("position", x))
            return [
                d.disj(
                    d.conj((position[r * n + c], get_var(r, c, digit, n)))
                    for r in range(n)
                    for c in range(n)
                )
                for digit in range(1, n + 1)
            ]
        if name in ("Contains", "NotContains"):
            x, number = args
            lit = self._same(self._defined(("value", x)), self._digits[number])
            return lit if name == "Contains" else -lit
        if name in ("Same", "Different"):
            x, y = args
            lit = self._same(self._defined(("value", x)), self._defined(("value", y)))
            return lit if name == "Same" else -lit
        if name == "digits_of":
            # Which digits the cells of the set hold. Counting them is what
            # the questions about sizes come down to, and SAT solvers prove
            # such counting arguments (pigeonhole) badly, so two facts that
            # hold in every solved grid are added: a set has no more digits
            # than cells, and one within a unit has exactly as many.
            # Third, a set with as many digits as cells holds no digit
            # twice.
            (cells,) = args
            held = [
                [d.conj((lit, get_var(p // n, p % n, digit, n))) for p, lit in enumerate(self._members[cells])]
                for digit in range(1, n + 1)
            ]
            digits = [d.disj(cells_holding) for cells_holding in held]
            at_least_digits = self._at_least(digits, n + 1)
            at_least_cells = self._defined(("count", cells))
            within = self._defined(("WithinUnit", cells))
            for size in range(1, n + 2):
                d.pending.append([-at_least_digits[size], at_least_cells[size]])
                d.pending.append([-within, -at_least_cells[size], at_least_digits[size]])
            as_many = d.conj(
                d.disj((-at_least_cells[size], at_least_digits[size])) for size in range(1, n + 2)
            )
            for cells_holding in held:
                # At most one of them, by a sequential counter, if as_many.
                seen = None
                for h in cells_holding:
                    if seen is not None:
                        d.pending.append([-as_many, -seen, -h])
                        now = d.var()
                        d.pending.append([-seen, now])
                        d.pending.append([-h, now])
                        seen = now
                    else:
                        seen = h
            return digits
        if name == "DigitsWithin":
            cells, numbers = args
            digits = self._defined(("digits_of", cells))
            return d.conj(d.disj((-lit, member)) for lit, member in zip(digits, self._members[numbers]))
        if name == "DigitsInclude":
            cells, numbers = args
            digits = self._defined(("digits_of", cells))
            return d.conj(d.disj((-member, lit)) for lit, member in zip(digits, self._members[numbers]))
        if name in CONFINEMENT_PREDICATES:
            # Wherever x is and whatever digit m is, the grid has that digit
            # in none of the cells the predicate keeps it out of.
            x, m = args
            position = self._defined(("position", x))
            return d.conj(
                d.disj((
                    -position[r * n + c],
                    -self._digits[m][digit - 1],
                    d.conj(
                        -get_var(br, bc, digit, n)
                        for br, bc in confinement_cells(name, (r, c), k)
                    ),
                ))
                for r in range(n)
                for c in range(n)
                for digit in range(1, n + 1)
            )
        if name in PAIR_CONFINEMENT_PREDICATES:
            # In x's row (column), the digit of m is in x or in y: wherever
            # the grid has it in that line, x or y is there.
            x, y, m = args
            by_row = name == "ConfinedToPairInRow"
            line_x, across_x, line_y, across_y = self._lines(name, x, y)
            return d.conj(
                d.disj((
                    -line_x[line],
                    -self._digits[m][digit - 1],
                    -(get_var(line, i, digit, n) if by_row else get_var(i, line, digit, n)),
                    across_x[i],
                    d.conj((line_y[line], across_y[i])),
                ))
                for line in range(n)
                for i in range(n)
                for digit in range(1, n + 1)
            )
        return super()._define(name, *args)


def sudoku_solutions(block_size: int) -> List[Tuple[Tuple[int, ...], ...]]:
    """Every solved grid of the given block size; feasible for 4x4 grids
    (288 of them), not for 9x9 ones."""
    n = block_size**2
    formula = sudoku2sat([[0] * n for _ in range(n)], block_size)
    with Solver(name="g3", bootstrap_with=formula.clauses) as solver:
        return [
            tuple(map(tuple, assemble_solution(model, block_size)))
            for model in solver.enum_models()
        ]


class PartialGridExpert(_SatRuleExpert):
    """SAT-based expert for rules about partial 4x4 grids.

    An object is a partial grid with at least one completion, together with
    a cell for each cell variable and a digit for each number variable.
    `Forced(x, n)` says that every completion has `n` in `x`, `Excluded(x, n)`
    that none does, and `Possible(x, n)` that some does; the Confined
    predicates hold if they hold in every completion.

    The givens are SAT variables, and each solved grid is consistent with
    them or not; the predicates quantify over those grids, so they are
    enumerated up front, which only 4x4 grids allow.
    """

    def __init__(
        self,
        variables: Iterable[SortedVariable],
        block_size: int = 2,
        solver_name: str = "g3",
    ) -> None:
        if block_size != 2:
            raise ValueError(
                "PartialGridExpert enumerates every solved grid, which only "
                "4x4 grids (block size 2) allow"
            )
        n = block_size**2
        # Variable get_var(r, c, d) says that cell (r, c) is given digit d.
        given = lambda r, c, d: get_var(r, c, d, n)
        clauses = [
            [-given(r, c, d), -given(r, c, e)]
            for r in range(n)
            for c in range(n)
            for d, e in combinations(range(1, n + 1), 2)
        ]
        super().__init__(block_size, variables, clauses, n**3 + 1, solver_name)

        # A solved grid is consistent with the givens when none of them
        # contradicts it; at least one must be.
        self._solutions = sudoku_solutions(block_size)
        self._consistent = [
            self._defs.conj(
                -given(r, c, d)
                for r in range(n)
                for c in range(n)
                for d in range(1, n + 1)
                if d != solution[r][c]
            )
            for solution in self._solutions
        ]
        self._defs.pending.append(list(self._consistent))

    def _witness(self, true: Set[int]) -> SudokuRuleWitness:
        return SudokuRuleWitness(self._assignment(true), self._grid(true, empty=0))

    def _kept_out(self, solution, name: str, x: Any, m: Any) -> int:
        """Whether the solved grid `solution` keeps the digit of number m out
        of the cells that Confined predicate `name` names for cell x."""
        d = self._defs
        n = self.grid_size
        position = self._defined(("position", x))
        return d.disj(
            d.conj((position[r * n + c], self._digits[m][digit - 1]))
            for r in range(n)
            for c in range(n)
            for digit in range(1, n + 1)
            if all(
                solution[br][bc] != digit
                for br, bc in confinement_cells(name, (r, c), self.block_size)
            )
        )

    def _pair_kept_out(self, solution, name: str, x: Any, y: Any, m: Any) -> int:
        """Whether the solved grid `solution` puts the digit of number m, in
        x's row (column), in x or in y."""
        d = self._defs
        n = self.grid_size
        by_row = name == "ConfinedToPairInRow"
        line_x, across_x, line_y, across_y = self._lines(name, x, y)
        cases = []
        for line in range(n):
            for digit in range(1, n + 1):
                # x's line and the digit decide the one cell holding it there.
                place = next(
                    i for i in range(n)
                    if (solution[line][i] if by_row else solution[i][line]) == digit
                )
                cases.append(d.conj((
                    line_x[line],
                    self._digits[m][digit - 1],
                    d.disj((across_x[place], d.conj((line_y[line], across_y[place])))),
                )))
        return d.disj(cases)

    def _in_every_completion(self, holds: Callable[[int], int]) -> int:
        """Whether every solved grid consistent with the givens satisfies
        `holds`, a literal for each grid's index."""
        d = self._defs
        return d.conj(
            d.disj((-consistent, holds(i)))
            for i, consistent in enumerate(self._consistent)
        )

    def _define(self, name: str, *args: Any):
        d = self._defs
        n = self.grid_size
        if name == "holds":
            # Whether solved grid i has, in cell x, the digit of number m.
            i, x, m = args
            position = self._defined(("position", x))
            solution = self._solutions[i]
            return d.disj(
                d.conj((
                    self._digits[m][digit - 1],
                    d.disj(
                        position[r * n + c]
                        for r in range(n)
                        for c in range(n)
                        if solution[r][c] == digit
                    ),
                ))
                for digit in range(1, n + 1)
            )
        if name == "Forced":
            x, m = args
            return self._in_every_completion(lambda i: self._defined(("holds", i, x, m)))
        if name == "Excluded":
            x, m = args
            return self._in_every_completion(lambda i: -self._defined(("holds", i, x, m)))
        if name == "Possible":
            return -self._defined(("Excluded", *args))
        if name in CONFINEMENT_PREDICATES:
            x, m = args
            return self._in_every_completion(
                lambda i: self._kept_out(self._solutions[i], name, x, m)
            )
        if name in PAIR_CONFINEMENT_PREDICATES:
            x, y, m = args
            return self._in_every_completion(
                lambda i: self._pair_kept_out(self._solutions[i], name, x, y, m)
            )
        return super()._define(name, *args)


def check_rules(
    implications: Iterable[Implication],
    block_size: int,
    variables: Iterable[SortedVariable],
) -> List[Tuple[Implication, Optional[PartialObject]]]:
    """Check rules found at one block size on grids of another.

    Returns each implication with a counterexample at `block_size`, or None
    where it holds on every grid of that size.
    """
    expert = SatSudokuRuleExpert(block_size, variables)
    return [(implication, expert.validate(implication)) for implication in implications]


# ---------------------------------------------------------------------------
# 7. Exploration Runner Helpers
# ---------------------------------------------------------------------------

def cell_exploration(block_size: int = 2) -> ExplorationBase:
    """Run relational rule exploration over cell variables (x, y, z, w)."""
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("w", SudokuSort.CELL),
    ]
    return _primitive_rule_exploration(block_size, variables, CELL_EQUIVALENCES)


def cell_number_exploration(block_size: int = 2) -> ExplorationBase:
    """Run relational rule exploration over cell and number variables."""
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
        SortedVariable("m", SudokuSort.NUMBER),
    ]
    return _primitive_rule_exploration(block_size, variables, PRIMITIVE_PREDICATES)


def _primitive_rule_exploration(
    block_size: int,
    variables: List[SortedVariable],
    names: Iterable[str],
) -> ExplorationBase:
    cells = [v.name for v in variables if v.sort is SudokuSort.CELL]
    numbers = [v.name for v in variables if v.sort is SudokuSort.NUMBER]
    exploration = sudoku_rule_exploration(
        block_size, cells, numbers, names, on_question=report_every(20)
    )
    exploration.run()
    return exploration.base


run_sudoku_rule_exploration = cell_number_exploration


# The predicates about where cells are, which do not depend on the digits.
GEOMETRIC_PREDICATES = (
    "SameCell", "DifferentCells", "SameRow", "DifferentRows", "SameColumn",
    "DifferentColumns", "SameBlock", "DifferentBlocks", "SameBand", "SameStack",
)


# Predicates about the digits, as opposed to where cells are or which
# numbers are equal.
DIGIT_PREDICATES = (
    ("Contains", "NotContains") + PARTIAL_PREDICATES
    + CONFINEMENT_PREDICATES + PAIR_CONFINEMENT_PREDICATES
)


def classical_rules(base: ExplorationBase, rules: List[Any]) -> List[Any]:
    """The simplified rules without those that follow classically from the
    others, with complements total (`classically_irredundant`). Rules
    concluding only where cells are or which numbers are equal, mostly
    contrapositive forms, are dropped first, so that the rules concluding
    about digits are kept."""
    about_digits = lambda rule: rule.everything or any(
        a.predicate.name in DIGIT_PREDICATES for a in rule.conclusion
    )
    return classically_irredundant(base, rules, drop_first=about_digits)


def geometry_basis(
    variables: Iterable[SortedVariable],
    names: Iterable[str],
    block_size: int = 2,
) -> List[Implication]:
    """The rules of the grid's geometry: the implications accepted by
    exploring the geometric predicates among `names` alone, over the cell
    variables among `variables`.

    Given as background, they keep facts about where cells can be from
    being reported among the rules about what the cells hold.
    """
    cells = [v for v in variables if v.sort is SudokuSort.CELL]
    predicates = sudoku_predicates(n for n in names if n in GEOMETRIC_PREDICATES)
    exploration = RuleExploration(
        predicates,
        cells,
        SatSudokuRuleExpert(block_size, cells),
        background=sudoku_background(predicates, cells),
        substitutions=True,
        evaluate_all=True,
    )
    exploration.run()
    return list(exploration.base.accepted_implications)


# The experts of the rule exploration: SAT decides every predicate, Z3 all
# but the confinement ones.
# What each kind of grid lets the predicates talk about: solved grids have
# values; partial grids have forced, excluded and possible digits, and what
# holds in all their completions, but no values of their own.
_GRID_PREDICATES: Dict[str, Set[str]] = {
    "solved": set(PREDICATE_SORTS) - set(PARTIAL_PREDICATES),
    "partial": (
        set(GEOMETRIC_PREDICATES) | set(PARTIAL_PREDICATES) | set(CONFINEMENT_PREDICATES)
        | set(PAIR_CONFINEMENT_PREDICATES) | {"Peers", "Apart", "SameNumber", "DifferentNumbers"}
    ),
}

# The experts for each kind of grid: on solved grids, SAT decides every
# predicate and Z3 all but the confinement ones; on partial grids, SAT lists
# every solved 4x4 grid.
_GRID_EXPERTS = {"solved": ("sat", "z3"), "partial": ("sat",)}
_NO_Z3_ENCODING = CONFINEMENT_PREDICATES + PAIR_CONFINEMENT_PREDICATES + SET_PREDICATES


def check_rule_exploration(
    block_size: int,
    cells: Iterable[str],
    numbers: Iterable[str],
    predicates: Iterable[str],
    expert: str = "sat",
    grid: str = "solved",
    cell_sets: Iterable[str] = (),
    number_sets: Iterable[str] = (),
) -> None:
    """Raise ValueError, saying why, if a rule exploration with these
    settings cannot be run."""
    cells, numbers, predicates = list(cells), list(numbers), list(predicates)
    cell_sets, number_sets = list(cell_sets), list(number_sets)
    if grid not in _GRID_PREDICATES:
        raise ValueError(f"grid must be one of {sorted(_GRID_PREDICATES)}, not {grid!r}")
    if block_size < 2:
        raise ValueError(f"block_size must be at least 2, not {block_size}")
    if expert not in _GRID_EXPERTS[grid]:
        raise ValueError(
            f"the expert for {grid} grids must be one of {list(_GRID_EXPERTS[grid])}, not {expert!r}"
        )
    if grid == "partial" and block_size != 2:
        raise ValueError(
            "partial grids need block_size 2: their expert lists every solved "
            "grid, which only 4x4 grids allow"
        )
    names = cells + numbers + cell_sets + number_sets
    if not names:
        raise ValueError("at least one cell or number variable is needed")
    if expert == "z3" and (cell_sets or number_sets):
        raise ValueError('set variables have no Z3 encoding; use expert = "sat"')
    if len(set(names)) != len(names):
        raise ValueError(f"variable names must be distinct: {names}")
    if not predicates:
        raise ValueError("at least one predicate is needed")
    unknown = [p for p in predicates if p not in PREDICATE_SORTS]
    if unknown:
        raise ValueError(f"unknown predicates {unknown}; known are {sorted(PREDICATE_SORTS)}")
    unsupported = [p for p in predicates if p not in _GRID_PREDICATES[grid]]
    if unsupported:
        raise ValueError(f"predicates {unsupported} do not apply to {grid} grids")
    unsupported = [p for p in predicates if p in _NO_Z3_ENCODING]
    if expert == "z3" and unsupported:
        raise ValueError(f"predicates {unsupported} have no Z3 encoding; use expert = \"sat\"")
    given = {
        SudokuSort.CELL: ("a cell variable", cells),
        SudokuSort.NUMBER: ("a number variable", numbers),
        SudokuSort.CELLSET: ("a cell set variable", cell_sets),
        SudokuSort.NUMBERSET: ("a number set variable", number_sets),
    }
    for p in predicates:
        for sort in set(PREDICATE_SORTS[p]):
            kind, variables = given[sort]
            if not variables:
                raise ValueError(f"predicate {p} needs {kind}")


def sudoku_rule_exploration(
    block_size: int,
    cells: Iterable[str],
    numbers: Iterable[str],
    predicates: Iterable[str],
    *,
    background: bool = True,
    geometry_first: bool = False,
    expert: str = "sat",
    grid: str = "solved",
    cell_sets: Iterable[str] = (),
    number_sets: Iterable[str] = (),
    on_question: Optional[Callable[[Any], None]] = None,
) -> RuleExploration:
    """Build a rule exploration of solved or partial Sudoku grids.

    `cells`, `numbers`, `cell_sets` and `number_sets` name the variables
    of each sort, and `predicates`
    the predicates to explore (see `PREDICATE_SORTS`; `PARTIAL_PREDICATES`
    apply to partial grids only, Contains and NotContains to solved ones). With `background`,
    what holds in any grid is given as background (`sudoku_background`);
    with `geometry_first`, the geometry is explored first and its rules are
    added to it, so that only rules about the grid's contents are reported.
    Settings that cannot be run raise ValueError, from
    `check_rule_exploration`.
    """
    cells, numbers, names = list(cells), list(numbers), list(predicates)
    cell_sets, number_sets = list(cell_sets), list(number_sets)
    check_rule_exploration(block_size, cells, numbers, names, expert, grid, cell_sets, number_sets)
    variables = (
        [SortedVariable(name, SudokuSort.CELL) for name in cells]
        + [SortedVariable(name, SudokuSort.NUMBER) for name in numbers]
        + [SortedVariable(name, SudokuSort.CELLSET) for name in cell_sets]
        + [SortedVariable(name, SudokuSort.NUMBERSET) for name in number_sets]
    )
    if grid == "partial":
        rule_expert = PartialGridExpert(variables, block_size)
        selected = sudoku_predicates(names)
    elif expert == "sat":
        rule_expert = SatSudokuRuleExpert(block_size, variables)
        selected = sudoku_predicates(names)
    else:
        rule_expert = Z3SudokuExpert(block_size, variables)
        selected = select_predicates(z3predicates(block_size, rule_expert), names)

    implications = sudoku_background(selected, variables) if background else []
    if geometry_first:
        implications += geometry_basis(variables, names, block_size)
    return RuleExploration(
        selected,
        variables,
        rule_expert,
        background=implications,
        substitutions=True,
        evaluate_all=True,
        on_question=on_question,
    )


def run_sudoku_sat_exploration(
    block_size: int = 2,
    use_symmetries: bool = True,
) -> Tuple[Any, ExplorationBase]:
    """Run propositional attribute exploration using SAT expert and symmetries."""
    attributes = get_sudoku_attributes(block_size)
    mappings = get_sudoku_symmetries(block_size) if use_symmetries else []

    base = ExplorationBase(
        attributes=attributes,
        background_implications=get_sudoku_background_implications(block_size),
        mappings=mappings,
    )
    expert = SudokuExpert(block_size)
    exploration = AttributeExploration(base, expert, on_question=report_every(20))
    state = exploration.run()
    return state, base
