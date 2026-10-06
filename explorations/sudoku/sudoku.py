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

from conceptual_exploration import AttributeExploration, Implication, report_every
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
    "SameNumber": _NUMBER_PAIR,
    "DifferentNumbers": _NUMBER_PAIR,
    "SameBlock": _CELL_PAIR,
    "SameRow": _CELL_PAIR,
    "SameColumn": _CELL_PAIR,
    "SameCell": _CELL_PAIR,
    "DifferentCells": _CELL_PAIR,
    "SameBand": _CELL_PAIR,
    "SameStack": _CELL_PAIR,
    # Predicates of partial grids, which only `PartialGridExpert` evaluates.
    "Forced": (SudokuSort.CELL, SudokuSort.NUMBER),
    "Excluded": (SudokuSort.CELL, SudokuSort.NUMBER),
}


_EQUIVALENCE = {"symmetric": True, "reflexive": True}
_DISTINCTION = {"symmetric": True, "irreflexive": True}

# What the exploration may assume of each predicate without asking: the
# equivalences are symmetric and reflexive; peers, apart cells, different
# cells and different values are symmetric and never relate a cell to itself;
# and `Different`, `DifferentNumbers` and `DifferentCells` are the complements
# of `Same`, `SameNumber` and `SameCell`.
PREDICATE_PROPERTIES: Dict[str, Dict[str, Any]] = {
    "Peers": _DISTINCTION,
    "Apart": _DISTINCTION,
    "Same": {**_EQUIVALENCE, "complement": "Different"},
    "Different": {**_DISTINCTION, "complement": "Same"},
    "Contains": {},
    "SameNumber": {**_EQUIVALENCE, "complement": "DifferentNumbers"},
    "DifferentNumbers": {**_DISTINCTION, "complement": "SameNumber"},
    "SameBlock": _EQUIVALENCE,
    "SameRow": _EQUIVALENCE,
    "SameColumn": _EQUIVALENCE,
    "SameCell": {**_EQUIVALENCE, "complement": "DifferentCells"},
    "DifferentCells": {**_DISTINCTION, "complement": "SameCell"},
    "SameBand": _EQUIVALENCE,
    "SameStack": _EQUIVALENCE,
    "Forced": {},
    "Excluded": {},
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
    nest, and that a cell holds a single value, which for partial grids means
    a single forced digit, never also excluded; none of them depends on a
    Sudoku rule. Given as background, they leave the exploration to find only
    what the rules add. Implications mentioning a predicate not in
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
            rule([("Contains", (u, n)), ("Contains", (v, n))], [("Same", (u, v))])

    for u in cells:
        for n, m in product(numbers, repeat=2):
            rule([("Contains", (u, n)), ("SameNumber", (n, m))], [("Contains", (u, m))])
            rule([("Contains", (u, n)), ("Contains", (u, m))], [("SameNumber", (n, m))])

    # Distinctness passes along equalities. Horn rules cannot get this from
    # the complements, since it is their contrapositive.
    for u, v, w in product(cells, repeat=3):
        rule([("SameCell", (u, v)), ("DifferentCells", (v, w))], [("DifferentCells", (u, w))])
    for n, m, k in product(numbers, repeat=3):
        rule([("SameNumber", (n, m)), ("DifferentNumbers", (m, k))], [("DifferentNumbers", (n, k))])

    # A cell of a partial grid has at most one forced digit, which is not
    # also excluded, and equal cells and numbers are interchangeable.
    for u in cells:
        for n in numbers:
            rule([("Forced", (u, n)), ("Excluded", (u, n))])
        for n, m in product(numbers, repeat=2):
            rule([("Forced", (u, n)), ("Forced", (u, m))], [("SameNumber", (n, m))])
            rule([("Forced", (u, n)), ("Excluded", (u, m))], [("DifferentNumbers", (n, m))])
            rule([("Forced", (u, n)), ("DifferentNumbers", (n, m))], [("Excluded", (u, m))])
            for name in ("Forced", "Excluded"):
                rule([(name, (u, n)), ("SameNumber", (n, m))], [(name, (u, m))])
    for u, v in product(cells, repeat=2):
        for n in numbers:
            for name in ("Forced", "Excluded"):
                rule([(name, (u, n)), ("SameCell", (u, v))], [(name, (v, n))])
            rule([("Forced", (u, n)), ("Excluded", (v, n))], [("DifferentCells", (u, v))])
        for n, m in product(numbers, repeat=2):
            rule(
                [("Forced", (u, n)), ("Forced", (v, m)), ("DifferentNumbers", (n, m))],
                [("DifferentCells", (u, v))],
            )

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
        self.variables = tuple(variables)
        for v in self.variables:
            if v.sort is SudokuSort.CELL:
                self._rows[v] = [self._defs.var() for _ in range(n)]
                self._columns[v] = [self._defs.var() for _ in range(n)]
                self._defs.exactly_one(self._rows[v])
                self._defs.exactly_one(self._columns[v])
            else:
                self._digits[v] = [self._defs.var() for _ in range(n)]
                self._defs.exactly_one(self._digits[v])

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
        index = lambda literals: next(i for i, v in enumerate(literals) if v in true)
        return tuple(
            (v.name, (index(self._rows[v]), index(self._columns[v])))
            if v.sort is SudokuSort.CELL
            else (v.name, index(self._digits[v]) + 1)
            for v in self.variables
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
        n = self.grid_size
        grid = tuple(
            tuple(
                next(d for d in range(1, n + 1) if get_var(r, c, d, n) in true)
                for c in range(n)
            )
            for r in range(n)
        )
        return SudokuRuleWitness(self._assignment(true), grid)

    def _define(self, name: str, *args: Any):
        d = self._defs
        n = self.grid_size
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
        if name == "Contains":
            x, number = args
            return self._same(self._defined(("value", x)), self._digits[number])
        if name in ("Same", "Different"):
            x, y = args
            lit = self._same(self._defined(("value", x)), self._defined(("value", y)))
            return lit if name == "Same" else -lit
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
    """SAT-based expert for rules about partial 4x4 grids and what follows
    from them.

    An object is a partial grid with at least one completion, together with
    a cell for each cell variable and a digit for each number variable.
    `Forced(x, n)` says that every completion has `n` in `x`, so that it
    follows from the givens; `Excluded(x, n)` says that none does. Rules
    over these predicates are deduction techniques.

    The givens are SAT variables, and each solved grid is consistent with
    them or not; deciding Forced and Excluded quantifies over those grids, so
    they are enumerated up front, which only 4x4 grids allow.
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
        n = self.grid_size
        grid = tuple(
            tuple(
                next((d for d in range(1, n + 1) if get_var(r, c, d, n) in true), 0)
                for c in range(n)
            )
            for r in range(n)
        )
        return SudokuRuleWitness(self._assignment(true), grid)

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
        if name in ("Forced", "Excluded"):
            x, m = args
            return d.conj(
                d.disj((
                    -consistent,
                    self._defined(("holds", i, x, m)) * (1 if name == "Forced" else -1),
                ))
                for i, consistent in enumerate(self._consistent)
            )
        return super()._define(name, *args)


class CegarPartialGridExpert(_SatRuleExpert):
    """Expert for rules about partial grids of any block size (prototype).

    It decides the same predicates as `PartialGridExpert` without listing
    the solved grids, which 9x9 grids have too many of. A counterexample has
    givens, a placement of the variables, and a completion W that breaks the
    conclusion; the premise's Forced and Excluded atoms must hold in every
    completion. That is an exists-forall question, decided by counterexample-
    guided refinement:

    - a SAT solver guesses givens, a placement and W, where W and every
      completion found so far that is consistent with the givens satisfy the
      premise;
    - a second SAT solver looks, under the guessed givens, for a completion
      that breaks a premise atom; one it finds joins the completions found
      so far and the guess is repeated;
    - a guess no completion breaks is a counterexample, and no guess at all
      means the implication holds.

    The completions found are kept for later questions. `refinements`
    counts them, and `rounds` the guesses made.
    """

    def __init__(
        self,
        variables: Iterable[SortedVariable],
        block_size: int = 2,
        solver_name: str = "g3",
    ) -> None:
        k, n = block_size, block_size**2
        self._n3 = n**3
        given = lambda r, c, d: get_var(r, c, d, n)
        witness = lambda r, c, d: self._n3 + get_var(r, c, d, n)
        # At most one given per cell; W is a solved grid that keeps them.
        clauses = [
            [-given(r, c, d), -given(r, c, e)]
            for r in range(n)
            for c in range(n)
            for d, e in combinations(range(1, n + 1), 2)
        ]
        clauses += [
            [lit + self._n3 if lit > 0 else lit - self._n3 for lit in clause]
            for clause in sudoku2sat([[0] * n for _ in range(n)], k).clauses
        ]
        clauses += [
            [-given(r, c, d), witness(r, c, d)]
            for r in range(n)
            for c in range(n)
            for d in range(1, n + 1)
        ]
        super().__init__(block_size, variables, clauses, 2 * self._n3 + 1, solver_name)
        self._given = given
        self._witness_var = witness

        # Completions found to break a premise, shared by later questions.
        self._completions: List[Tuple[Tuple[int, ...], ...]] = []
        self._verifier = Solver(
            name=solver_name,
            bootstrap_with=sudoku2sat([[0] * n for _ in range(n)], k).clauses,
        )
        self.refinements = 0
        self.rounds = 0

    def validate(
        self,
        implication: Implication,
        attributes: Optional[Iterable[Any]] = None,
    ) -> Optional[PartialObject]:
        semantic = lambda a: a.predicate.name in ("Forced", "Excluded")
        premise_static = [self._literal(a) for a in implication.premise if not semantic(a)]
        premise_semantic = [
            (a.predicate.name, a.arguments[0], a.arguments[1])
            for a in implication.premise if semantic(a)
        ]

        # Only the call that assumes `active` needs these.
        active = self._defs.var()
        failing = []
        for a in implication.conclusion:
            if semantic(a):
                holds_in_w = self._defined(("witness_holds", a.arguments[0], a.arguments[1]))
                failing.append(-holds_in_w if a.predicate.name == "Forced" else holds_in_w)
            else:
                failing.append(-self._literal(a))
        self._defs.pending.append([-active] + failing)
        for name, x, m in premise_semantic:
            holds_in_w = self._defined(("witness_holds", x, m))
            self._defs.pending.append([-active, holds_in_w if name == "Forced" else -holds_in_w])

        def require(completion: int) -> None:
            """Completion number `completion`, if consistent with the givens,
            satisfies the premise's Forced and Excluded atoms."""
            consistent = self._defined(("consistent", completion))
            for name, x, m in premise_semantic:
                holds = self._defined(("holds_in", completion, x, m))
                self._defs.pending.append(
                    [-active, -consistent, holds if name == "Forced" else -holds]
                )

        for completion in range(len(self._completions)):
            require(completion)

        while True:
            self.rounds += 1
            self._solver.append_formula(self._defs.pending)
            self._defs.pending = []
            if not self._solver.solve(assumptions=premise_static + [active]):
                return None
            true = {v for v in self._solver.get_model() if v > 0}
            givens = self._givens(true)
            places = self._places(true)
            broken = None
            for name, x, m in premise_semantic:
                (r, c), digit = places[x], places[m]
                broken = self._completion(givens, r, c, digit, name == "Excluded")
                if broken is not None:
                    break
            if broken is None:
                return self._counterexample(implication, attributes, true, givens, places)
            self._completions.append(broken)
            self.refinements += 1
            require(len(self._completions) - 1)

    def _givens(self, true: Set[int]) -> Dict[Tuple[int, int], int]:
        n = self.grid_size
        return {
            (r, c): d
            for r in range(n)
            for c in range(n)
            for d in range(1, n + 1)
            if self._given(r, c, d) in true
        }

    def _places(self, true: Set[int]) -> Dict[SortedVariable, Any]:
        index = lambda literals: next(i for i, v in enumerate(literals) if v in true)
        return {
            v: (index(self._rows[v]), index(self._columns[v]))
            if v.sort is SudokuSort.CELL
            else index(self._digits[v]) + 1
            for v in self.variables
        }

    def _completion(self, givens, r, c, digit, has_digit):
        """A completion of the givens with (has_digit) or without digit in
        cell (r, c), or None if there is none."""
        n = self.grid_size
        assumptions = [get_var(gr, gc, d, n) for (gr, gc), d in givens.items()]
        cell = get_var(r, c, digit, n)
        if not self._verifier.solve(assumptions=assumptions + [cell if has_digit else -cell]):
            return None
        return tuple(map(tuple, assemble_solution(self._verifier.get_model(), self.block_size)))

    def _counterexample(self, implication, attributes, true, givens, places):
        if attributes is None:
            attributes = implication.premise | implication.conclusion
        n = self.grid_size
        positive = set()
        for a in attributes:
            if a.predicate.name in ("Forced", "Excluded"):
                (r, c), digit = places[a.arguments[0]], places[a.arguments[1]]
                # Forced: no completion lacks the digit; Excluded: none has it.
                has_digit = a.predicate.name == "Excluded"
                holds = self._completion(givens, r, c, digit, has_digit) is None
            else:
                lit = self._literal(a)
                holds = lit in true if lit > 0 else -lit not in true
            if holds:
                positive.add(a)
        grid = tuple(
            tuple(givens.get((r, c), 0) for c in range(n))
            for r in range(n)
        )
        assignment = tuple((v.name, places[v]) for v in self.variables)
        return PartialObject(
            SudokuRuleWitness(assignment, grid),
            positive,
            set(attributes) - positive,
        )

    def _define(self, name: str, *args: Any):
        d = self._defs
        n = self.grid_size
        if name == "witness_holds":
            # Whether W has, in cell x, the digit of number m.
            x, m = args
            position = self._defined(("position", x))
            return d.disj(
                d.conj((
                    self._digits[m][digit - 1],
                    d.disj(
                        d.conj((position[r * n + c], self._witness_var(r, c, digit)))
                        for r in range(n)
                        for c in range(n)
                    ),
                ))
                for digit in range(1, n + 1)
            )
        if name == "consistent":
            (i,) = args
            solution = self._completions[i]
            return d.conj(
                -self._given(r, c, digit)
                for r in range(n)
                for c in range(n)
                for digit in range(1, n + 1)
                if digit != solution[r][c]
            )
        if name == "holds_in":
            # Whether completion i has, in cell x, the digit of number m.
            i, x, m = args
            position = self._defined(("position", x))
            solution = self._completions[i]
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
        "solved", block_size, cells, numbers, names, on_question=report_every(20)
    )
    exploration.run()
    return exploration.base


run_sudoku_rule_exploration = cell_number_exploration


# The predicates about where cells are, which do not depend on the digits.
GEOMETRIC_PREDICATES = (
    "SameCell", "DifferentCells", "SameRow", "SameColumn", "SameBlock", "SameBand", "SameStack",
)


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


# What each kind of grid lets the predicates talk about: solved grids have
# values but nothing follows from anything, partial grids have forced and
# excluded digits but no values of their own.
_GRID_PREDICATES: Dict[str, Set[str]] = {
    "solved": set(PREDICATE_SORTS) - {"Forced", "Excluded"},
    "partial": set(GEOMETRIC_PREDICATES) | {
        "Peers", "Apart", "Forced", "Excluded", "SameNumber", "DifferentNumbers",
    },
}


def check_rule_exploration(
    grid: str,
    block_size: int,
    cells: Iterable[str],
    numbers: Iterable[str],
    predicates: Iterable[str],
    expert: str = "sat",
) -> None:
    """Raise ValueError, saying why, if a rule exploration with these
    settings cannot be run."""
    cells, numbers, predicates = list(cells), list(numbers), list(predicates)
    if grid not in _GRID_PREDICATES:
        raise ValueError(f"grid must be one of {sorted(_GRID_PREDICATES)}, not {grid!r}")
    if block_size < 2:
        raise ValueError(f"block_size must be at least 2, not {block_size}")
    if grid == "partial" and block_size != 2:
        raise ValueError(
            "partial grids need block_size 2: deciding what follows from the "
            "givens enumerates every solved grid, which only 4x4 grids allow"
        )
    if expert not in ("sat", "z3"):
        raise ValueError(f"expert must be 'sat' or 'z3', not {expert!r}")
    if expert == "z3" and grid != "solved":
        raise ValueError("the z3 expert decides rules about solved grids only")
    names = cells + numbers
    if not names:
        raise ValueError("at least one cell or number variable is needed")
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
    for p in predicates:
        sorts = set(PREDICATE_SORTS[p])
        if SudokuSort.CELL in sorts and not cells:
            raise ValueError(f"predicate {p} needs a cell variable")
        if SudokuSort.NUMBER in sorts and not numbers:
            raise ValueError(f"predicate {p} needs a number variable")


def sudoku_rule_exploration(
    grid: str,
    block_size: int,
    cells: Iterable[str],
    numbers: Iterable[str],
    predicates: Iterable[str],
    *,
    background: bool = True,
    geometry_first: bool = False,
    expert: str = "sat",
    on_question: Optional[Callable[[Any], None]] = None,
) -> RuleExploration:
    """Build a rule exploration of solved or partial Sudoku grids.

    `cells` and `numbers` name the variables of each sort, and `predicates`
    the predicates to explore (see `PREDICATE_SORTS`). With `background`,
    what holds in any grid is given as background (`sudoku_background`);
    with `geometry_first`, the geometry is explored first and its rules are
    added to it, so that only rules about the grid's contents are reported.
    Settings that cannot be run raise ValueError, from
    `check_rule_exploration`.
    """
    cells, numbers, names = list(cells), list(numbers), list(predicates)
    check_rule_exploration(grid, block_size, cells, numbers, names, expert)
    variables = (
        [SortedVariable(name, SudokuSort.CELL) for name in cells]
        + [SortedVariable(name, SudokuSort.NUMBER) for name in numbers]
    )
    if grid == "partial":
        rule_expert = PartialGridExpert(variables)
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
