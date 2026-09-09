import time
import z3

from enum import auto

from core.context import PartialObject
from logic.predicate import EvaluatablePredicate
from logic.variable import Sort, SortedVariable
from experts.base import Expert
from exploration.rule import RuleExploration
from core.theory import ImplicationTheory


class SudokuSort(Sort):
    CELL = auto()
    NUMBER = auto()


def z3_variables(variables):
    return {
        v:
            (z3.Int(f"{v.name}.row"), z3.Int(f"{v.name}.col"))
            if v.sort is SudokuSort.CELL
            else z3.Int(v.name)
        for v in variables
    }


class Z3SudokuExpert(Expert):
    def __init__(self, block_size, variables):
        self.block_size = block_size
        self.grid_size = block_size**2
        self.value = z3.Function(
            "value",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )
        # self.axioms = self._sudoku_axioms()
        self.zvars = z3_variables(variables)

        self.solver = z3.Solver()
        self.solver.add(*self._domain_constraints(self.zvars))
        self.solver.add(*self._sudoku_axioms())

    def validate(self, implication, attributes=None) -> PartialObject | None:
        assert attributes is not None, "Attributes must be provided"

        print(f'Validating {implication}')
        if self.solver.check([
            self._compile(implication.premise),
            z3.Not(self._compile(implication.conclusion))
        ]) == z3.unsat:
            print('Valid')
            return None

        model = self.solver.model()
        assignment = self._eval(model)
        positive, negative = set(), set()
        for a in attributes:
            if model.evaluate(a(self.zvars).holds()):
                positive.add(a)
            else:
                negative.add(a)
        print(f'Found counterexample: {assignment}')
        for var, val in assignment.items():
            if var.sort is SudokuSort.CELL:
                print(f'{var} = {val} contains {model.eval(self.value(val[0], val[1]))}')
            else:
                print(f'{var} = {val}')
        print(f'Positive: {", ".join(str(a) for a in positive)}')
        print(f'Negative: {", ".join(str(a) for a in negative)}\n')
        return PartialObject(model, positive, negative)

    def _domain_constraints(self, zvars):
        constraints = []
        for v in zvars.values():
            if isinstance(v, tuple):
                row, col = v
                constraints.extend([
                    row >= 0,
                    row < self.grid_size,
                    col >= 0,
                    col < self.grid_size
                ])
            else:
                constraints.append(1 <= v)
                constraints.append(v <= self.grid_size)
        return constraints

    def _sudoku_axioms(self):
        axioms = []

        # number range
        for r in range(self.grid_size):
            for c in range(self.grid_size):
                axioms.append(
                    z3.And(
                        self.value(r, c) >= 1,
                        self.value(r, c) <= self.grid_size
                    )
                )

        # rows
        for r in range(self.grid_size):
            axioms.append(
                z3.Distinct(
                    *[
                        self.value(r, c)
                        for c in range(self.grid_size)
                    ]
                )
            )

        # columns
        for c in range(self.grid_size):
            axioms.append(
                z3.Distinct(
                    *[
                        self.value(r, c)
                        for r in range(self.grid_size)
                    ]
                )
            )

        # blocks
        for br in range(self.block_size):
            for bc in range(self.block_size):
                block = []
                for r in range(
                    br * self.block_size,
                    (br + 1) * self.block_size
                ):
                    for c in range(
                        bc * self.block_size,
                        (bc + 1) * self.block_size
                    ):
                        block.append(self.value(r, c))
                axioms.append(z3.Distinct(*block))

        return axioms

    def _compile(self, atoms):
        return z3.And(
            *[
                #a.predicate.to_z3(self, [zvars[arg] for arg in a.arguments])
                a(self.zvars).holds()
                for a in atoms
            ]
        )

    def _eval(self, model):
        return {
            v:
            (
                model.eval(zv[0], model_completion=True).as_long(),
                model.eval(zv[1], model_completion=True).as_long()
            ) if v.sort is SudokuSort.CELL
            else model.eval(zv, model_completion=True).as_long()
            for v, zv in self.zvars.items()
        }


# Predicates

def z3_same_block_coords(i, j, block_size):
    return i / block_size == j / block_size


def z3_same_block(x, y, block_size):
    return z3.And(*(z3_same_block_coords(x[i], y[i], block_size)
                    for i in range(2)))


def z3_together(x, y, block_size):
    return z3.Or(
        x[0] == y[0],
        x[1] == y[1],
        z3_same_block(x, y, block_size)
    )


def z3predicates(block_size, expert):
    return [
        EvaluatablePredicate(
            'Peers',
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.And(
                z3.Or(x[0] != y[0], x[1] != y[1]),
                z3_together(x, y, block_size)
            )
        ),
        EvaluatablePredicate(
            'Apart',
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3.Not(z3_together(x, y, block_size))
        ),
        EvaluatablePredicate(
            'Same',
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: expert.value(x[0], x[1]) == expert.value(y[0], y[1])
        ),
        EvaluatablePredicate(
            'Different',
            2,
            sorts=(SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: expert.value(x[0], x[1]) != expert.value(y[0], y[1])
        ),
        EvaluatablePredicate(
            'Contains',
            2,
            sorts = (SudokuSort.CELL, SudokuSort.NUMBER),
            function=lambda c, n: expert.value(c[0], c[1]) == n
        ),
        EvaluatablePredicate(
            'SameNumber',
            2,
            sorts = (SudokuSort.NUMBER, SudokuSort.NUMBER),
            function=lambda m, n: m == n
        ),
        EvaluatablePredicate(
            'DifferentNumbers',
            2,
            sorts = (SudokuSort.NUMBER, SudokuSort.NUMBER),
            function=lambda m, n: m != n
        ),
        EvaluatablePredicate(
            'SameBlock',
            2,
            sorts = (SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: z3_same_block(x, y, block_size)
        ),
        EvaluatablePredicate(
            'SameRow',
            2,
            sorts = (SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[0] == y[0]
        ),
        EvaluatablePredicate(
            'SameColumn',
            2,
            sorts = (SudokuSort.CELL, SudokuSort.CELL),
            function=lambda x, y: x[1] == y[1]
        )
    ]


# Exploration

def cell_exploration():
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        SortedVariable("w", SudokuSort.CELL)
    ]
    exploration_block_size = 2
    expert = Z3SudokuExpert(exploration_block_size, variables)
    exploration = RuleExploration(
        z3predicates(exploration_block_size, expert)[:4],
        variables,
        expert,
        substitutions=True,
        evaluate_all=True
    )
    exploration.run()
    return exploration.base


def cell_number_exploration():
    variables = [
        SortedVariable("x", SudokuSort.CELL),
        SortedVariable("y", SudokuSort.CELL),
        SortedVariable("z", SudokuSort.CELL),
        #SortedVariable("u", SudokuSort.CELL),
        SortedVariable("n", SudokuSort.NUMBER),
        SortedVariable("m", SudokuSort.NUMBER),
        #SortedVariable("l", SudokuSort.NUMBER),
        #SortedVariable("k", SudokuSort.NUMBER)
    ]
    exploration_block_size = 2
    expert = Z3SudokuExpert(exploration_block_size, variables)
    predicates = z3predicates(exploration_block_size, expert)
    exploration = RuleExploration(
        (
            predicates[0], # Peers
            predicates[1], # Apart
            predicates[2], # Same
            predicates[3], # Different
            predicates[4], # Contains
            predicates[5], # SameNumber
            predicates[6], # DifferentNumbers
            # predicates[7], # SameBlock
            predicates[8], # SameRow
            predicates[9]  # SameColumn
        ),
        variables,
        expert,
        substitutions=True,
        evaluate_all=True
    )
    exploration.run()
    return exploration.base


if __name__ == "__main__":
    start_time = time.perf_counter()
    # profiler = cProfile.Profile()
    # profiler.enable()
    # base = cell_exploration()
    base = cell_number_exploration()
    # profiler.disable()
    end_time = time.perf_counter()

    elapsed = end_time - start_time
    print(
        f"\nExploration completed in {elapsed:.4f} seconds "
        f"({elapsed / 60:.2f} minutes)."
    )
    print()

    print(f'Accepted {len(base.accepted_implications)} implications:\n')
    theory = ImplicationTheory(base.implications)
    for implication in base.accepted_implications:
        simplified = theory.simplify(implication)
        for atom in simplified.premise:
            print(atom)
        print('-' * 20)
        if len(implication.premise | implication.conclusion) == len(base.attributes):
            print('No way\n')
            continue
        for atom in simplified.conclusion:
            print(atom)
        print()
    print()

    # stats = pstats.Stats(profiler).sort_stats("cumulative")
    # stats.print_stats(25)  # Print top 25 slowest functions
