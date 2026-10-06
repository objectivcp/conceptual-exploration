"""Conceptual Exploration of Sudoku Rules and Constraints.

This script demonstrates how Formal Concept Analysis and Attribute/Rule Exploration
can discover the logic of Sudoku:
1. First-Order Relational Rule Exploration using the Z3 SMT solver
   (with multi-sorted variables `SudokuSort.CELL` and `SudokuSort.NUMBER`).
2. Propositional Attribute Exploration using PySAT and symmetry mappings
   (digit permutations, rotations, and reflections).
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import AttributeExploration
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.exploration.base import ExplorationBase
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku.sudoku import (
    CELL_EQUIVALENCES,
    PRIMITIVE_PREDICATES,
    SudokuExpert,
    SudokuSort,
    Z3SudokuExpert,
    get_sudoku_attributes,
    get_sudoku_symmetries,
    select_predicates,
    sudoku_background,
    z3predicates,
)


def run_sudoku_rule_exploration(
    block_size: int = 2,
    quick: bool = True,
    use_background: bool = True,
):
    """Run first-order relational rule exploration using Z3 SMT solver."""
    print("=" * 70)
    print(f"SUDOKU FIRST-ORDER RULE EXPLORATION (Block Size: {block_size}x{block_size})")
    print(f"Mode: {'Quick (2 Cell Variables)' if quick else 'Full (3 Cell + 2 Number Variables)'}")
    print("=" * 70)

    if quick:
        variables = [
            SortedVariable("x", SudokuSort.CELL),
            SortedVariable("y", SudokuSort.CELL),
        ]
        names = CELL_EQUIVALENCES
    else:
        variables = [
            SortedVariable("x", SudokuSort.CELL),
            SortedVariable("y", SudokuSort.CELL),
            SortedVariable("z", SudokuSort.CELL),
            SortedVariable("n", SudokuSort.NUMBER),
            SortedVariable("m", SudokuSort.NUMBER),
        ]
        names = PRIMITIVE_PREDICATES
    expert = Z3SudokuExpert(block_size, variables)
    selected_predicates = select_predicates(z3predicates(block_size, expert), names)
    background = (
        sudoku_background(selected_predicates, variables) if use_background else []
    )

    print(f"\nVariables ({len(variables)}):")
    for v in variables:
        print(f"  - {v.name}: {v.sort.name}")

    print(f"\nPredicates ({len(selected_predicates)}):")
    for p in selected_predicates:
        sort_names = tuple(s.name for s in p.sorts) if p.sorts else ()
        print(f"  - {p.name}{sort_names}")

    print(f"\nBackground Implications: {len(background)}")

    exploration = RuleExploration(
        selected_predicates,
        variables,
        expert,
        background=background,
        substitutions=True,
        evaluate_all=True,
    )

    print("\nStarting First-Order Rule Exploration...")
    start_time = time.perf_counter()
    exploration.run()
    elapsed = time.perf_counter() - start_time

    base = exploration.base
    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Time Elapsed:                 {elapsed:.2f}s")
    print(f"Total Base Attributes:        {len(base.attributes)}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"Total Implications in Theory: {len(base.implications.implications)}")

    theory = ImplicationTheory(base.implications)
    print("\nDiscovered Relational Rules (Simplified):")
    for idx, impl in enumerate(base.accepted_implications, start=1):
        simplified = theory.simplify(impl)
        premise_str = " {" + ", ".join(str(a) for a in simplified.premise) + "}" if simplified.premise else " Ø"
        concl_str = " {" + ", ".join(str(a) for a in simplified.conclusion) + "}"
        print(f"  [{idx}] {premise_str}  ==>  {concl_str}")

    return base


def run_sudoku_sat_exploration(block_size: int = 2, use_symmetries: bool = True):
    """Run propositional attribute exploration using PySAT solver and symmetries."""
    print("=" * 70)
    print(f"SUDOKU PROPOSITIONAL ATTRIBUTE EXPLORATION (Block Size: {block_size}x{block_size})")
    print(f"Symmetries Enabled: {use_symmetries}")
    print("=" * 70)

    attributes = get_sudoku_attributes(block_size)
    mappings = get_sudoku_symmetries(block_size) if use_symmetries else []

    print(f"\nAttributes: {len(attributes)} cell assignments (r, c, num)")
    print(f"Symmetry Mappings: {len(mappings)}")

    base = ExplorationBase(
        attributes=attributes,
        mappings=mappings,
    )
    expert = SudokuExpert(block_size)
    exploration = AttributeExploration(base, expert)

    print("\nStarting Propositional Attribute Exploration...")
    start_time = time.perf_counter()
    state = exploration.run()
    elapsed = time.perf_counter() - start_time

    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Time Elapsed:                 {elapsed:.2f}s")
    print(f"Total Questions Asked:        {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"Total Implications in Theory: {len(base.implications.implications)}")
    print(f"Discovered Objects/Configs:   {len(base.objects)}")

    return state, base


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Sudoku Conceptual Exploration")
    parser.add_argument(
        "--mode",
        choices=["rule", "sat", "both"],
        default="rule",
        help="Exploration mode to execute: rule (Z3 first-order) or sat (PySAT propositional)",
    )
    parser.add_argument(
        "--block-size",
        type=int,
        default=2,
        help="Sudoku block size (default: 2 for 4x4 grid)",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        default=True,
        help="Run fast rule exploration with cell variables (default: True)",
    )
    parser.add_argument(
        "--full",
        dest="quick",
        action="store_false",
        help="Run full multi-sorted rule exploration with cell and number variables",
    )
    parser.add_argument(
        "--no-background",
        dest="background",
        action="store_false",
        help=(
            "Explore without the background implications that hold in any grid "
            "(equivalence laws, how rows, columns, blocks, bands and stacks nest, "
            "one value per cell), so that these are rediscovered as well"
        ),
    )
    args = parser.parse_args()

    if args.mode in ("rule", "both"):
        run_sudoku_rule_exploration(
            block_size=args.block_size,
            quick=args.quick,
            use_background=args.background,
        )
    if args.mode in ("sat", "both"):
        run_sudoku_sat_exploration(block_size=args.block_size)
