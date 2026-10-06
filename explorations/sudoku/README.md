# Sudoku Conceptual Exploration

This exploration project applies Formal Concept Analysis (FCA), Attribute Exploration, and First-Order Rule Exploration to the logic and constraints of **Sudoku**.

## Overview

Sudoku can be modeled conceptually at two levels:

1. **Propositional Attribute Exploration (SAT-based)**:
   - Attributes are cell value assignments `(row, column, number)`.
   - Uses **PySAT** to encode standard Sudoku rules into CNF and answer expert queries with valid grid configurations.
   - Leverages **Symmetry Mappings** (digit permutations, rotations, and reflections) to automatically propagate accepted implications and counterexamples, reducing expert queries.

2. **First-Order Relational Rule Exploration (SAT-based)**:
   - Uses multi-sorted variables (`SudokuSort.CELL` for coordinates and `SudokuSort.NUMBER` for cell values).
   - Uses a **PySAT** expert, or optionally the **Z3 SMT solver**, to reason about relational predicates: the cell equivalences `SameCell`, `SameRow`, `SameColumn`, `SameBlock`, `SameBand`, `SameStack` and `Same` (equal values), together with `Contains` and `SameNumber`. The derived predicates `Peers`, `Apart`, `Different` and `DifferentNumbers` remain available but are not explored by default.
   - Declares which predicates are symmetric, reflexive, irreflexive or complementary, so only one atom of each symmetric pair is explored and atoms such as `Same(x, x)` are not.
   - Takes as background what holds in any grid whatever its digits (equivalence laws, how the regions nest, one value per cell), so the accepted rules are the ones the Sudoku constraints add.
   - Re-checks the accepted rules on grids of another block size (9x9 by default), marking those that hold only on the explored size.

## Features

- **PySAT Reduction & Solver**: Functions `sudoku2sat`, `solve_sudoku`, and `assemble_solution` for flexible puzzle solving and verification.
- **SAT Expert (`SudokuExpert`)**: Verifies candidate implications and provides full/partial satisfying Sudoku grids as counterexamples.
- **Symmetry Group**: Generators for digit permutations, 90°/180°/270° rotations, reflections, and compositions.
- **Z3 Rule Expert (`Z3SudokuExpert`)**: SMT-based first-order verification with background Sudoku axioms, selected with `--expert z3`.
- **SAT Rule Expert (`SatSudokuRuleExpert`)**: Complete SAT-based verification of first-order rules at any block size; the default expert of the rule exploration, also used by `check_rules` to test rules across grid sizes.
- **First-Order Predicates**: Predicate library for relational exploration over cells and numbers.

## Quick Start

### Run the CLI Exploration Script

Run first-order relational rule exploration:
```bash
python explorations/sudoku/explore.py --mode rule
```

`--full` explores three cell and two number variables instead of two cells, and `--no-background` drops the background implications, so the exploration rediscovers them too. `--check-block-size K` sets the block size the accepted rules are re-checked on (default 3, or 2 when exploring 9x9 grids; 0 skips the check), and `--expert z3` answers the questions with Z3 instead of the SAT expert.

Run propositional attribute exploration with PySAT and symmetries:
```bash
python explorations/sudoku/explore.py --mode sat
```

Or run both:
```bash
python explorations/sudoku/explore.py --mode both
```

### Interactive Jupyter Notebook

Launch the interactive notebook demonstrating both exploration techniques:
```bash
jupyter notebook explorations/sudoku/explore.ipynb
```
