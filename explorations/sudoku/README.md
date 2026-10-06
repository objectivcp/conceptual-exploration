# Sudoku Conceptual Exploration

This exploration project applies Formal Concept Analysis (FCA), Attribute Exploration, and First-Order Rule Exploration to the logic and constraints of **Sudoku**.

## Overview

Sudoku can be modeled conceptually at three levels:

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

3. **Deduction Rules on Partial Grids (SAT-based)**:
   - Objects are partial 4x4 grids with at least one completion. `Forced(x, n)` says that every completion has `n` in `x`, `Excluded(x, n)` that none does, so the rules found are deduction techniques such as naked and hidden singles.
   - `PartialGridExpert` enumerates the 288 solved 4x4 grids to decide these predicates; 9x9 grids have too many.
   - Presets pick the variables and predicates: `cell` (one cell, four digits), `row`, `column` and `block` (the four cells of a unit), and `units` (three cells, all of the geometry).

## Features

- **PySAT Reduction & Solver**: Functions `sudoku2sat`, `solve_sudoku`, and `assemble_solution` for flexible puzzle solving and verification.
- **SAT Expert (`SudokuExpert`)**: Verifies candidate implications and provides full/partial satisfying Sudoku grids as counterexamples.
- **Symmetry Group**: Generators for digit permutations, 90°/180°/270° rotations, reflections, and compositions.
- **Z3 Rule Expert (`Z3SudokuExpert`)**: SMT-based first-order verification with background Sudoku axioms, selected with `--expert z3`.
- **SAT Rule Expert (`SatSudokuRuleExpert`)**: Complete SAT-based verification of first-order rules at any block size; the default expert of the rule exploration, also used by `check_rules` to test rules across grid sizes.
- **Partial-Grid Expert (`PartialGridExpert`)**: SAT-based verification of rules about what follows from the givens of a partial 4x4 grid.
- **First-Order Predicates**: Predicate library for relational exploration over cells and numbers.

## Quick Start

### Run the CLI Exploration Script

Run first-order relational rule exploration:
```bash
python explorations/sudoku/explore.py --mode rule
```

`--full` explores three cell and two number variables instead of two cells, and `--no-background` drops the background implications, so the exploration rediscovers them too. `--check-block-size K` sets the block size the accepted rules are re-checked on (default 3, or 2 when exploring 9x9 grids; 0 skips the check), and `--expert z3` answers the questions with Z3 instead of the SAT expert.

Run the exploration of deduction rules on partial 4x4 grids, for every preset or, with `--preset`, for one:
```bash
python explorations/sudoku/explore.py --mode partial --preset row
```

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
