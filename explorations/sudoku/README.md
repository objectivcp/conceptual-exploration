# Sudoku Conceptual Exploration

This exploration project applies Formal Concept Analysis (FCA), Attribute Exploration, and First-Order Rule Exploration to the logic and constraints of **Sudoku**.

## Overview

Sudoku can be modeled conceptually at three levels:

1. **Propositional Attribute Exploration (SAT-based)**:
   - Attributes are cell value assignments `(row, column, number)`.
   - Uses **PySAT** to encode standard Sudoku rules into CNF and answer expert queries with valid grid configurations.
   - Takes the rules of Sudoku as background (`get_sudoku_background_implications`), so the accepted implications are the deductions they lead to.
   - Leverages the full **symmetry group** of 4x4 grids to automatically propagate accepted implications and counterexamples, reducing expert queries.

2. **First-Order Relational Rule Exploration (SAT-based)**:
   - Uses multi-sorted variables (`SudokuSort.CELL` for coordinates and `SudokuSort.NUMBER` for cell values).
   - Uses a **PySAT** expert, or optionally the **Z3 SMT solver**, to reason about relational predicates: the cell equivalences `SameCell`, `SameRow`, `SameColumn`, `SameBlock`, `SameBand`, `SameStack` and `Same` (equal values), together with `Contains` and `SameNumber`. The derived predicates `Peers`, `Apart`, `Different` and `DifferentNumbers` remain available but are not explored by default.
   - Declares which predicates are symmetric, reflexive, irreflexive or complementary, so only one atom of each symmetric pair is explored and atoms such as `Same(x, x)` are not.
   - Takes as background what holds in any grid whatever its digits (equivalence laws, how the regions nest, one value per cell), so the accepted rules are the ones the Sudoku constraints add.
   - Re-checks the accepted rules on grids of another block size (9x9 by default), marking those that hold only on the explored size.

3. **Deduction Techniques (SAT-based)**:
   - Solved grids with `NotContains(x, n)`, the complement of `Contains`, and the Confined predicates: `n`'s place in `x`'s block lies in `x`'s row or column (`ConfinedToRowInBlock`, `ConfinedToColumnInBlock`), or its place in `x`'s row or column lies in `x`'s block (`ConfinedToBlockInRow`, `ConfinedToBlockInColumn`).
   - Read on a partial grid as holding in all its completions, these predicates give it exactly the properties its completions share, so the rules found on solved grids are deduction techniques: naked and hidden singles, locked candidates.
   - The shipped configurations pick the variables and predicates: `solved-cell` (one cell, four digits), `solved-row`, `solved-column` and `solved-block` (the four cells of a unit), `solved-units` (three cells, all of the geometry), `solved-full` (four cells, all of the geometry), and `solved-locked` (two cells with the Confined predicates). `solved-full` explores the geometry alone first and adds its rules to the background, so that only rules about the digits are reported.

4. **Partial Grids with `Possible` (SAT-based, 4x4)**:
   - `grid = "partial"`: objects are partial 4x4 grids with at least one completion. `Forced(x, n)` holds if every completion has `n` in `x`, `Excluded(x, n)` if none does, and `Possible(x, n)`, the complement of `Excluded`, if some does. With `Possible`, a partial grid is no longer determined by what its completions share.
   - `PartialGridExpert` decides these predicates by listing the 288 solved 4x4 grids.
   - The shipped configurations `partial-cell`, `partial-row`, `partial-units`, `partial-two-digits` and `partial-rows-columns` set `compare_without = ["Possible"]`: the runner explores again without `Possible` and marks `[NEW]` the rules that this theory does not entail classically. Only `partial-row` has one, and `partial-rows-columns` shows that it follows once columns are in the vocabulary.

## Features

- **PySAT Reduction & Solver**: Functions `sudoku2sat`, `solve_sudoku`, and `assemble_solution` for flexible puzzle solving and verification.
- **SAT Expert (`SudokuExpert`)**: Verifies candidate implications and provides full/partial satisfying Sudoku grids as counterexamples.
- **Symmetry Group**: The 3072 symmetries of 4x4 grids: band, row, stack and column permutations, transposition, and digit relabelling; rotations and reflections are among them.
- **Z3 Rule Expert (`Z3SudokuExpert`)**: SMT-based first-order verification with background Sudoku axioms, selected with `expert = "z3"`.
- **SAT Rule Expert (`SatSudokuRuleExpert`)**: Complete SAT-based verification of first-order rules at any block size, including the Confined predicates; the default expert of the rule exploration, also used by `check_rules` to test rules across grid sizes.
- **First-Order Predicates**: Predicate library for relational exploration over cells and numbers.

## Quick Start

### Run the CLI Exploration Script

Each exploration is described by a TOML configuration file. Run one shipped in `configs/` by name, or your own by path; several run in turn:
```bash
python explorations/sudoku/explore.py solved-row
python explorations/sudoku/explore.py my-exploration.toml
```

A configuration says which grids to explore and how:
```toml
grid = "solved"           # "solved", "partial" or "propositional"
block_size = 2            # 3 for 9x9 grids
cells = ["w", "x", "y", "z"]
numbers = ["n"]
predicates = ["SameCell", "DifferentCells", "SameRow", "Contains", "NotContains"]
background = true         # what holds in any grid
geometry_first = false    # explore the geometry first and add it to the background
classical = true          # drop the rules that follow classically from the others
compare_without = []      # mark [NEW] the rules not entailed when these are left out
expert = "sat"            # solved grids: or "z3", which lacks the Confined predicates
check_block_size = 3      # solved grids: re-check the rules there; 0 skips
```

`grid = "propositional"` explores (row, column, digit) attributes and takes only `block_size`, `background` and `symmetries`. Settings that cannot be run, such as a Confined predicate with the Z3 expert or a misspelt key, are reported before anything runs.

The shipped configurations are `solved-pairs`, `solved-triples` and `solved-quads` (the rules of Sudoku), `solved-cell`, `solved-row`, `solved-column`, `solved-block`, `solved-units`, `solved-full` and `solved-locked` (deduction techniques), `partial-cell`, `partial-row`, `partial-units`, `partial-two-digits` and `partial-rows-columns` (partial grids with `Possible`), and `propositional`.

By default (`classical`), rules that follow from the others in propositional logic, with complements such as `Possible` and `Excluded` total, are dropped; contrapositive forms go first, so that rules concluding about digits are kept.

`--block-size K`, `--no-background` and `--no-classical` override the configuration, and `--output PATH` also writes the rules to a file, after the configuration that produced them.

### Interactive Jupyter Notebook

Launch the interactive notebook demonstrating both exploration techniques:
```bash
jupyter notebook explorations/sudoku/explore.ipynb
```
