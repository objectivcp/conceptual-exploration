# Sudoku Conceptual Exploration

This exploration project applies Formal Concept Analysis (FCA), Attribute Exploration, and First-Order Rule Exploration to the logic and constraints of **Sudoku**.

## Overview

Sudoku can be modeled conceptually at two levels:

1. **Propositional Attribute Exploration (SAT-based)**:
   - Attributes are cell value assignments `(row, column, number)`.
   - Uses **PySAT** to encode standard Sudoku rules into CNF and answer expert queries with valid grid configurations.
   - Leverages **Symmetry Mappings** (digit permutations, rotations, and reflections) to automatically propagate accepted implications and counterexamples, reducing expert queries.

2. **First-Order Relational Rule Exploration (SMT-based)**:
   - Uses multi-sorted variables (`SudokuSort.CELL` for coordinates and `SudokuSort.NUMBER` for cell values).
   - Uses the **Z3 SMT solver** to reason about relational predicates like `Peers`, `Apart`, `Same`, `Different`, `Contains`, `SameRow`, `SameColumn`, and `SameBlock`.
   - Automatically discovers domain axioms and deduction rules (e.g., cell peer relations, value uniqueness, row/column dependencies).

## Features

- **PySAT Reduction & Solver**: Functions `sudoku2sat`, `solve_sudoku`, and `assemble_solution` for flexible puzzle solving and verification.
- **SAT Expert (`SudokuExpert`)**: Verifies candidate implications and provides full/partial satisfying Sudoku grids as counterexamples.
- **Symmetry Group**: Generators for digit permutations, 90°/180°/270° rotations, reflections, and compositions.
- **Z3 Rule Expert (`Z3SudokuExpert`)**: High-performance SMT-based first-order verification with background Sudoku axioms.
- **First-Order Predicates**: Predicate library for relational exploration over cells and numbers.

## Quick Start

### Run the CLI Exploration Script

Run first-order relational rule exploration with Z3:
```bash
python explorations/sudoku/explore.py --mode rule
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
