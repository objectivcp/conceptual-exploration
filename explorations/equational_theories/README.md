# Equational Theories Project (ETP) — Magma Exploration

This exploration project applies Formal Concept Analysis (FCA) and Attribute Exploration to the **Equational Theories Project (ETP)**.

## Background

The **Equational Theories Project (ETP)** explores the complete landscape of implications and non-implications among equational laws on magmas (sets equipped with a single binary operation $*$).

Given a signature with binary operation $*$ and variables $x, y, z, \dots$, an equational law $L = R$ is an identity universally quantified over all occurring variables. Examples include:
- **Commutativity (Eq 43)**: $x * y = y * x$
- **Associativity (Eq 381)**: $(x * y) * z = x * (y * z)$
- **Idempotence (Eq 3)**: $x = x * x$
- **Medial / Entropic (Eq 4512)**: $(x * y) * (z * w) = (x * z) * (y * w)$
- **Steiner Law 1 (Eq 4687)**: $x * (x * y) = y$

## Features

- **AST Representation & Evaluation**: Expressive term trees (`Term`, `Var`, `Op`) and equations (`Equation`) evaluated against finite Cayley tables.
- **Duality Symmetries**: Anti-automorphism mappings $(x * y)^{\text{op}} = y^{\text{op}} * x^{\text{op}}$ integrated into `ExplorationBase` to reduce redundant expert queries by up to 50%.
- **Automated Counterexample Oracle (`MagmaExpert`)**: Checks candidate implications against a catalog of standard finite magmas (cyclic groups, projections, tournaments, boolean magmas) and dynamically searches for small Cayley table counterexamples (order $n \le 3$).
- **Canonical Implication Basis**: Computes the minimal Duquenne–Guigues implication basis for equational theories.

## Quick Start

Run the exploration script:

```bash
python explorations/equational_theories/explore.py
```

Or open the interactive Jupyter notebook:

```bash
jupyter notebook explorations/equational_theories/explore.ipynb
```
