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
- **Automated Counterexample Oracle (`MagmaExpert`)**: Checks candidate implications against a catalog of standard finite magmas (cyclic groups, projections, tournaments, boolean magmas), then searches for a counterexample Cayley table with the **Z3 SMT solver**, representing the operation as an uninterpreted function over the finite domain of each candidate size $n$.
- **Unconfirmed Results**: A query whose per-size solver budget runs out was neither refuted nor decided, so its implication is accepted but reported `[UNCONFIRMED]` instead of being presented as verified.
- **Canonical Implication Basis**: Computes the minimal Duquenne–Guigues implication basis for equational theories.

## Quick Start

Run the exploration script:

```bash
python explorations/equational_theories/explore.py
```

The per-magma-size solver budget is configurable with `--z3-timeout-ms` (default `5000`; `0` or less runs unbounded):

```bash
python explorations/equational_theories/explore.py --z3-timeout-ms 500
```

A tighter budget trades open questions for speed rather than changing the answer. On a full run, `500` finishes in roughly 17 s and leaves 4 implications `[UNCONFIRMED]`, while the `5000` default takes roughly 27 s and leaves 2 — both deriving the same 27 accepted implications. Running unbounded removes the flagging entirely, at the cost of a few pathological size-5 queries that can each take a minute or more.

Progress reporting is controlled with `--report-every` (default `20`; `1` shows every question the expert is asked, `0` or less prints nothing):

```bash
python explorations/equational_theories/explore.py --report-every 1
```

Or open the interactive Jupyter notebook:

```bash
jupyter notebook explorations/equational_theories/explore.ipynb
```
