# Equational Theories Project (ETP) — Magma Exploration

This exploration project applies Formal Concept Analysis (FCA) and Attribute Exploration to the **Equational Theories Project (ETP)**.

## Background

The **Equational Theories Project (ETP)** explores the complete landscape of implications and non-implications among equational laws on magmas (sets equipped with a single binary operation $*$).

Given a signature with binary operation $*$ and variables $x, y, z, \dots$, an equational law $L = R$ is an identity universally quantified over all occurring variables. Examples include:
- **Commutativity (Eq 43)**: $x * y = y * x$
- **Associativity (Eq 4512)**: $(x * y) * z = x * (y * z)$
- **Idempotence (Eq 3)**: $x = x * x$
- **Medial / Entropic**: $(x * y) * (z * w) = (x * z) * (y * w)$
- **Steiner Law 1 (Eq 16)**: $x * (x * y) = y$

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

The equations explored as attributes are listed in [`equations.json`](equations.json); each entry has an `equation` string and optional `name` and `id` fields, and the set must be closed under duality. Use `--equations` to explore a different file:

```bash
python explorations/equational_theories/explore.py --equations my_equations.json
```

The per-magma-size solver budget is configurable with `--z3-timeout-ms` (default `30000`; `0` or less runs unbounded):

```bash
python explorations/equational_theories/explore.py --z3-timeout-ms 500
```

A tighter budget trades open questions for speed rather than changing the answer: a query that runs out of time is reported `[UNCONFIRMED]` instead of being decided, so a smaller budget finishes sooner and leaves more implications open. Running unbounded removes the flagging entirely, at the cost of a few pathological searches at the larger magma sizes, which can dominate the running time.

The solver searches for counterexample magmas of sizes `--min-search-size` to `--max-search-size` (defaults `1` and `6`); the built-in pool of small standard magmas is checked first regardless:

```bash
python explorations/equational_theories/explore.py --min-search-size 4 --max-search-size 7
```

Progress reporting is controlled with `--report-every` (default `1`, showing every question the expert is asked; `0` or less prints nothing):

```bash
python explorations/equational_theories/explore.py --report-every 1
```

With `--background-order N`, implications derivable by equational reasoning are given to the exploration as background knowledge (one-variable equations only). The rules are multiplying both sides by the same term from the same side, substituting a term for the variable, and replacing a subterm by an equivalent one, applied through equations of at most `N` operations. `--background-premise-size K` (default `2`) bounds their premises; `0` computes the canonical basis of everything derivable instead, which is slower. `--background-transient-order M` lets a single multiplication or substitution reach equations of up to `M` operations, as long as rewriting with derived equations brings the result back within `N`:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --background-order 4 --background-transient-order 10
```

Or open the interactive Jupyter notebook:

```bash
jupyter notebook explorations/equational_theories/explore.ipynb
```
