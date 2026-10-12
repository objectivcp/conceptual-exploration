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
- **Theorem-Proving Oracle (`VampireExpert`)**: Proves implications in equational logic with the Vampire theorem prover and refutes them with finite counterexamples of any size or with free magmas over the premise, which are usually infinite.
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

With `--expert vampire`, questions the pool does not refute go to the [Vampire](https://vprover.github.io) theorem prover (installed separately, e.g. `brew install vampire`). It tries to prove the implication (`--vampire-prove-time-limit`, default `10` seconds) and then, briefly, to find a counterexample of any size (`--vampire-quick-model-time-limit`, default `1`). Failing both, it decides each law on its own for the free magma over the premise, whose elements are terms modulo the equations the premise derives: that magma, usually infinite, refutes the implication when a law of the conclusion is not derivable, and the implication is proved when every law of the conclusion is. Otherwise it searches for a counterexample again, to each law of the conclusion not proved, separately and in parallel (`--vampire-model-time-limit`, default `10`). The laws of the conclusion it proves are then accepted; the rest is left as an open question if Vampire shows the implication false, and accepted as `[UNCONFIRMED]` otherwise. Objects are completed only with background and confirmed implications. When a later object refutes an unconfirmed implication, which has steered the enumeration since it was accepted, the exploration resumes at the question it was accepted at, keeping what was accepted before, the confirmed implications found after, and every object; the refuted implication is reported and dropped. The search sizes and solver budget above apply to the default `z3` expert only:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --expert vampire
```

With `--background-order N`, implications derivable by equational reasoning are given to the exploration as background knowledge (one-variable equations only). The rules are multiplying both sides by the same term from the same side, substituting a term for the variable, and replacing a subterm by an equivalent one, applied through equations of at most `N` operations. `--background-premise-size K` (default `2`) bounds their premises; `0` computes the canonical basis of everything derivable instead, which is slower. `--background-transient-order M` lets a single multiplication or substitution reach equations of up to `M` operations, as long as rewriting with derived equations brings the result back within `N`:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --background-order 4 --background-transient-order 10
```

Magmas found earlier, such as the `magmas.json` of saved results, can be reused. `--seed-magmas PATH...` adds them to the expert's pool, which is checked for a counterexample before the solver searches. `--seed-context PATH...` instead evaluates them on every equation and adds them to the context before the exploration starts, dropping those whose rows the others account for, so that no question they refute is asked:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --seed-context explorations/equational_theories/results/1var_order4_sizes1-6/magmas.json
```

Each run saves its log (`exploration.log`), its implication theory with the source of every implication (`implications.txt`, `implications.json`) together with the open questions, and its context (`magmas.json`, `free_magmas.json`, `context.cxt` with the objects whose rows are complete, and `partial_context.cxt` with every object, `?` marking the equations not known to hold or fail) to a new directory under `results/` named after the equations file and the starting time, or to `--results-dir PATH`.

Or open the interactive Jupyter notebook:

```bash
jupyter notebook explorations/equational_theories/explore.ipynb
```
