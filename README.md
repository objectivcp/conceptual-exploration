# Conceptual Exploration

[![Python Version](https://img.shields.io/badge/python-3.10%2B-blue.svg)](https://www.python.org/downloads/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](https://opensource.org/licenses/MIT)

**`conceptual-exploration`** is a Python library for interactive knowledge discovery and formal theory building based on **Formal Concept Analysis (FCA)**. It provides implementations of:

- **Attribute Exploration** — discovering the canonical (Duquenne–Guigues) implication basis for propositional attributes through interactive expert queries and counterexample refutations.
- **First-Order Rule Exploration** — extending attribute exploration to relational and first-order domains with predicates, typed/sorted variables, and automated symmetry/substitution reductions.

---

## Table of Contents

- [Key Features](#key-features)
- [Background: Formal Concept Analysis](#background-formal-concept-analysis)
- [Installation](#installation)
- [Architecture & Core Concepts](#architecture--core-concepts)
- [Quick Start](#quick-start)
  - [1. Attribute Exploration](#1-attribute-exploration)
  - [2. First-Order Rule Exploration](#2-first-order-rule-exploration)
  - [3. Loading Formal Contexts from `.cxt` Files](#3-loading-formal-contexts-from-cxt-files)
- [Symmetries & Background Knowledge](#symmetries--background-knowledge)
- [Included Examples](#included-examples)
- [Testing](#testing)
- [License](#license)

---

## Key Features

- **NextClosure Algorithm**: Ganter's NextClosure algorithm for lectically ordered enumeration of closed sets and premise candidate generation.
- **Attribute Exploration Engine**: Iterative question-and-answer workflow between the exploration engine and a domain expert/oracle (human, SAT/SMT solver, or dataset).
- **First-Order Rule Exploration (`RuleExploration`)**: Native support for relational signatures, predicates, and sorted variables.
- **Symmetry & Substitution Invariance**: Automatic generation of variable symmetries and variable identification/substitutions to prune redundant queries and map learned implications.
- **Partial Formal Contexts**: First-class handling of three-valued logic (positive, negative, and unknown attribute values) via `PartialContext` and `PartialObject`.
- **Burmeister `.cxt` Format Support**: Read and parse standard Formal Concept Analysis context files.
- **Implication Theory Management**: Simplification of implication premises, entailment checks, semantic closure computations, and source tracking (confirmed, background, mapped).

---

## Background: Formal Concept Analysis

**Attribute Exploration** (Bernhard Ganter, 1984) is a semi-automated knowledge acquisition technique in Formal Concept Analysis. Given a set of attributes and a domain of interest:
1. The exploration engine proposes hypothetical implications of the form $P \to C$ (premise implies conclusion).
2. A domain **Expert** evaluates the implication:
   - If the implication is valid, the expert confirms it and it is added to the implication basis.
   - If invalid, the expert provides a **counterexample** (an object that satisfies $P$ but violates at least one attribute in $C$).
3. The process terminates with a minimal, complete implication basis that describes the domain without asking redundant questions.

**Rule Exploration** generalizes this paradigm from propositional attributes to first-order Horn-like relational rules over predicates and variables.

---

## Installation

### Requirements
- Python >= 3.10

### Basic Installation

Clone the repository and install in editable mode:

```bash
git clone https://github.com/username/conceptual-exploration.git
cd conceptual-exploration
pip install -e .
```

### Optional Dependencies

Install extra dependencies for development, tests, or examples:

```bash
# For running tests
pip install -e ".[test]"

# For development (pytest, z3-solver)
pip install -e ".[dev]"

# For examples and Jupyter notebooks (z3-solver, jupyter, python-sat)
pip install -e ".[examples]"
pip install python-sat
```

---

## Architecture & Core Concepts

```
src/conceptual_exploration/
├── algorithms/
│   ├── closure.py             # Abstract ClosureOperator protocol
│   └── next_closure.py        # NextClosure lectic enumeration algorithm
├── core/
│   ├── context.py             # PartialObject and PartialContext (with CXT parser)
│   ├── implication.py         # Implication dataclass and respectedness checks
│   └── theory.py              # ImplicationTheory for closure & simplification
├── experts/
│   └── base.py                # Abstract Expert interface (validate method)
├── exploration/
│   ├── base.py                # ExplorationBase with context, mappings & implications
│   ├── attribute.py           # AttributeExploration coordinator
│   ├── rule.py                # RuleExploration first-order coordinator
│   └── state.py               # ExplorationState tracking queries and statistics
└── logic/
    ├── atom.py                # Atom, GroundedAtom, and atoms_over generator
    ├── predicate.py           # Predicate, EvaluatablePredicate, and Notation
    ├── symmetries.py          # Variable permutations and substitutions
    └── variable.py            # Variable, SortedVariable, and Sort enum
```

### Key Classes

| Class | Description |
|---|---|
| `AttributeExploration` | Orchestrates standard attribute exploration over a set of attributes and an `Expert`. |
| `RuleExploration` | Orchestrates first-order rule exploration given predicates, variables, and an `Expert`. |
| `ExplorationBase` | Manages attributes, background implications, partial contexts, and symmetry mappings. |
| `Expert` | Abstract base class for domain oracles implementing `validate(implication, attributes)`. |
| `Implication` | Represents a rule of the form $\text{Premise} \to \text{Conclusion}$. |
| `ImplicationTheory` | Maintains a set of implications, computes closures, checks entailment, and simplifies rules. |
| `PartialObject` | Represents a concrete or counterexample object with `positive` and `negative` attribute sets. |
| `PartialContext` | Formal context storing objects and attributes, capable of loading `.cxt` files. |
| `Predicate` / `EvaluatablePredicate` | Relational symbol with fixed arity, sort constraints, and optional evaluation function. |
| `Variable` / `SortedVariable` | Variables used in first-order relational atoms. |

---

## Quick Start

### 1. Attribute Exploration

Here is a minimal example discovering arithmetic relationships over small integers:

```python
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.attribute import AttributeExploration
from conceptual_exploration.exploration.base import ExplorationBase


class NamedPredicate:
    def __init__(self, name, predicate):
        self.name = name
        self.predicate = predicate

    def __call__(self, n):
        return self.predicate(n)

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def __lt__(self, other):
        return self.name < other.name


class IntegerExpert(Expert):
    def __init__(self, domain, predicates):
        self.domain = domain
        self.predicates = predicates

    def validate(self, implication, attributes=None):
        for n in self.domain:
            # Check if integer n satisfies the premise but violates conclusion
            if all(p(n) for p in implication.premise) and any(not c(n) for c in implication.conclusion):
                positives = {p for p in self.predicates if p(n)}
                negatives = set(self.predicates) - positives
                return PartialObject(n, positives, negatives)
        return None  # Implication holds across domain


attributes = [
    NamedPredicate("even", lambda n: n % 2 == 0),
    NamedPredicate("odd", lambda n: n % 2 == 1),
    NamedPredicate("divisible_by_4", lambda n: n % 4 == 0),
    NamedPredicate("divisible_by_6", lambda n: n % 6 == 0),
]

base = ExplorationBase(attributes=attributes)
expert = IntegerExpert(domain=range(1, 100), predicates=attributes)
exploration = AttributeExploration(base, expert)

exploration.run()

print("Discovered Implications:")
for impl in base.accepted_implications:
    print(f"  {impl}")
```

### 2. First-Order Rule Exploration

Explore relational rules over variables $x, y, z$ and binary order/equality predicates:

```python
from itertools import product
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.predicate import EvaluatablePredicate, Notation
from conceptual_exploration.logic.variable import Variable


class NumberRelationalExpert(Expert):
    def __init__(self, domain, variables):
        self.domain = tuple(domain)
        self.variables = variables

    def validate(self, implication, attributes=None):
        for values in product(self.domain, repeat=len(self.variables)):
            assignment = dict(zip(self.variables, values))
            # Verify premise holds for assignment
            if all(atom(assignment).holds() for atom in implication.premise):
                for atom in implication.conclusion:
                    if not atom(assignment).holds():
                        positive = {a for a in implication.premise}
                        return PartialObject(tuple(assignment.items()), positive, {atom})
        return None


predicates = [
    EvaluatablePredicate("<", 2, function=lambda a, b: a < b, notation=Notation.INFIX),
    EvaluatablePredicate("=", 2, function=lambda a, b: a == b, notation=Notation.INFIX),
]
variables = [Variable("x"), Variable("y"), Variable("z")]

expert = NumberRelationalExpert(domain=range(-5, 6), variables=variables)
exploration = RuleExploration(predicates, variables, expert, substitutions=True)
exploration.run()

print(f"Accepted {len(exploration.base.accepted_implications)} first-order rules:")
for impl in exploration.base.accepted_implications:
    print(f"  {impl}")
```

### 3. Loading Formal Contexts from `.cxt` Files

You can initialize contexts from standard Burmeister `.cxt` files:

```python
from conceptual_exploration.core.context import PartialContext

# Load context from file
context = PartialContext.from_cxt("examples/test.cxt")

print(f"Loaded {len(context.objects)} objects and {len(context.attributes)} attributes.")
```

---

## Symmetries & Background Knowledge

In many domains, rules are invariant under symmetries (e.g. geometric rotations, renaming of symmetric variables, or digit permutations in Sudoku). 

`conceptual-exploration` allows passing mappings/symmetries to `ExplorationBase`:
- Whenever an implication is accepted, its symmetric transformations are automatically derived and accepted without asking the expert.
- Whenever a counterexample is provided, its symmetric counterparts are generated in the background context.

```python
base = ExplorationBase(
    attributes=attributes,
    background_implications=background_rules,
    mappings=symmetry_mappings,
)
```

For first-order rule exploration, variable symmetries (permutations and non-injective variable substitutions) are configured automatically via `substitutions=True` in `RuleExploration`.

---

## Included Examples

The `examples/` directory contains complete demonstrations across various domains:

- `numbers_exploration.py`: Propositional exploration of prime numbers, factorials, parity, and divisibility.
- `numbers_rule_exploration.py`: First-order exploration of arithmetic inequalities and signs.
- `sudoku_exploration.ipynb`: SAT-based (PySAT) Sudoku exploration demonstrating symmetry mappings (rotations and digit permutations) and reduction to CNF formulas.
- `sudoku_rule_exploration.py`: First-order rule exploration of Sudoku logic using the **Z3 SMT solver** with multi-sorted variables (`SudokuSort.CELL` and `SudokuSort.NUMBER`).
- `simulated_exploration.py`: Automated benchmarking and simulated exploration over existing `.cxt` formal contexts.
- `implication_theories_exploration.py`: Meta-exploration of implication theories and inference rules.

---

## Testing

Run the test suite using `pytest`:

```bash
pytest
```

Or using the built-in test runner:

```bash
PYTHONPATH=src python3 -c "import tests.test_enumerator as t; t.test_next_closure_one(); t.test_next_closure_complete(); t.test_all_generated_sets_are_closed(); t.test_no_duplicates(); t.test_first_element(); t.test_last_element(); t.test_lectic_order(); print('All tests passed!')"
```

---

## License

This project is licensed under the MIT License — see the [pyproject.toml](pyproject.toml) file for details.
