"""Conceptual Exploration of Magmas in the Equational Theories Project (ETP).

This script demonstrates how Formal Concept Analysis and Attribute Exploration
can discover the canonical implication basis between equational laws over magmas
(sets equipped with a single binary operation `*`).

Background:
The Equational Theories Project (ETP) investigates the web of implications
and non-implications between equational laws on magmas.
Using conceptual exploration:
1. The exploration engine proposes candidate implications P => C (premises imply conclusions).
2. The `MagmaExpert` evaluates the implication by checking if all magmas satisfying P also satisfy C.
3. If an implication is false, the expert provides a finite counterexample Magma (with Cayley table).
4. Duality symmetries (the anti-automorphism (x * y)^op = y^op * x^op) are leveraged
   to automatically map implications and reduce expert queries.
"""

from __future__ import annotations

import sys
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
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert


def run_magma_exploration(use_duality_symmetry: bool = True):
    print("=" * 70)
    print("EQUATIONAL THEORIES PROJECT (ETP) — MAGMA EXPLORATION")
    print(f"Duality Symmetry Enabled: {use_duality_symmetry}")
    print("=" * 70)

    # Selected representative equational laws from ETP
    equations = [
        Equation.parse("x = y", name="Singleton / Degenerate", id=2),
        Equation.parse("x = (x * x)", name="Idempotence", id=3),
        Equation.parse("x = (x * y)", name="Left-Zero / Left-Absorption", id=4),
        Equation.parse("x = (y * x)", name="Right-Zero / Right-Absorption", id=5),
        Equation.parse("x = ((x * y) * x)", name="Central-Identity", id=6),
        Equation.parse("x = (x * (y * x))", name="Left-Central-Identity", id=23),
        Equation.parse("((x * x) * y) = (x * (x * y))", name="Left-Alternative", id=7),
        Equation.parse("((y * x) * x) = (y * (x * x))", name="Right-Alternative", id=8),
        Equation.parse("((x * y) * x) = (x * (y * x))", name="Flexible", id=9),
        Equation.parse("(x * y) = (y * x)", name="Commutativity", id=43),
        Equation.parse("(x * y) = (x * (x * y))", name="Left-Idempotent-Composition", id=46),
        Equation.parse("((y * x) * x) = (y * x)", name="Right-Idempotent-Composition", id=47),
        Equation.parse("((x * y) * z) = (x * (y * z))", name="Associativity", id=381),
        Equation.parse("((x * y) * (z * w)) = ((x * z) * (y * w))", name="Medial / Entropic", id=4512),
        Equation.parse("(x * (x * y)) = y", name="Steiner Law 1", id=4687),
        Equation.parse("((y * x) * x) = y", name="Steiner Law 2", id=4688),
    ]

    print(f"\nExploring {len(equations)} Equational Laws:")
    for eq in equations:
        print(f"  - {eq}")

    # Set up duality mapping if symmetry is enabled
    mappings = []
    if use_duality_symmetry:
        duality_map = ETP.get_duality_mapping(equations)
        mappings.append(duality_map)

    base = ExplorationBase[Magma, Equation](
        attributes=equations,
        mappings=mappings,
    )
    expert = MagmaExpert(attributes=equations, max_search_size=3)
    exploration = AttributeExploration(base, expert, evaluate_all=True)

    print("\nStarting Attribute Exploration...")
    state = exploration.run()

    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Total Questions Asked:        {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"Total Implications in Theory: {len(base.implications.implications)}")
    print(f"Counterexample Magmas Found:  {len(state.counterexamples)}")

    # Display canonical simplified implication basis
    theory = ImplicationTheory(base.implications)
    print("\nDiscovered Canonical Implication Basis (Simplified):")
    for idx, impl in enumerate(base.accepted_implications, start=1):
        simplified = theory.simplify(impl)
        premise_str = " {" + ", ".join(eq.name or str(eq) for eq in simplified.premise) + "}" if simplified.premise else " Ø"
        concl_str = " {" + ", ".join(eq.name or str(eq) for eq in simplified.conclusion) + "}"
        print(f"  [{idx}] {premise_str}  ==>  {concl_str}")

    # Display discovered counterexample magmas
    print("\nSample Counterexample Magmas Generated:")
    unique_magmas = []
    seen = set()
    for cex in state.counterexamples:
        m = cex.object.original if hasattr(cex.object, "original") else cex.object
        key = (m.size, m.table)
        if key not in seen:
            seen.add(key)
            unique_magmas.append(m)

    for i, m in enumerate(unique_magmas[:5], start=1):
        print(f"\nCounterexample #{i}:")
        print(m)

    return state, base


if __name__ == "__main__":
    run_magma_exploration(use_duality_symmetry=True)
