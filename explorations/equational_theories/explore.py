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
5. Queries where the solver runs out of its per-size budget are accepted but
   flagged [UNCONFIRMED], since they were neither refuted nor decided.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import AttributeExploration, report_every
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert


DEFAULT_EQUATIONS_PATH = Path(__file__).resolve().parent / "equations.json"


def run_magma_exploration(
    equations_path: str | Path = DEFAULT_EQUATIONS_PATH,
    use_duality_symmetry: bool = True,
    z3_timeout_ms: int | None = None,
    report_interval: int = 20,
):
    print("=" * 70)
    print("EQUATIONAL THEORIES PROJECT (ETP) — MAGMA EXPLORATION")
    print(f"Equations File:           {Path(equations_path).name}")
    print(f"Duality Symmetry Enabled: {use_duality_symmetry}")
    print(f"Solver Budget Per Size:   {f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'}")
    print(f"Question Reporting:       {f'every {report_interval}' if report_interval >= 1 else 'off'}")
    print("=" * 70)

    equations = ETP.load_equations(equations_path)

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
    expert = MagmaExpert(
        attributes=equations,
        max_search_size=6,
        z3_timeout_ms=z3_timeout_ms,
    )
    exploration = AttributeExploration(
        base,
        expert,
        evaluate_all=True,
        on_question=report_every(report_interval),
    )

    print("\nStarting Attribute Exploration...")
    state = exploration.run()

    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Total Questions Asked:        {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"  of which unconfirmed:       {len(base.unconfirmed_implications)}")
    print(f"Total Implications in Theory: {len(base.implications.implications)}")
    print(f"Counterexample Magmas Found:  {len(state.counterexamples)}")

    # Display canonical simplified implication basis
    theory = ImplicationTheory(base.implications)
    print("\nDiscovered Canonical Implication Basis (Simplified):")
    for idx, impl in enumerate(base.accepted_implications, start=1):
        simplified = theory.simplify(impl)
        premise_str = " {" + ", ".join(eq.name or str(eq) for eq in simplified.premise) + "}" if simplified.premise else " Ø"
        concl_str = " {" + ", ".join(eq.name or str(eq) for eq in simplified.conclusion) + "}"
        unconfirmed = (
            base.implication_sources[impl] is ImplicationSource.UNCONFIRMED
        )
        marker = "   [UNCONFIRMED]" if unconfirmed else ""
        print(f"  [{idx}] {premise_str}  ==>  {concl_str}{marker}")

    if base.unconfirmed_implications:
        print(
            "\n  [UNCONFIRMED] = no counterexample was found, but the solver ran out"
            "\n  of time at some magma size, so these implications remain open rather"
            f"\n  than verified up to size {expert.max_search_size}."
        )

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
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--equations",
        type=Path,
        default=DEFAULT_EQUATIONS_PATH,
        metavar="PATH",
        help=(
            "JSON file listing the equations to explore as attributes "
            "(default: equations.json next to this script). Each entry has an "
            '"equation" string and optional "name" and "id" fields; the set '
            "must be closed under duality."
        ),
    )
    parser.add_argument(
        "--z3-timeout-ms",
        type=int,
        default=30000,
        metavar="MS",
        help=(
            "Per-magma-size solver budget in milliseconds (default: 30000); "
            "0 or less runs unbounded. A few pathological searches at the "
            "larger magma sizes can dominate the running time, and the budget "
            "cuts those short. Queries that run out of budget are neither "
            "refuted nor decided, and are reported [UNCONFIRMED]."
        ),
    )
    parser.add_argument(
        "--report-every",
        type=int,
        default=1,
        metavar="N",
        help=(
            "Print every Nth question and its outcome while exploring "
            "(default: 1); 0 or less reports nothing. Use 1 to watch every "
            "question the expert is asked."
        ),
    )
    args = parser.parse_args()
    run_magma_exploration(
        equations_path=args.equations,
        use_duality_symmetry=True,
        z3_timeout_ms=args.z3_timeout_ms if args.z3_timeout_ms > 0 else None,
        report_interval=args.report_every,
    )
