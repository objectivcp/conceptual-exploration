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
6. Optionally, implications derivable by equational reasoning within a bounded
   order are given to the exploration as background knowledge beforehand.
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

from conceptual_exploration import AttributeExploration, reduced_basis, report_every
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from explorations.equational_theories.background import background_implications
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert


DEFAULT_EQUATIONS_PATH = Path(__file__).resolve().parent / "equations.json"


def run_magma_exploration(
    equations_path: str | Path = DEFAULT_EQUATIONS_PATH,
    use_duality_symmetry: bool = True,
    z3_timeout_ms: int | None = None,
    report_interval: int = 20,
    min_search_size: int = 1,
    max_search_size: int = 6,
    background_order: int | None = None,
    background_premise_size: int | None = 2,
    background_transient_order: int | None = None,
):
    print("=" * 70)
    print("EQUATIONAL THEORIES PROJECT (ETP) — MAGMA EXPLORATION")
    print(f"Equations File:           {Path(equations_path).name}")
    print(f"Duality Symmetry Enabled: {use_duality_symmetry}")
    print(f"Search Sizes:             {min_search_size}..{max_search_size}")
    print(f"Solver Budget Per Size:   {f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'}")
    print(f"Question Reporting:       {f'every {report_interval}' if report_interval >= 1 else 'off'}")
    if background_order is None:
        print("Background Implications:  off")
    else:
        premise_bound = background_premise_size if background_premise_size is not None else "any"
        transient = background_transient_order if background_transient_order is not None else background_order
        print(
            f"Background Implications:  order {background_order}, transient order {transient}, "
            f"premise size {premise_bound}"
        )
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

    background = []
    if background_order is not None:
        background = background_implications(
            equations, background_order, background_premise_size, background_transient_order
        )
        print(f"\nDerived {len(background)} Background Implications.")

    base = ExplorationBase[Magma, Equation](
        attributes=equations,
        background_implications=background,
        mappings=mappings,
    )
    expert = MagmaExpert(
        attributes=equations,
        min_search_size=min_search_size,
        max_search_size=max_search_size,
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

    # Display the implication basis, reduced for reading
    rules = reduced_basis(base)
    print(f"\nDiscovered Implication Basis (Reduced, {len(rules)} rules):")
    for idx, rule in enumerate(rules, start=1):
        unconfirmed = rule.source is ImplicationSource.UNCONFIRMED
        marker = "   [UNCONFIRMED]" if unconfirmed else ""
        print(f"  [{idx}] {rule.format(lambda eq: eq.name or str(eq))}{marker}")

    if base.unconfirmed_implications:
        print(
            "\n  [UNCONFIRMED] = no counterexample was found, but the solver ran out"
            "\n  of time at some magma size, so these implications remain open rather"
            f"\n  than verified for sizes {expert.min_search_size}..{expert.max_search_size}."
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
        "--min-search-size",
        type=int,
        default=1,
        metavar="N",
        help=(
            "Smallest magma size the solver searches for counterexamples "
            "(default: 1). The built-in pool of small standard magmas is "
            "still checked first, whatever this is set to."
        ),
    )
    parser.add_argument(
        "--max-search-size",
        type=int,
        default=6,
        metavar="N",
        help=(
            "Largest magma size the solver searches for counterexamples "
            "(default: 6). An implication with no counterexample in the "
            "searched range is accepted, though a larger counterexample "
            "may exist."
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
    parser.add_argument(
        "--background-order",
        type=int,
        default=None,
        metavar="N",
        help=(
            "Derive background implications with equational reasoning "
            "(multiplying both sides by a term, substituting a term for the "
            "variable, replacing a subterm by an equivalent one) through "
            "equations of at most N operations, at least the largest order "
            "among the explored equations (default: no background "
            "implications). Only one-variable equations are supported."
        ),
    )
    parser.add_argument(
        "--background-premise-size",
        type=int,
        default=2,
        metavar="K",
        help=(
            "Largest premise of a background implication (default: 2); 0 or "
            "less computes the canonical basis of everything derivable, whose "
            "premises may be of any size, at a much higher cost."
        ),
    )
    parser.add_argument(
        "--background-transient-order",
        type=int,
        default=None,
        metavar="M",
        help=(
            "Let a single multiplication or substitution reach equations of up "
            "to M operations, provided rewriting with derived equations brings "
            "the result back within --background-order (default: the "
            "background order itself, so no step goes beyond it)."
        ),
    )
    args = parser.parse_args()
    if not 1 <= args.min_search_size <= args.max_search_size:
        parser.error("search sizes must satisfy 1 <= --min-search-size <= --max-search-size")
    run_magma_exploration(
        equations_path=args.equations,
        use_duality_symmetry=True,
        z3_timeout_ms=args.z3_timeout_ms if args.z3_timeout_ms > 0 else None,
        report_interval=args.report_every,
        min_search_size=args.min_search_size,
        max_search_size=args.max_search_size,
        background_order=args.background_order,
        background_premise_size=(
            args.background_premise_size if args.background_premise_size > 0 else None
        ),
        background_transient_order=args.background_transient_order,
    )
