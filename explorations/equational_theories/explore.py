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
7. The log, the implication theory and the context are saved to a results
   directory.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from datetime import datetime
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import AttributeExploration, reduced_basis, report_every
from conceptual_exploration.core.context import PartialObject, reduce_objects
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from explorations.equational_theories.background import background_implications
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert


DEFAULT_EQUATIONS_PATH = Path(__file__).resolve().parent / "equations.json"
RESULTS_PATH = Path(__file__).resolve().parent / "results"


class _Tee:
    """Write to several streams at once, to keep a log of what is printed."""

    def __init__(self, *streams):
        self.streams = streams

    def write(self, text: str) -> int:
        for stream in self.streams:
            stream.write(text)
        return len(text)

    def flush(self) -> None:
        for stream in self.streams:
            stream.flush()


def save_results(base: ExplorationBase, equations: Sequence[Equation], directory: Path, settings: str) -> None:
    """Write the implication theory and the context of an exploration.

    implications.txt and implications.json list every implication of the
    theory with its source; magmas.json and context.cxt (Burmeister format)
    hold the objects of the context, a dual image being named after its
    original with ^op. Every object of the context is fully evaluated, the
    expert being asked to evaluate all attributes.
    """
    directory.mkdir(parents=True, exist_ok=True)
    ordered = sorted(equations, key=lambda eq: eq.id)
    label = lambda eq: f"Eq{eq.id}"

    names: dict[Magma, str] = {}
    objects = []  # (name, magma, found_as, dual_of, positive)
    for version, obj in base.context.objects.items():
        magma = version.original
        name = names.setdefault(magma, f"M{len(names) + 1}")
        if version.version == 0:
            objects.append((name, magma.table, magma.name, None, obj.positive))
        else:
            # The only mapping is duality, whose image is the transposed table.
            table = tuple(zip(*magma.table))
            objects.append((name + "^op", table, magma.name, name, obj.positive))

    cxt = ["B", "", str(len(objects)), str(len(ordered)), ""]
    cxt += [o[0] for o in objects]
    cxt += [label(eq) for eq in ordered]
    cxt += ["".join("X" if eq in o[4] else "." for eq in ordered) for o in objects]
    (directory / "context.cxt").write_text("\n".join(cxt) + "\n", encoding="utf-8")
    (directory / "magmas.json").write_text(
        "[\n" + ",\n".join(
            "  " + json.dumps({"name": n, "size": len(t), "table": [list(r) for r in t],
                               "found_as": f, "dual_of": d})
            for n, t, f, d, _ in objects
        ) + "\n]\n",
        encoding="utf-8",
    )

    records, lines = [], []
    for idx, implication in enumerate(base.implications, start=1):
        premise = sorted(implication.premise, key=lambda eq: eq.id)
        conclusion = sorted(implication.conclusion, key=lambda eq: eq.id)
        source = base.implication_sources[implication].value
        records.append({"premise": [eq.id for eq in premise],
                        "conclusion": [eq.id for eq in conclusion], "source": source})
        lines.append(
            f"[{idx}] {', '.join(map(label, premise)) or 'Ø'} ==> "
            f"{', '.join(map(label, conclusion))}   ({source})"
        )
    header = [
        f"Implication theory of an exploration ({settings}).",
        "background = derived by equational reasoning; confirmed = no counterexample in the",
        "searched sizes; unconfirmed = no counterexample found, but the solver ran out of time",
        "at some size; mapped = dual of another implication, added when not already entailed.",
        "",
        "Equations:",
        *(f"  {label(eq)}: {eq.lhs} = {eq.rhs}" for eq in ordered),
        "",
    ]
    (directory / "implications.txt").write_text("\n".join(header + lines) + "\n", encoding="utf-8")
    (directory / "implications.json").write_text(
        "[\n" + ",\n".join("  " + json.dumps(r) for r in records) + "\n]\n", encoding="utf-8"
    )


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
    seed_magmas: Sequence[str | Path] = (),
    seed_context: Sequence[str | Path] = (),
    results_dir: str | Path | None = None,
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
    if results_dir is not None:
        print(f"Results Directory:        {results_dir}")
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
    for path in seed_magmas:
        added = expert.add_magmas(ETP.load_magmas(path))
        print(f"Seeded the expert with {added} magmas from {path}.")
    if seed_context:
        # Each table once, evaluated on every equation, and reduced to the
        # magmas whose rows the others do not already account for.
        tables: dict[tuple, Magma] = {}
        for path in seed_context:
            for magma in ETP.load_magmas(path):
                tables.setdefault((magma.size, magma.table), magma)
        seeds = [PartialObject(m, *m.evaluate_all(equations)) for m in tables.values()]
        reduced = reduce_objects(seeds)
        for seed in reduced:
            base.add_counterexample(seed)
        print(
            f"Seeded the context with {len(reduced)} of {len(seeds)} magmas, "
            f"the others being redundant."
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

    if results_dir is not None:
        settings = (
            f"{Path(equations_path).name}, {state.questions_asked} questions, search sizes "
            f"{expert.min_search_size}..{expert.max_search_size}, "
            f"{f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'} per size"
        )
        if background_order is not None:
            settings += (
                f", background order {background_order}, transient order "
                f"{background_transient_order or background_order}, premise size "
                f"{background_premise_size or 'any'}"
            )
        save_results(base, equations, Path(results_dir), settings)
        print(f"\nResults saved to {results_dir}.")

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
        "--seed-magmas",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "JSON files of magmas, such as the magmas.json of earlier results, "
            "added to the expert's pool of standard magmas. The pool is checked "
            "for a counterexample before the solver searches for one."
        ),
    )
    parser.add_argument(
        "--seed-context",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "JSON files of magmas, such as the magmas.json of earlier results, "
            "evaluated on every equation and added to the context before the "
            "exploration starts, after dropping those whose rows the others "
            "account for. No question that they refute is asked."
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
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "Directory to save the log, the implication theory and the context "
            "in (default: a new directory under results/ named after the "
            "equations file and the starting time). It must not hold results "
            "already."
        ),
    )
    args = parser.parse_args()
    if not 1 <= args.min_search_size <= args.max_search_size:
        parser.error("search sizes must satisfy 1 <= --min-search-size <= --max-search-size")
    results_dir = args.results_dir or (
        RESULTS_PATH / f"{args.equations.stem}_{datetime.now():%Y-%m-%d_%H%M%S}"
    )
    if (results_dir / "exploration.log").exists():
        parser.error(f"{results_dir} already holds results")
    results_dir.mkdir(parents=True, exist_ok=True)
    # Line-buffered, so the log can be followed while the exploration runs.
    with open(results_dir / "exploration.log", "w", encoding="utf-8", buffering=1) as log:
        sys.stdout = _Tee(sys.__stdout__, log)
        try:
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
                seed_magmas=args.seed_magmas,
                seed_context=args.seed_context,
                results_dir=results_dir,
            )
        finally:
            sys.stdout = sys.__stdout__
