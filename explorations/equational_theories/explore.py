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
   flagged [UNCONFIRMED], since they were neither refuted nor decided. With
   the Vampire expert, an implication is instead confirmed only when proved,
   counterexamples are searched for at any size, and an implication shown
   false without a counterexample on a particular law is left open.
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

from conceptual_exploration import Implication, reduced_basis, report_every
from conceptual_exploration.core.context import PartialObject, reduce_objects
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from conceptual_exploration.exploration.rounds import explore_in_rounds
from explorations.equational_theories.background import background_implications
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert
from explorations.equational_theories.vampire import FreeMagma, VampireExpert


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


def save_results(
    base: ExplorationBase,
    equations: Sequence[Equation],
    directory: Path,
    settings: str,
    refuted: Sequence[Implication[Equation]] = (),
) -> None:
    """Write the implication theory and the context of an exploration.

    implications.txt and implications.json list every implication of the
    theory with its source, and the questions left open; magmas.json holds
    the finite magmas of the context and free_magmas.json the free magmas,
    with their rows, which Vampire may have left partial; context.cxt
    (Burmeister format) holds every object whose row is complete. A dual
    image is named after its original with ^op.
    """
    directory.mkdir(parents=True, exist_ok=True)
    # Equations are identified by their id, or else by their name or text,
    # and listed in that order.
    position = {eq: k for k, eq in enumerate(equations)}
    order = lambda eq: (eq.id is None, eq.id or 0, position[eq])
    ordered = sorted(equations, key=order)
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    label = lambda eq: f"Eq{eq.id}" if eq.id is not None else ident(eq)
    ids = lambda eqs: [ident(eq) for eq in sorted(eqs, key=order)]

    names: dict[object, str] = {}
    magmas, free, rows = [], [], []  # rows: (name, positive, negative)
    for version, obj in base.context.objects.items():
        original = version.original
        prefix = "F" if isinstance(original, FreeMagma) else "M"
        count = sum(1 for o in names if isinstance(o, FreeMagma) == (prefix == "F"))
        name = names.setdefault(original, f"{prefix}{count + 1}")
        # The only mapping is duality, whose image of a table is its transpose.
        dual_of = name if version.version else None
        if version.version:
            name += "^op"
        rows.append((name, obj.positive, obj.negative))
        if isinstance(original, FreeMagma):
            free.append({
                "name": name, "dual_of": dual_of,
                "premise": ids(original.premise),
                "positive": ids(obj.positive),
                "negative": ids(obj.negative),
            })
        else:
            table = tuple(zip(*original.table)) if version.version else original.table
            magmas.append({"name": name, "size": len(table), "table": [list(r) for r in table],
                           "found_as": original.name, "dual_of": dual_of})

    complete = [(n, pos) for n, pos, neg in rows if len(pos) + len(neg) == len(ordered)]
    cxt = ["B", "", str(len(complete)), str(len(ordered)), ""]
    cxt += [n for n, _ in complete]
    cxt += [label(eq) for eq in ordered]
    cxt += ["".join("X" if eq in pos else "." for eq in ordered) for _, pos in complete]
    (directory / "context.cxt").write_text("\n".join(cxt) + "\n", encoding="utf-8")
    for filename, entries in (("magmas.json", magmas), ("free_magmas.json", free)):
        (directory / filename).write_text(
            "[\n" + ",\n".join("  " + json.dumps(e) for e in entries) + "\n]\n", encoding="utf-8"
        )

    records, lines = [], []
    for idx, implication in enumerate(base.implications, start=1):
        premise = sorted(implication.premise, key=order)
        conclusion = sorted(implication.conclusion, key=order)
        source = base.implication_sources[implication].value
        records.append({"premise": ids(premise), "conclusion": ids(conclusion), "source": source})
        lines.append(
            f"[{idx}] {', '.join(map(label, premise)) or 'Ø'} ==> "
            f"{', '.join(map(label, conclusion))}   ({source})"
        )
    header = [
        f"Implication theory of an exploration ({settings}).",
        "background = derived by equational reasoning; confirmed = no counterexample in the",
        "searched sizes, or proved by Vampire; unconfirmed = neither refuted nor decided;",
        "mapped = dual of another implication, added when not already entailed. Open questions",
        "are implications shown false without a counterexample known to violate their conclusion.",
        "",
        "Equations:",
        *(f"  {label(eq)}: {eq.lhs} = {eq.rhs}" for eq in ordered),
        "",
    ]
    for implication in refuted:
        records.append({"premise": ids(implication.premise),
                        "conclusion": ids(implication.conclusion),
                        "source": "refuted"})
    for implication in base.open_questions:
        premise = sorted(implication.premise, key=order)
        conclusion = sorted(implication.conclusion, key=order)
        records.append({"premise": ids(premise), "conclusion": ids(conclusion), "source": "open"})
    extra = []
    if refuted:
        extra += ["", "Unconfirmed implications refuted by a later object, and dropped:"]
        extra += [f"  {', '.join(map(label, sorted(i.premise, key=order)))} ==> "
                  f"{', '.join(map(label, sorted(i.conclusion, key=order)))}"
                  for i in refuted]
    if base.open_questions:
        extra += ["", "Open questions:"]
        extra += [f"  {', '.join(map(label, sorted(i.premise, key=order)))} ==> "
                  f"{', '.join(map(label, sorted(i.conclusion, key=order)))}"
                  for i in base.open_questions]
    (directory / "implications.txt").write_text(
        "\n".join(header + lines + extra) + "\n", encoding="utf-8"
    )
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
    expert_kind: str = "z3",
    vampire_prove_time_limit: int = 10,
    vampire_model_time_limit: int = 10,
    vampire_quick_model_time_limit: int = 1,
):
    print("=" * 70)
    print("EQUATIONAL THEORIES PROJECT (ETP) — MAGMA EXPLORATION")
    print(f"Equations File:           {Path(equations_path).name}")
    print(f"Duality Symmetry Enabled: {use_duality_symmetry}")
    if expert_kind == "vampire":
        print(
            f"Expert:                   Vampire, {vampire_prove_time_limit} s to prove, "
            f"{vampire_quick_model_time_limit} s and {vampire_model_time_limit} s for a model"
        )
    else:
        print(f"Expert:                   Z3, sizes {min_search_size}..{max_search_size}, "
              f"{f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'} per size")
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

    if expert_kind == "vampire":
        expert = VampireExpert(
            attributes=equations,
            prove_time_limit=vampire_prove_time_limit,
            model_time_limit=vampire_model_time_limit,
            quick_model_time_limit=vampire_quick_model_time_limit,
        )
    else:
        expert = MagmaExpert(
            attributes=equations,
            min_search_size=min_search_size,
            max_search_size=max_search_size,
            z3_timeout_ms=z3_timeout_ms,
        )
    for path in seed_magmas:
        added = expert.add_magmas(ETP.load_magmas(path))
        print(f"Seeded the expert with {added} magmas from {path}.")
    reduced = []
    if seed_context:
        # Each table once, evaluated on every equation, and reduced to the
        # magmas whose rows the others do not already account for.
        tables: dict[tuple, Magma] = {}
        for path in seed_context:
            for magma in ETP.load_magmas(path):
                tables.setdefault((magma.size, magma.table), magma)
        seeds = [PartialObject(m, *m.evaluate_all(equations)) for m in tables.values()]
        reduced = reduce_objects(seeds)
        print(
            f"Seeded the context with {len(reduced)} of {len(seeds)} magmas, "
            f"the others being redundant."
        )

    def resumed(implication, refuter):
        print(f"\nRefuted the unconfirmed implication {implication} by {getattr(refuter, 'name', refuter)}; "
              f"resuming at its premise.")

    print("\nStarting Attribute Exploration...")
    result = explore_in_rounds(
        equations,
        expert,
        background_implications=background,
        mappings=mappings,
        objects=reduced,
        evaluate_all=True,
        on_question=report_every(report_interval),
        on_resume=resumed,
    )
    base, state = result.base, result.state
    state.questions_asked = result.questions_asked
    state.counterexamples = result.counterexamples
    refuted = [(i, getattr(o, "name", str(o))) for i, o in result.refuted]
    rounds = result.rounds

    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Total Questions Asked:        {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"  of which unconfirmed:       {len(base.unconfirmed_implications)}")
    print(f"Total Implications in Theory: {len(base.implications.implications)}")
    print(f"Counterexamples Found:        {len(state.counterexamples)}")
    print(f"Open Questions:               {len(base.open_questions)}")
    print(f"Rounds:                       {rounds}")
    if isinstance(expert, VampireExpert):
        answers = ", ".join(f"{kind} {count}" for kind, count in expert.answers.most_common())
        print(f"Expert Answers:               {answers}")

    # Display the implication basis, reduced for reading
    rules = reduced_basis(base)
    print(f"\nDiscovered Implication Basis (Reduced, {len(rules)} rules):")
    for idx, rule in enumerate(rules, start=1):
        unconfirmed = rule.source is ImplicationSource.UNCONFIRMED
        marker = "   [UNCONFIRMED]" if unconfirmed else ""
        print(f"  [{idx}] {rule.format(lambda eq: eq.name or str(eq))}{marker}")

    if base.unconfirmed_implications and expert_kind == "vampire":
        print(
            "\n  [UNCONFIRMED] = Vampire decided nothing about the implication in time,"
            "\n  so it remains open."
        )
    if refuted:
        print("\nUnconfirmed Implications Refuted by a Later Object (and dropped):")
        for implication, name in refuted:
            print(f"  {implication}   (by {name})")
    if base.open_questions:
        print("\nOpen Questions (shown false, but no known object violates the conclusion):")
        for implication in base.open_questions:
            print(f"  {implication}")
    if base.unconfirmed_implications and expert_kind != "vampire":
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
        if not isinstance(m, Magma):
            continue
        key = (m.size, m.table)
        if key not in seen:
            seen.add(key)
            unique_magmas.append(m)

    for i, m in enumerate(unique_magmas[:5], start=1):
        print(f"\nCounterexample #{i}:")
        print(m)

    if results_dir is not None:
        if expert_kind == "vampire":
            expert_settings = (
                f"Vampire expert, {vampire_prove_time_limit} s to prove, "
                f"{vampire_quick_model_time_limit} s and {vampire_model_time_limit} s for a model"
            )
        else:
            expert_settings = (
                f"search sizes {expert.min_search_size}..{expert.max_search_size}, "
                f"{f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'} per size"
            )
        settings = f"{Path(equations_path).name}, {state.questions_asked} questions, {expert_settings}"

        if background_order is not None:
            settings += (
                f", background order {background_order}, transient order "
                f"{background_transient_order or background_order}, premise size "
                f"{background_premise_size or 'any'}"
            )
        save_results(base, equations, Path(results_dir), settings, [i for i, _ in refuted])
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
        "--expert",
        choices=("z3", "vampire"),
        default="z3",
        help=(
            "How questions are answered (default: z3). z3 searches for "
            "counterexamples of the sizes given below and accepts an implication "
            "when it finds none; vampire tries to prove the implication with the "
            "Vampire theorem prover and searches for a counterexample of any "
            "size, accepting the implication as confirmed only when proved."
        ),
    )
    parser.add_argument(
        "--vampire-prove-time-limit",
        type=int,
        default=10,
        metavar="S",
        help="Seconds Vampire gets to prove an implication or a single law (default: 10).",
    )
    parser.add_argument(
        "--vampire-model-time-limit",
        type=int,
        default=10,
        metavar="S",
        help=(
            "Seconds Vampire gets for a second search for a finite "
            "counterexample, made for each law of the conclusion not proved "
            "when the free magma over the premise does not refute the "
            "implication (default: 10)."
        ),
    )
    parser.add_argument(
        "--vampire-quick-model-time-limit",
        type=int,
        default=1,
        metavar="S",
        help=(
            "Seconds Vampire first gets to find a finite counterexample "
            "(default: 1). Failing that, it decides each law separately for "
            "the free magma over the premise, with the proving time limit per "
            "law."
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
                expert_kind=args.expert,
                vampire_prove_time_limit=args.vampire_prove_time_limit,
                vampire_model_time_limit=args.vampire_model_time_limit,
                vampire_quick_model_time_limit=args.vampire_quick_model_time_limit,
            )
        finally:
            sys.stdout = sys.__stdout__
