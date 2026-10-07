"""Conceptual Exploration of Sudoku Rules and Constraints.

Runs the Sudoku explorations described by TOML configuration files (see
`config.py`): first-order rule exploration of solved grids or of partial 4x4
grids, or propositional attribute exploration of 4x4 grids. Each argument is
a configuration file, or the name of one shipped in `configs/`:

    python explorations/sudoku/explore.py partial-row
    python explorations/sudoku/explore.py my-exploration.toml --block-size 3
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import AttributeExploration, reduced_basis
from conceptual_exploration.exploration.base import ExplorationBase
from explorations.sudoku.config import ExplorationConfig, available_configs, load_config
from explorations.sudoku.sudoku import (
    SudokuExpert,
    check_rules,
    get_sudoku_attributes,
    get_sudoku_background_implications,
    get_sudoku_symmetries,
)


def expert_label(config: ExplorationConfig) -> str:
    """How the configured expert decides the questions."""
    if config.grid == "partial":
        if config.expert == "cegar":
            return "CEGAR (counterexample-guided, two PySAT solvers)"
        return "SAT (PySAT), listing every solved 4x4 grid"
    return {"sat": "SAT (PySAT)", "z3": "SMT (Z3)"}[config.expert]


def run_rule_exploration(config: ExplorationConfig, label: str) -> list[str]:
    """Run a first-order rule exploration and return its rules as printed."""
    size = config.block_size**2
    print("=" * 70)
    print(f"SUDOKU RULE EXPLORATION: {label} ({config.grid} {size}x{size} grids)")
    print("=" * 70)
    print(f"Cells:      {', '.join(config.cells) or '-'}")
    print(f"Numbers:    {', '.join(config.numbers) or '-'}")
    print(f"Predicates: {', '.join(config.predicates)}")
    print(f"Expert:     {expert_label(config)}")
    background = "on" if config.background else "off"
    if config.geometry_first:
        background += ", with the geometry explored first"
    print(f"Background: {background}")

    exploration = config.rule_exploration()
    base = exploration.base
    # How large the exploration is decides how long it takes; say so first.
    print(f"\nAtoms: {len(base.attributes)}, mappings: {len(base.mappings)}, "
          f"background implications: {len(exploration.background)}")

    start_time = time.perf_counter()
    state = exploration.run()
    elapsed = time.perf_counter() - start_time
    print(f"\nTime Elapsed:                 {elapsed:.2f}s")
    print(f"Questions Asked:              {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")

    check_size = config.effective_check_block_size
    counterexamples = {}
    if check_size:
        start_time = time.perf_counter()
        counterexamples = dict(
            check_rules(base.accepted_implications, check_size, config.variables)
        )
        elapsed = time.perf_counter() - start_time
        failing = sum(c is not None for c in counterexamples.values())
        print(f"Checked on Block Size {check_size}:     "
              f"{failing} of {len(counterexamples)} fail ({elapsed:.2f}s)")

    rules = reduced_basis(base)
    lines = []
    print(f"\nDiscovered Rules (Reduced, {len(rules)}):")
    for idx, rule in enumerate(rules, start=1):
        fails = counterexamples.get(rule.implication) is not None
        marker = f"   [FAILS FOR BLOCK SIZE {check_size}]" if fails else ""
        lines.append(f"{rule}{marker}")
        print(f"  [{idx}] {rule}{marker}")

    failing = [
        (idx, counterexamples[rule.implication])
        for idx, rule in enumerate(rules, start=1)
        if counterexamples.get(rule.implication) is not None
    ]
    if failing:
        print(f"\nCounterexamples for Block Size {check_size}:")
        for idx, counterexample in failing:
            print(f"\nRule [{idx}]: {counterexample.object}")
    print()
    return lines


def run_propositional_exploration(config: ExplorationConfig, label: str) -> list[str]:
    """Run propositional attribute exploration of 4x4 grids and return its
    rules as printed."""
    print("=" * 70)
    print(f"SUDOKU PROPOSITIONAL EXPLORATION: {label} (4x4 grids)")
    print("=" * 70)

    attributes = get_sudoku_attributes(config.block_size)
    mappings = get_sudoku_symmetries(config.block_size) if config.symmetries else []
    background = (
        get_sudoku_background_implications(config.block_size) if config.background else []
    )
    print(f"Attributes: {len(attributes)} cell assignments (row, column, digit), "
          f"mappings: {len(mappings)}, background implications: {len(background)}")

    base = ExplorationBase(
        attributes=attributes,
        background_implications=background,
        mappings=mappings,
    )
    start_time = time.perf_counter()
    state = AttributeExploration(base, SudokuExpert(config.block_size)).run()
    elapsed = time.perf_counter() - start_time
    print(f"\nTime Elapsed:                 {elapsed:.2f}s")
    print(f"Questions Asked:              {state.questions_asked}")
    print(f"Accepted Implications (Base): {len(base.accepted_implications)}")
    print(f"Discovered Objects/Configs:   {len(base.context.objects)}")

    rules = reduced_basis(base)
    lines = [str(rule) for rule in rules]
    print(f"\nDiscovered Rules (Reduced, {len(rules)}), as (row, column, digit):")
    for idx, line in enumerate(lines, start=1):
        print(f"  [{idx}] {line}")
    print()
    return lines


def run(config: ExplorationConfig, label: str) -> list[str]:
    if config.grid == "propositional":
        return run_propositional_exploration(config, label)
    return run_rule_exploration(config, label)


def write_rules(path: Path, label: str, config: ExplorationConfig, lines: list[str]) -> None:
    """Write the rules, after the configuration that produced them."""
    header = [f"# Sudoku exploration: {label}", "#"]
    header += [f"# {line}" for line in config.to_toml().splitlines()]
    path.write_text("\n".join(header + [""] + lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        epilog=f"Shipped configurations: {', '.join(available_configs())}",
    )
    parser.add_argument(
        "configs",
        nargs="+",
        metavar="CONFIG",
        help="a TOML configuration file, or the name of a shipped one; several run in turn",
    )
    parser.add_argument(
        "--block-size",
        type=int,
        metavar="K",
        help="explore grids of block size K instead of the configured one",
    )
    parser.add_argument(
        "--no-background",
        dest="background",
        action="store_false",
        default=None,
        help="explore without the background implications, so they are rediscovered too",
    )
    parser.add_argument(
        "--output",
        type=Path,
        metavar="PATH",
        help="also write the rules to PATH, after the configuration that produced them",
    )
    args = parser.parse_args(argv)
    if args.output is not None and len(args.configs) > 1:
        parser.error("--output takes a single configuration")

    overrides = {}
    if args.block_size is not None:
        overrides["block_size"] = args.block_size
    if args.background is not None:
        overrides["background"] = args.background

    # Check every configuration before running any, so that a mistake in the
    # last one does not show up only after the first has run for minutes.
    configs = []
    for name in args.configs:
        try:
            configs.append((name, load_config(name).with_overrides(**overrides)))
        except (OSError, ValueError) as error:
            parser.error(str(error))

    for name, config in configs:
        lines = run(config, Path(name).stem)
        if args.output is not None:
            write_rules(args.output, Path(name).stem, config, lines)
            print(f"Rules written to {args.output}")


if __name__ == "__main__":
    main()
