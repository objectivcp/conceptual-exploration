"""Configuration of Sudoku explorations, read from TOML files.

A configuration says what kind of grid is explored and how:

    grid = "solved"           # "solved", "partial" or "propositional"
    block_size = 2
    cells = ["w", "x", "y", "z"]
    numbers = ["n"]
    cell_sets = []            # variables for non-empty sets of cells
    number_sets = []          # and of numbers
    predicates = ["SameCell", "DifferentCells", "SameRow", "Contains", "NotContains"]
    background = true
    geometry_first = false
    classical = true          # drop rules that follow classically from the others
    compare_without = []      # mark the rules not entailed when these are left out
    expert = "sat"            # or "z3" for solved grids
    check_block_size = 3      # solved grids: re-check the rules there; 0 skips

Solved and partial grids are explored with first-order rules over the cell
and number variables; partial grids only at block size 2, with Forced,
Excluded and Possible in place of Contains and NotContains. Propositional
exploration has (row, column, digit) attributes and takes `block_size`,
`background` and `symmetries` only. The shipped
configurations in `configs/` can be named instead of given by path.
"""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, fields, replace
from pathlib import Path
from typing import Any, Callable, Optional

from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.variable import SortedVariable
from explorations.sudoku.sudoku import (
    SudokuSort,
    check_rule_exploration,
    sudoku_rule_exploration,
)

CONFIG_DIR = Path(__file__).resolve().parent / "configs"

_RULE_ONLY = (
    "cells", "numbers", "cell_sets", "number_sets", "predicates", "geometry_first", "classical", "compare_without",
    "expert", "check_block_size",
)


@dataclass(frozen=True)
class ExplorationConfig:
    grid: str
    block_size: int = 2
    cells: tuple[str, ...] = ()
    numbers: tuple[str, ...] = ()
    cell_sets: tuple[str, ...] = ()
    number_sets: tuple[str, ...] = ()
    predicates: tuple[str, ...] = ()
    background: bool = True
    geometry_first: bool = False
    classical: bool = True
    compare_without: tuple[str, ...] = ()
    expert: str = "sat"
    # None means the default: 9x9 for rules found on 4x4 grids, 4x4 for rules
    # found on larger ones.
    check_block_size: Optional[int] = None
    symmetries: bool = True

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "ExplorationConfig":
        """Build and check a configuration; unknown keys and wrong types
        raise ValueError, so that a misspelt key is not silently ignored."""
        types = {
            "grid": str, "block_size": int, "cells": list, "numbers": list,
            "cell_sets": list, "number_sets": list,
            "predicates": list, "background": bool, "geometry_first": bool,
            "classical": bool, "compare_without": list, "expert": str, "check_block_size": int, "symmetries": bool,
        }
        unknown = sorted(set(data) - set(types))
        if unknown:
            raise ValueError(f"unknown configuration keys {unknown}; known are {sorted(types)}")
        if "grid" not in data:
            raise ValueError("the configuration must say which grid to explore (grid = ...)")
        values = {}
        for key, value in data.items():
            # bool is an int in Python; neither stands in for the other here.
            if not isinstance(value, types[key]) or (types[key] is int and isinstance(value, bool)):
                raise ValueError(f"{key} must be a {types[key].__name__}, not {value!r}")
            if types[key] is list:
                if not all(isinstance(item, str) for item in value):
                    raise ValueError(f"{key} must be a list of names, not {value!r}")
                value = tuple(value)
            values[key] = value
        config = cls(**values)
        config.check()
        return config

    def check(self) -> None:
        """Raise ValueError, saying why, if the configuration cannot be run."""
        if self.grid not in ("solved", "partial", "propositional"):
            raise ValueError(f'grid must be "solved", "partial" or "propositional", not {self.grid!r}')
        if self.grid == "propositional":
            given = [
                name for name in _RULE_ONLY
                if getattr(self, name) != next(f.default for f in fields(self) if f.name == name)
            ]
            if given:
                raise ValueError(f"{given} do not apply to propositional exploration")
            if self.block_size != 2:
                raise ValueError(
                    "propositional exploration needs block_size 2: its symmetry "
                    "group and background are only practical for 4x4 grids"
                )
            return
        check_rule_exploration(
            self.block_size, self.cells, self.numbers, self.predicates, self.expert, self.grid,
            self.cell_sets, self.number_sets,
        )
        stray = [p for p in self.compare_without if p not in self.predicates]
        if stray:
            raise ValueError(f"compare_without names predicates that are not explored: {stray}")
        if self.compare_without and set(self.predicates) <= set(self.compare_without):
            raise ValueError("compare_without leaves no predicate to compare with")
        if self.grid == "partial" and self.check_block_size:
            raise ValueError("rules about partial grids cannot be re-checked on another grid size")
        if self.check_block_size is not None and self.check_block_size not in (0, 2, 3):
            raise ValueError(f"check_block_size must be 0, 2 or 3, not {self.check_block_size}")

    @property
    def variables(self) -> list[SortedVariable]:
        """The cell variables, the number variables, then the set variables."""
        return (
            [SortedVariable(name, SudokuSort.CELL) for name in self.cells]
            + [SortedVariable(name, SudokuSort.NUMBER) for name in self.numbers]
            + [SortedVariable(name, SudokuSort.CELLSET) for name in self.cell_sets]
            + [SortedVariable(name, SudokuSort.NUMBERSET) for name in self.number_sets]
        )

    @property
    def effective_check_block_size(self) -> int:
        """The block size the accepted rules are re-checked on, 0 for none."""
        if self.grid != "solved":
            return 0
        if self.check_block_size is not None:
            return self.check_block_size
        return 3 if self.block_size == 2 else 2

    def with_overrides(self, **changes: Any) -> "ExplorationConfig":
        """A copy with some settings changed, checked again."""
        config = replace(self, **changes)
        config.check()
        return config

    def rule_exploration(
        self,
        on_question: Optional[Callable[[Any], None]] = None,
    ) -> RuleExploration:
        if self.grid == "propositional":
            raise ValueError("propositional exploration is not a rule exploration")
        return sudoku_rule_exploration(
            self.block_size,
            self.cells,
            self.numbers,
            self.predicates,
            background=self.background,
            geometry_first=self.geometry_first,
            expert=self.expert,
            grid=self.grid,
            cell_sets=self.cell_sets,
            number_sets=self.number_sets,
            on_question=on_question,
        )

    def to_toml(self) -> str:
        """The settings that apply to this kind of exploration, as TOML."""
        def value(v: Any) -> str:
            if isinstance(v, bool):
                return "true" if v else "false"
            if isinstance(v, tuple):
                return "[" + ", ".join(f'"{item}"' for item in v) + "]"
            if isinstance(v, str):
                return f'"{v}"'
            return str(v)

        lines = []
        for f in fields(self):
            v = getattr(self, f.name)
            if self.grid == "propositional" and f.name in _RULE_ONLY:
                continue
            if self.grid != "propositional" and f.name == "symmetries":
                continue
            if f.name == "check_block_size":
                if self.grid != "solved":
                    continue
                v = self.effective_check_block_size
            lines.append(f"{f.name} = {value(v)}")
        return "\n".join(lines)


def available_configs() -> list[str]:
    """The names of the configurations shipped in `configs/`."""
    return sorted(path.stem for path in CONFIG_DIR.glob("*.toml"))


def load_config(name_or_path: str | Path) -> ExplorationConfig:
    """Read a configuration from a TOML file, or from the shipped one of
    that name."""
    path = Path(name_or_path)
    if not path.exists():
        shipped = CONFIG_DIR / f"{name_or_path}.toml"
        if not shipped.exists():
            raise FileNotFoundError(
                f"no configuration file {str(name_or_path)!r}, and no shipped "
                f"configuration of that name; shipped are {available_configs()}"
            )
        path = shipped
    with open(path, "rb") as file:
        data = tomllib.load(file)
    try:
        return ExplorationConfig.from_dict(data)
    except ValueError as error:
        raise ValueError(f"{path}: {error}") from None
