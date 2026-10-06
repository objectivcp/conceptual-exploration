"""Tests for the TOML configuration of Sudoku explorations and its runner."""

import tomllib

import pytest

from explorations.sudoku import ExplorationConfig, available_configs, load_config
from explorations.sudoku.explore import main


@pytest.mark.parametrize("name", available_configs())
def test_shipped_configurations_load(name):
    config = load_config(name)
    assert config.grid in ("solved", "partial", "propositional")


def test_shipped_configurations_include_every_kind_of_grid():
    grids = {load_config(name).grid for name in available_configs()}
    assert grids == {"solved", "partial", "propositional"}


def _config(**settings):
    return ExplorationConfig.from_dict(settings)


@pytest.mark.parametrize("settings, message", [
    ({"cells": ["x"], "predicates": ["SameRow"]}, "which grid"),
    ({"grid": "solved", "cells": ["x"], "predicates": ["SameRow"], "colour": 1}, "unknown configuration keys"),
    ({"grid": "solved", "block_size": "2", "cells": ["x"], "predicates": ["SameRow"]}, "block_size must be"),
    ({"grid": "solved", "background": 1, "cells": ["x"], "predicates": ["SameRow"]}, "background must be"),
    ({"grid": "solved", "cells": ["x"], "predicates": ["Forced"]}, "do not apply to solved grids"),
    ({"grid": "partial", "cells": ["x"], "numbers": ["n"], "predicates": ["Contains"]}, "do not apply to partial grids"),
    ({"grid": "partial", "block_size": 4, "cells": ["x"], "predicates": ["SameRow"]}, "block_size 2"),
    ({"grid": "partial", "cells": ["x"], "predicates": ["SameRow"], "expert": "z3"}, "expert for partial grids"),
    ({"grid": "solved", "cells": ["x"], "predicates": ["SameRow"], "expert": "cegar"}, "expert for solved grids"),
    ({"grid": "partial", "block_size": 3, "cells": ["x"], "predicates": ["SameRow"]}, "use expert = \"cegar\""),
    ({"grid": "partial", "cells": ["x"], "predicates": ["SameRow"], "check_block_size": 3}, "cannot be re-checked"),
    ({"grid": "solved", "cells": ["x"], "predicates": ["Contains"]}, "needs a number variable"),
    ({"grid": "solved", "cells": ["x", "x"], "predicates": ["SameRow"]}, "distinct"),
    ({"grid": "solved", "cells": ["x"], "predicates": ["SameRoww"]}, "unknown predicates"),
    ({"grid": "solved", "cells": ["x"], "predicates": []}, "at least one predicate"),
    ({"grid": "propositional", "cells": ["x"]}, "do not apply to propositional"),
    ({"grid": "propositional", "block_size": 3}, "block_size 2"),
])
def test_configurations_that_cannot_run_say_why(settings, message):
    with pytest.raises(ValueError, match=message):
        _config(**settings)


def test_overrides_are_checked():
    config = load_config("partial-row")
    with pytest.raises(ValueError, match="block_size 2"):
        config.with_overrides(block_size=3)
    assert load_config("solved-pairs").with_overrides(block_size=3).block_size == 3


def test_the_check_defaults_to_the_other_grid_size():
    assert load_config("solved-pairs").effective_check_block_size == 3
    assert load_config("solved-pairs").with_overrides(block_size=3).effective_check_block_size == 2
    assert load_config("partial-row").effective_check_block_size == 0


@pytest.mark.parametrize("name", available_configs())
def test_written_configuration_reads_back(name):
    config = load_config(name)
    again = ExplorationConfig.from_dict(tomllib.loads(config.to_toml()))
    assert again.effective_check_block_size == config.effective_check_block_size
    if config.grid == "solved":
        config = config.with_overrides(check_block_size=config.effective_check_block_size)
    assert again == config


def test_runner_writes_the_rules_after_the_configuration(tmp_path, capsys):
    output = tmp_path / "rules.txt"
    main(["solved-pairs", "--output", str(output)])
    text = output.read_text()
    header, rules = text.split("\n\n", 1)
    assert header.startswith("# Sudoku exploration: solved-pairs")
    assert ExplorationConfig.from_dict(
        tomllib.loads("\n".join(line[2:] for line in header.splitlines()[2:]))
    ).grid == "solved"
    assert sorted(rules.split("\n")[:-1]) == [
        "Same(x, y), SameBlock(x, y) -> SameCell(x, y)",
        "Same(x, y), SameColumn(x, y) -> SameCell(x, y)",
        "Same(x, y), SameRow(x, y) -> SameCell(x, y)",
    ]


def test_runner_checks_every_configuration_before_running(capsys):
    with pytest.raises(SystemExit):
        main(["solved-pairs", "no-such-configuration"])
    assert "SUDOKU" not in capsys.readouterr().out
