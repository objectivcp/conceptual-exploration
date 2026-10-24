"""Unit tests for the options of explore.py read from and saved to TOML files."""

from pathlib import Path

import pytest

from explorations.equational_theories.explore import build_parser, parse_arguments, read_config, write_settings

ROOT = Path(__file__).resolve().parent.parent


def test_a_config_file_gives_defaults_that_the_command_line_overrides(tmp_path):
    config = tmp_path / "run.toml"
    config.write_text('expert = "vampire"\nmace4-time-limit = 30\nask_unconfirmed_duals = true\n'
                      'etp-graph = "graph.json"\netp-equations = "equations.txt"\n')
    args = parse_arguments(build_parser(), ["--config", str(config), "--mace4-time-limit", "5"])
    assert (args.expert, args.mace4_time_limit, args.ask_unconfirmed_duals) == ("vampire", 5, True)
    assert args.etp_graph == Path("graph.json")


def test_unknown_options_and_values_are_errors(tmp_path):
    config = tmp_path / "run.toml"
    config.write_text("mace5-time-limit = 30\n")
    with pytest.raises(SystemExit):
        parse_arguments(build_parser(), ["--config", str(config)])
    config.write_text('expert = "prover9"\n')
    with pytest.raises(SystemExit):
        parse_arguments(build_parser(), ["--config", str(config)])


def test_seed_patterns_are_expanded(tmp_path):
    for name in ("b.txt", "a.txt"):
        (tmp_path / name).write_text("Table [[0]]\n")
    args = parse_arguments(build_parser(), ["--seed-context", str(tmp_path / "*.txt")])
    assert args.seed_context == [tmp_path / "a.txt", tmp_path / "b.txt"]


def test_saved_settings_give_the_same_options_again(tmp_path):
    parser = build_parser()
    argv = ["--expert", "vampire", "--eprover-time-limit", "2", "--etp-refutations",
            "--seed-context", str(tmp_path / "a.txt"), "--results-dir", str(tmp_path / "results")]
    (tmp_path / "a.txt").write_text("Table [[0]]\n")
    args = parse_arguments(parser, argv)
    write_settings(parser, args, tmp_path / "settings.toml")
    again = parse_arguments(build_parser(), ["--config", str(tmp_path / "settings.toml")])
    assert {**vars(again), "config": None, "results_dir": None} == {**vars(args), "results_dir": None}


def test_the_order3_preset_reads():
    # Read as defaults only, so that the ETP data need not be fetched.
    defaults = read_config(build_parser(), ROOT / "explorations/equational_theories/configs/order3.toml")
    assert defaults["expert"] == "vampire" and defaults["eprover_time_limit"] == 2
    assert defaults["seed_context"] == [Path("etp/magmas/*.txt")]


def test_the_semigroup_preset_reads():
    defaults = read_config(build_parser(), ROOT / "explorations/equational_theories/configs/semigroup.toml")
    assert defaults["axiom"] == ["4512"] and defaults["model_premise"] == "simplified"
    assert defaults["vampire_row_time_limit"] == 0


def test_the_commutative_semigroup_preset_reads():
    defaults = read_config(build_parser(), ROOT / "explorations/equational_theories/configs/csemigroup5.toml")
    assert defaults["axiom"] == ["4512", "43"] and defaults["no_duality"] is True
