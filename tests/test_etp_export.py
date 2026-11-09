"""Unit tests for the data in the ETP's form."""

import json

from explorations.equational_theories import etp_export
from explorations.equational_theories.certificates import parse_law, show
from explorations.equational_theories.etp import ImplicationClosure, ImplicationGraph


class FakeLaws:
    """ETP numbers for a few laws, in the ETP's form."""

    numbers = {"x = x": 1, "x = y": 2, "x = (x * x)": 3, "x = (x * (x * x))": 8, "x = ((x * x) * x)": 23}

    def __init__(self, etp):
        pass

    def number(self, law):
        for text, number in self.numbers.items():
            if parse_law(text) in (law, law[::-1]):
                return number
        raise KeyError(f"{show(law[0])} = {show(law[1])}")

    def text(self, number):
        return next(text for text, n in self.numbers.items() if n == number).replace("*", "◇")


def results(tmp_path):
    equations = [{"id": n, "equation": text} for text, n in FakeLaws.numbers.items()]
    (tmp_path / "equations.json").write_text(json.dumps(equations))
    run = tmp_path / "run"
    run.mkdir()
    (run / "implications.json").write_text(json.dumps([
        {"premise": [], "conclusion": [1], "source": "background"},
        {"premise": [3], "conclusion": [8], "source": "confirmed"},
        {"premise": [3], "conclusion": [23], "source": "mapped"},
    ]))
    # The constant magma satisfies x = x only; the one-element magma everything.
    (run / "context.cxt").write_text("B\n\n2\n5\n\nM1\nM2\nEq1\nEq2\nEq3\nEq8\nEq23\nX....\nXXXXX\n")
    (run / "magmas.json").write_text(json.dumps([{"name": "M1", "table": [[0, 0], [0, 0]]},
                                                 {"name": "M2", "table": [[0]]}]))
    return run


def test_the_rules_are_simplified_and_followed_by_their_duals(tmp_path, monkeypatch):
    monkeypatch.setattr(etp_export, "EtpLaws", FakeLaws)
    export = etp_export.Export(results(tmp_path), tmp_path / "equations.json", [], tmp_path)
    implications = export.implications()
    # One of x = x(xx) and its dual x = (xx)x is kept, the other is its image.
    proved = [(r["name"], r["premise"], r["conclusion"], r["source"])
              for r in implications if not r["name"].startswith("B")]
    assert sorted(proved) in (
        [("1", [3], [8], "proved"), ("1^op", [3], [23], "dual of 1")],
        [("1", [3], [23], "proved"), ("1^op", [3], [8], "dual of 1")],
    )
    assert {"name": "B1", "premise": [], "conclusion": [1], "source": "background"} in implications


def closure(implications, duals={8: 23, 23: 8}):
    """The closure of the ETP's implications among laws 1 to 23, given as
    pairs, and of their images under the duality given."""
    outcomes = bytearray(23 * 23)
    for premise, conclusion in implications:
        outcomes[(premise - 1) * 23 + conclusion - 1] = 3
    return ImplicationClosure(ImplicationGraph(outcomes, 23), lambda law: duals.get(law, law))


def test_the_closure_chains_implications_and_their_duals():
    # 1 => 2 directly; 2 => 23 as the dual of 2 => 8; 23 => 5 directly.
    implied = closure([(1, 2), (2, 8), (23, 5)]).implied(1)
    assert {q for q in range(1, 24) if implied >> (q - 1) & 1} == {1, 2, 5, 8, 23}
    assert closure([]).implied(30) == 0


def test_rules_the_etp_lacks_even_up_to_duality_are_new(tmp_path, monkeypatch):
    monkeypatch.setattr(etp_export, "EtpLaws", FakeLaws)
    run = results(tmp_path)
    # x = xx => x = (xx)x is known; x = xx => x = x(xx) is its dual.
    export = etp_export.Export(run, tmp_path / "equations.json", [], tmp_path,
                               background_label="ETP", closure=closure([(3, 23)]))
    implications = {tuple(r["conclusion"]): r for r in export.implications()}
    assert implications[(1,)]["origin"] == "ETP" and not implications[(1,)]["new"]
    assert not implications[(8,)]["new"] and not implications[(23,)]["new"]
    assert "origin" not in implications[(8,)] and "origin" not in implications[(23,)]
    export = etp_export.Export(run, tmp_path / "equations.json", [], tmp_path, closure=closure([]))
    etp_export.write(export, tmp_path / "data", reduce=False)
    lines = (tmp_path / "data" / "implications.txt").read_text().splitlines()
    assert lines[0] == "[B1] ∅ => E1: x = x   (background)"
    assert all(line.endswith(", new)") for line in lines if "E8:" in line or "E23:" in line)


def test_background_implications_are_checked_against_the_background_without_its_duals(tmp_path, monkeypatch):
    monkeypatch.setattr(etp_export, "EtpLaws", FakeLaws)
    run = results(tmp_path)
    # Only x = xx => x = (xx)x was given; the duality adds x = xx => x = x(xx).
    (run / "implications.json").write_text(json.dumps([
        {"premise": [], "conclusion": [1], "source": "background"},
        {"premise": [3], "conclusion": [23], "source": "background"},
    ]))
    export = etp_export.Export(run, tmp_path / "equations.json", [], tmp_path, background_label="ETP")
    origins = {tuple(r["conclusion"]): r.get("origin") for r in export.implications()}
    assert origins[(1,)] == origins[(23,)] == "ETP"
    law = {number: eq for eq, number in export.number.items()}
    assert export._direct([law[3]], [law[23]]) and not export._direct([law[3]], [law[8]])


def test_the_magmas_are_written_with_their_facts(tmp_path, monkeypatch):
    monkeypatch.setattr(etp_export, "EtpLaws", FakeLaws)
    export = etp_export.Export(results(tmp_path), tmp_path / "equations.json", [], tmp_path)
    etp_export.write(export, tmp_path / "data", reduce=False)
    assert (tmp_path / "data" / "magmas.txt").read_text().split("\n\n")[0] == (
        "Table [[0, 0], [0, 0]]\nSatisfies [1]\nRefutes [2, 3, 8, 23]")
    assert (tmp_path / "data" / "laws.txt").read_text().splitlines()[2] == "3: x = (x ◇ x)"
    # The one-element magma's row is the intersection of no others: kept.
    assert len(export.magmas(reduce=True)) == 2
