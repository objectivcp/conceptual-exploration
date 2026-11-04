"""Unit tests for the Lean files in the ETP's form and for reading their
statements back."""

from explorations.equational_theories.certificates import parse_law, show
from explorations.equational_theories.lean_etp import (
    PART,
    Semigroup,
    _fixed,
    assembled,
    counterexample,
    facts_theorem,
    implication_theorem,
    parts,
)
from explorations.equational_theories.verify import _FACTS, _HYPOTHESIS, _THEOREM


class FakeLaws:
    """ETP numbers for a few laws, in the ETP's form."""

    numbers = {"x = y": 2, "x = (x * x)": 3, "x = (x * (x * x))": 8, "(x * (y * z)) = ((x * y) * z)": 4512}

    def number(self, law):
        for text, number in self.numbers.items():
            if parse_law(text) in (law, law[::-1]):
                return number
        raise KeyError(f"{show(law[0])} = {show(law[1])}")

    def definition(self, number):
        return parse_law(next(text for text, n in self.numbers.items() if n == number))


CERTIFICATE = {
    "premise": ["x = x * x", "x * (y * z) = (x * y) * z"],
    "conclusion": "x = x * (x * x)",
    "lemmas": [{"terms": ["y * y", "y"], "by": ["h0"]}],
    "terms": ["x", "x * x", "x * (x * x)"],
    "by": ["h0", "h0"],
}


def test_a_certificate_becomes_an_etp_theorem_with_the_laws_it_uses():
    name, text = implication_theorem(CERTIFICATE, FakeLaws())
    # Associativity is not used, so the theorem has one hypothesis and is an
    # equational result.
    assert name == "Equation3_implies_Equation8"
    assert text.startswith("@[equational_result]\ntheorem Equation3_implies_Equation8 (G : Type*) [Magma G] "
                           "(h3 : Equation3 G) : Equation8 G := by\n")
    assert "  conv => enter [1]; rw [h3 x]\n" in text
    assert "  conv => enter [1, 2]; rw [h3 x]" in text
    (hypotheses, conclusion), = _THEOREM.findall(text)
    assert _HYPOTHESIS.findall(hypotheses) == ["3"] and conclusion == "8"


def test_facts_are_stated_as_in_the_etp_and_read_back():
    semigroup = Semigroup("M1", [[1, 1], [1, 1]], [(3, 4), (4512, 8)], [2, 8])
    text = facts_theorem("source", semigroup, FakeLaws())
    assert "∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 4512] [2, 8]" in text
    # Each satisfied law is decided, and each refuted one at a counterexample.
    assert text.endswith("⟨Fin 2, «source M1», Finite.of_fintype _,\n"
                         "      by decideFin!,\n      by decideFin!,\n"
                         "      fun h => absurd (h 0 1) (by decideFin!),\n"
                         "      fun h => absurd (h 0) (by decideFin!)⟩\n")
    assert _FACTS.findall(text) == [("source M1", "3, 4512", "2, 8")]


def test_a_counterexample_has_the_least_largest_value():
    # x = x * x fails at 1 but not at 0, in the order of the law's variables
    table = [[0, 0], [0, 0]]
    assert counterexample(table, parse_law("x = x * x")) == (1,)
    assert counterexample(table, parse_law("x * y = y")) == (0, 1)


def test_a_costly_law_is_decided_in_parts_by_its_first_variables():
    assert _fixed(3, 4512, 10) == 0
    assert _fixed(3, 4512, 125) == 1  # 125 parts of 125² evaluations
    assert _fixed(5, 0, 31) == 2  # 31² parts of 31³ evaluations
    semigroup = Semigroup("M2", [[0] * 125] * 125, [(4512, 125 ** 3)], [2])
    pieces = parts("source", semigroup, 4512, FakeLaws())
    assert len(pieces) == 125 and all(cost <= PART for _, _, cost in pieces)
    assert pieces[7][1] == ("theorem «source M2 satisfies 4512 at 7» : ∀ y z : Fin 125, "
                            "((7 : Fin 125) ◇ (y ◇ z)) = (((7 : Fin 125) ◇ y) ◇ z) := by decideFin!\n")
    name, text = assembled("source", semigroup, 4512, FakeLaws())
    assert text.startswith(f"theorem {name} : Equation4512 (Fin 125) :=\n  fun x0 => match x0 with\n")
    assert text.endswith("    | ⟨124, _⟩ =>\n      «source M2 satisfies 4512 at 124»\n"
                         "    | ⟨_ + 125, h⟩ =>\n      absurd h (by omega)\n")
    # The facts take the law decided in parts first.
    facts = facts_theorem("source", semigroup, FakeLaws())
    assert "Facts G [4512] [2]" in facts and "Finite.of_fintype _,\n      «source M2 satisfies 4512»,\n" in facts


class FakeEtpLaws(FakeLaws):
    """FakeLaws as the ETP's laws for lean_etp.main, all declared by it."""

    def __init__(self, etp):
        self.used = set()
        self.declared = {2: "x = y", 3: "x = x ◇ x", 1: "x = x"}

    def number(self, law):
        number = 1 if law[0] == law[1] else super().number(law)
        self.used.add(number)
        return number

    def text(self, number):
        return self.declared[number]

    def definition(self, number):
        return parse_law(self.declared[number].replace("◇", "*"))


def test_a_magma_exploration_without_settings_becomes_lean_files_whose_statements_give_its_result(
        tmp_path, monkeypatch):
    import json

    import pytest

    from explorations.equational_theories import lean_etp
    from explorations.equational_theories.verify import VerificationError, verify_lean

    monkeypatch.setattr(lean_etp, "EtpLaws", FakeEtpLaws)
    etp = tmp_path / "etp"
    (etp / "equational_theories" / "Equations").mkdir(parents=True)
    (etp / "equational_theories" / "Equations" / "Basic.lean").write_text(
        "equation 1 := x = x\nequation 2 := x = y\nequation 3 := x = x ◇ x\n")
    equations = tmp_path / "equations.json"
    equations.write_text(json.dumps([{"id": 1, "equation": "x = x"}, {"id": 2, "equation": "x = y"},
                                     {"id": 3, "equation": "x = x * x"}]))
    results = tmp_path / "run"
    results.mkdir()
    # The free magma F1, without a table, is the only object satisfying x = x
    # alone; M3 is M1 again.
    (results / "context.cxt").write_text("B\n\n4\n3\n\nM1\nM2\nF1\nM3\nEq1\nEq2\nEq3\nX.X\nXXX\nX..\nX.X\n")
    (results / "magmas.json").write_text(json.dumps([{"name": "M1", "table": [[0, 0], [1, 1]]},
                                                     {"name": "M2", "table": [[0]]},
                                                     {"name": "M3", "table": [[0, 0], [1, 1]]}]))
    certificates = tmp_path / "certificates.jsonl"
    certificates.write_text(json.dumps({"premise": ["x = y"], "conclusion": "x = x * x",
                                        "terms": ["x", "x * x"], "by": ["h0"]}) + "\n")
    lean = tmp_path / "lean"
    lean_etp.main([str(results), str(certificates), "--etp", str(etp), "-o", str(lean), "--module", "Test",
                   "--equations-module", "Shared", "--equations", str(equations), "--axiom"])

    implications = (lean / "Test" / "Implications0.lean").read_text()
    assert implications.startswith("import Shared\n") and "namespace Test\n" in implications
    tables = (lean / "Test" / "MagmaTables.lean").read_text()
    assert "def «Test M1» :" in tables and "«Test M3»" not in tables
    assert (lean / "Test.lean").read_text().splitlines()[:3] == ["import Shared", "import Test.Implications0",
                                                                 "import Test.MagmaTables"]
    statements = [lean / "Test", lean / "Shared.lean"]
    with pytest.raises(VerificationError):
        verify_lean(results, statements, etp, False, tmp_path, equations, [])
    verify_lean(results, statements, etp, False, tmp_path, equations, [], free_rows=True)
