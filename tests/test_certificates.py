"""Unit tests for proof certificates, their checker and their reconstruction
from Vampire's proofs."""

import re
import shutil

import pytest

from explorations.equational_theories.certificates import (
    CertificateError,
    check_certificate,
    is_step,
    parse_law,
    parse_term,
    show,
    word_law,
)
from explorations.equational_theories.certify import certificate_from_tstp, certify, cover, tptp_problem

ASSOCIATIVITY = "(x * (y * z)) = ((x * y) * z)"

# Vampire's proof in casc mode of x = x * (x * x) from x = x * x, with the
# constants of its definitions and a forward subsumption resolution.
PROOF = """% SZS output start Proof for t
fof(f1,axiom,(
  ! [X0] : X0 = m(X0,X0)),
  file('t.p','h0')).
fof(f3,conjecture,(
  ! [X0] : X0 = m(X0,m(X0,X0))),
  file('t.p','goal')).
fof(f4,negated_conjecture,(
  ~ ! [X0] : X0 = m(X0,m(X0,X0))),
  inference(negated_conjecture,[status(cth)],[f3])).
fof(f5,plain,(
  ? [X0] : m(X0,m(X0,X0)) != X0),
  inference(ennf_transformation,[],[f4])).
fof(f6,plain,(
  sK0 != m(sK0,m(sK0,sK0))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X0,sK0)],[f5])).
fof(f7,plain,(
  ( ! [X0] : (m(X0,X0) = X0) )),
  inference(cnf_transformation,[],[f1])).
fof(f9,plain,(
  sK0 != m(sK0,m(sK0,sK0))),
  inference(cnf_transformation,[],[f6])).
fof(f10,definition,(
  sF1 = m(sK0,sK0)),
  introduced(definition,[new_symbols(definition,[sF1])],[function_definition])).
fof(f11,plain,(
  m(sK0,sK0) = sF1),
  inference(reorient_equations,[],[f10])).
fof(f12,definition,(
  sF2 = m(sK0,sF1)),
  introduced(definition,[new_symbols(definition,[sF2])],[function_definition])).
fof(f13,plain,(
  m(sK0,sF1) = sF2),
  inference(reorient_equations,[],[f12])).
fof(f14,plain,(
  sK0 != sF2),
  inference(definition_folding,[],[f9,f13,f11])).
fof(f15,plain,(
  sK0 = sF1),
  inference(forward_demodulation,[],[f11,f7])).
fof(f16,plain,(
  m(sK0,sK0) = sF2),
  inference(superposition,[],[f13,f15])).
fof(f17,plain,(
  sK0 = sF2),
  inference(forward_demodulation,[],[f16,f7])).
fof(f18,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f17,f14])).
% SZS output end Proof for t
"""


def test_terms_are_parsed_and_shown():
    assert parse_term("x * y * z") == (("x", "y"), "z")
    assert parse_term("(x * (y * z))") == ("x", ("y", "z"))
    assert show(parse_term("x * (y * sK0)")) == "(x * (y * sK0))"
    assert word_law("xxy = yx") == (("x", ("x", "y")), ("y", "x"))
    with pytest.raises(ValueError):
        parse_term("x * ")


def test_a_step_rewrites_one_subterm_with_an_instance_of_the_law():
    law = parse_law("x * x = x")
    assert is_step(parse_term("a * ((b * c) * (b * c))"), parse_term("a * (b * c)"), law)
    assert is_step(parse_term("a * (b * c)"), parse_term("a * ((b * c) * (b * c))"), law)
    assert not is_step(parse_term("a * (b * c)"), parse_term("a * ((b * b) * (b * c))"), law)
    # Two subterms rewritten at once are two steps.
    assert not is_step(parse_term("(a * a) * (b * b)"), parse_term("a * b"), law)


def test_a_right_certificate_is_accepted():
    certificate = {
        "premise": ["x = x * x"],
        "conclusion": "x = x * (x * x)",
        "lemmas": [{"terms": ["y * y", "y"], "by": ["h0"]}],
        "terms": ["x", "x * x", "x * (x * x)"],
        "by": ["h0", "h0"],
    }
    premise, conclusion = check_certificate(certificate)
    assert premise == [("x", ("x", "x"))]
    assert conclusion == ("x", ("x", ("x", "x")))


@pytest.mark.parametrize("change, message", [
    ({"by": ["h0", "h1"]}, "no h1"),
    ({"terms": ["x", "x * x", "x * (x * y)"]}, "does not follow"),
    ({"conclusion": "x = (x * x) * x"}, re.escape("not x = (x * x) * x")),
    ({"by": ["h0"]}, "3 terms but 1 citations"),
])
def test_a_wrong_certificate_is_rejected(change, message):
    certificate = {"premise": ["x = x * x"], "conclusion": "x = x * (x * x)",
                   "terms": ["x", "x * x", "x * (x * x)"], "by": ["h0", "h0"], **change}
    with pytest.raises(CertificateError, match=message):
        check_certificate(certificate)


def test_a_lemma_holds_for_all_values_of_its_variables():
    # A lemma about a constant of its chain is used as a law.
    certificate = {
        "premise": ["x * y = x"],
        "conclusion": "(x * y) * z = x",
        "lemmas": [{"terms": ["(c * d) * e", "c * d", "c"], "by": ["h0", "h0"]}],
        "terms": ["(x * y) * z", "x"],
        "by": ["l0"],
    }
    check_certificate(certificate)


def test_a_vampire_proof_becomes_a_checked_certificate():
    certificate = certificate_from_tstp(["x = x * x"], "x = x * (x * x)", PROOF)
    assert certificate["premise"] == ["x = x * x"]
    assert certificate["conclusion"] == "x = x * (x * x)"
    assert certificate["terms"][0] == "x" and certificate["terms"][-1] == "(x * (x * x))"
    check_certificate(certificate)


def test_the_problem_names_the_premise_laws_in_order():
    problem = tptp_problem(["x = x * x", ASSOCIATIVITY], "x = y")
    assert problem.splitlines() == [
        "fof(h0, axiom, ![Vx]: Vx = m(Vx,Vx)).",
        "fof(h1, axiom, ![Vx,Vy,Vz]: m(Vx,m(Vy,Vz)) = m(m(Vx,Vy),Vz)).",
        "fof(goal, conjecture, ![Vx,Vy]: Vx = Vy).",
    ]


@pytest.mark.skipif(shutil.which("vampire") is None, reason="Vampire not installed")
@pytest.mark.parametrize("premise, law", [
    # Vampire's simultaneous superposition rewrites every occurrence of the
    # subterm it unifies.
    (["x * x = y * (x * y)", ASSOCIATIVITY], "x * (y * x) = z * (y * y)"),
    (["x * y = y * x", ASSOCIATIVITY], "x * (y * z) = z * (y * x)"),
    (["x * y = x"], "(x * y) * z = x * w"),
])
def test_vampire_proofs_are_certified(premise, law):
    certificate = certify(premise, law, 10)
    assert isinstance(certificate, dict), certificate
    check_certificate(certificate)


def test_the_cover_takes_the_strongest_laws_first(tmp_path):
    equations = [{"id": 1, "equation": "x = x", "class": []},
                 {"id": 2, "equation": "x = y", "class": []},
                 {"id": 3, "equation": "x = x * x", "class": []},
                 {"id": 43, "equation": "x * y = y * x", "class": []}]
    (tmp_path / "context.cxt").write_text(
        "B\n\n2\n4\n\nM1\nM2\nEq1\nEq2\nEq3\nEq43\nX.XX\nX..X\n", encoding="utf-8")
    (tmp_path / "implications.json").write_text(
        '[{"premise": [3], "conclusion": [43], "source": "confirmed"},'
        ' {"premise": [2], "conclusion": [43, 3], "source": "confirmed"}]', encoding="utf-8")
    # Eq3 holds in fewer objects than Eq43, so it is taken first, and with
    # Eq3 => Eq43, Eq2 => Eq43 follows.
    assert cover(tmp_path, equations, []) == [([3], 43), ([2], 3)]
