"""Unit tests for proof certificates, their checker and their reconstruction
from Vampire's proofs."""

import json
import lzma
import re
import shutil
import subprocess

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
from explorations.equational_theories.certify import (
    SavedProofs,
    certificate_from_tstp,
    certificates_from_tstp,
    certify,
    cover,
    mirrored,
    tptp_problem,
)

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


def test_the_cover_leaves_out_what_was_not_found(tmp_path):
    equations = [{"id": 1, "equation": "x = x", "class": []},
                 {"id": 3, "equation": "x = x * x", "class": []},
                 {"id": 43, "equation": "x * y = y * x", "class": []}]
    (tmp_path / "context.cxt").write_text("B\n\n1\n3\n\nM1\nEq1\nEq3\nEq43\nX.X\n", encoding="utf-8")
    (tmp_path / "implications.json").write_text(
        '[{"premise": [3], "conclusion": [43], "source": "unconfirmed"},'
        ' {"premise": [43], "conclusion": [3], "source": "rejected"},'
        ' {"premise": [1], "conclusion": [3], "source": "refuted"},'
        ' {"premise": [1], "conclusion": [43], "source": "tentatively rejected"}]', encoding="utf-8")
    assert cover(tmp_path, equations, []) == [([3], 43)]


def test_a_mirrored_certificate_proves_the_dual():
    certificate = mirrored(certificate_from_tstp(["x = x * x"], "x = x * (x * x)", PROOF))
    assert certificate["conclusion"] == "x = ((x * x) * x)"
    check_certificate(certificate)


def test_saved_proofs_certify_larger_premises_and_duals(tmp_path):
    path = tmp_path / "proofs.jsonl.xz"
    with lzma.open(path, "wt", encoding="utf-8") as file:
        file.write(json.dumps({"premise": ["x = x * x"], "conclusion": ["x = x * (x * x)"],
                               "prover": "vampire", "proof": PROOF}) + "\n")
    saved = SavedProofs(path, associative=False, processes=1)
    assert saved.certificate(["x * y = y * x", "x = x * x"], "y = y * (y * y)")["premise"] == ["x = x * x"]
    assert saved.certificate(["x = x * x"], "x = (x * x) * x")["conclusion"] == "x = ((x * x) * x)"
    assert saved.certificate(["x * y = y * x"], "x = x * (x * x)") is None


@pytest.mark.skipif(shutil.which("vampire") is None, reason="Vampire not installed")
def test_each_law_of_a_conjunction_gets_its_certificate(tmp_path):
    # As the expert asks: AVATAR splits the negated conjunction into a
    # branch for each law.
    premise = ["x * y = y * x", ASSOCIATIVITY, "x * x = x"]
    conclusion = ["x * (y * x) = x * y", "x * (y * z) = z * (y * x)", "(x * y) * (x * y) = y * x"]
    problem = tptp_problem(premise, "x = x").splitlines()[:-1]
    goal = " & ".join(f"({line.split('conjecture, ')[1][:-2]})"
                      for law in conclusion for line in tptp_problem([], law).splitlines())
    (tmp_path / "t.p").write_text("\n".join(problem + [f"fof(goal, conjecture, {goal})."]) + "\n")
    output = subprocess.run(["vampire", "--mode", "casc", "--time_limit", "10", str(tmp_path / "t.p")],
                            capture_output=True, text=True).stdout
    certificates = certificates_from_tstp(premise, conclusion, output)
    assert sorted(c["conclusion"] for c in certificates) == sorted(conclusion)


# Vampire's proof without AVATAR of a conclusion of two laws, as the expert
# asks: the first law's literal is removed by subsumption resolution, and
# the second refuted on its own.
TWO_LAWS = """% SZS output start Proof for t
fof(f2,axiom,(
  ! [X0,X1] : m(X0,m(X1,X0)) = m(X0,m(X1,X1))),
  file('t.p','premise1')).
fof(f3,axiom,(
  ! [X0,X1] : m(X0,m(X1,X1)) = m(X1,m(X0,X0))),
  file('t.p','premise2')).
fof(f5,conjecture,(
  ! [X0,X1] : m(X0,m(X1,X0)) = m(X1,m(X0,X0)) & ! [X0,X1] : m(X0,m(X1,X0)) = m(X1,m(X0,X1))),
  file('t.p','conclusion')).
fof(f6,negated_conjecture,(
  ~(! [X0,X1] : m(X0,m(X1,X0)) = m(X1,m(X0,X0)) & ! [X0,X1] : m(X0,m(X1,X0)) = m(X1,m(X0,X1)))),
  inference(negated_conjecture,[status(cth)],[f5])).
fof(f7,plain,(
  ~(! [X0,X1] : m(X0,m(X1,X0)) = m(X1,m(X0,X0)) & ! [X2,X3] : m(X2,m(X3,X2)) = m(X3,m(X2,X3)))),
  inference(rectify,[],[f6])).
fof(f8,plain,(
  ? [X0,X1] : m(X0,m(X1,X0)) != m(X1,m(X0,X0)) | ? [X2,X3] : m(X2,m(X3,X2)) != m(X3,m(X2,X3))),
  inference(ennf_transformation,[],[f7])).
fof(f9,plain,(
  m(sK0,m(sK1,sK0)) != m(sK1,m(sK0,sK0)) | m(sK2,m(sK3,sK2)) != m(sK3,m(sK2,sK3))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3]),skolemize(X0,sK0),skolemize(X1,sK1),skolemize(X2,sK2),skolemize(X3,sK3)],[f8])).
fof(f10,plain,(
  m(sK0,m(sK1,sK0)) != m(sK1,m(sK0,sK0)) | m(sK2,m(sK3,sK2)) != m(sK3,m(sK2,sK3))),
  inference(cnf_transformation,[],[f9])).
fof(f13,plain,(
  ( ! [X0,X1] : (m(X0,m(X1,X1)) = m(X1,m(X0,X0))) )),
  inference(cnf_transformation,[],[f3])).
fof(f14,plain,(
  ( ! [X0,X1] : (m(X0,m(X1,X0)) = m(X0,m(X1,X1))) )),
  inference(cnf_transformation,[],[f2])).
fof(f15,plain,(
  m(sK0,m(sK1,sK0)) != m(sK0,m(sK1,sK1)) | m(sK2,m(sK3,sK2)) != m(sK3,m(sK2,sK3))),
  inference(forward_demodulation,[],[f10,f13])).
fof(f16,plain,(
  m(sK2,m(sK3,sK2)) != m(sK3,m(sK2,sK3))),
  inference(forward_subsumption_resolution,[],[f15,f14])).
fof(f17,plain,(
  m(sK2,m(sK3,sK2)) != m(sK3,m(sK2,sK2))),
  inference(forward_demodulation,[],[f16,f14])).
fof(f18,plain,(
  m(sK2,m(sK3,sK2)) != m(sK2,m(sK3,sK3))),
  inference(forward_demodulation,[],[f17,f13])).
fof(f19,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f18,f14])).
% SZS output end Proof for t"""


def test_each_law_of_a_clause_of_several_literals_gets_its_certificate():
    premise = ["x = x", "(x * (y * x)) = (x * (y * y))", "(x * (y * y)) = (y * (x * x))", ASSOCIATIVITY]
    conclusion = ["(x * (y * x)) = (y * (x * x))", "(x * (y * x)) = (y * (x * y))"]
    certificates = certificates_from_tstp(premise, conclusion, TWO_LAWS)
    assert sorted(c["conclusion"] for c in certificates) == conclusion


# A proof with inequality splitting: the negated conclusion s != t becomes
# ~sP1(s) and sP1(t), whose arguments are rewritten until they meet.
SPLIT = """% SZS output start Proof for t
fof(f1,axiom,(
  ! [X0] : m(X0,X0) = m(m(m(X0,X0),X0),X0)),
  file('t.p','premise0')).
fof(f2,axiom,(
  ! [X0] : X0 = m(m(X0,X0),m(X0,X0))),
  file('t.p','premise1')).
fof(f3,conjecture,(
  ! [X0] : X0 = m(m(X0,m(X0,X0)),m(X0,X0))),
  file('t.p','conclusion')).
fof(f4,negated_conjecture,(
  ~ ! [X0] : X0 = m(m(X0,m(X0,X0)),m(X0,X0))),
  inference(negated_conjecture,[status(cth)],[f3])).
fof(f5,plain,(
  ? [X0] : m(m(X0,m(X0,X0)),m(X0,X0)) != X0),
  inference(ennf_transformation,[],[f4])).
fof(f6,plain,(
  sK0 != m(m(sK0,m(sK0,sK0)),m(sK0,sK0))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X0,sK0)],[f5])).
fof(f7,plain,(
  ( ! [X0] : (m(X0,X0) = m(m(m(X0,X0),X0),X0)) )),
  inference(cnf_transformation,[],[f1])).
fof(f8,plain,(
  ( ! [X0] : (m(m(X0,X0),m(X0,X0)) = X0) )),
  inference(cnf_transformation,[],[f2])).
fof(f9,plain,(
  sK0 != m(m(sK0,m(sK0,sK0)),m(sK0,sK0))),
  inference(cnf_transformation,[],[f6])).
fof(f10,definition,(
  ~sP1(sK0)),
  introduced(definition,[new_symbols(definition,[sP1])],[inequality_splitting_name_introduction])).
fof(f11,plain,(
  sP1(m(m(sK0,m(sK0,sK0)),m(sK0,sK0)))),
  inference(inequality_splitting,[],[f9,f10])).
fof(f12,definition,(
  sF2 = m(sK0,sK0)),
  introduced(definition,[new_symbols(definition,[sF2])],[function_definition])).
fof(f13,plain,(
  m(sK0,sK0) = sF2),
  inference(reorient_equations,[],[f12])).
fof(f14,definition,(
  sF3 = m(sK0,sF2)),
  introduced(definition,[new_symbols(definition,[sF3])],[function_definition])).
fof(f15,plain,(
  m(sK0,sF2) = sF3),
  inference(reorient_equations,[],[f14])).
fof(f16,definition,(
  sF4 = m(sF3,sF2)),
  introduced(definition,[new_symbols(definition,[sF4])],[function_definition])).
fof(f17,plain,(
  m(sF3,sF2) = sF4),
  inference(reorient_equations,[],[f16])).
fof(f18,plain,(
  sP1(sF4)),
  inference(definition_folding,[],[f11,f17,f13,f15,f13])).
fof(f19,plain,(
  sK0 = m(sF2,sF2)),
  inference(superposition,[],[f8,f13])).
fof(f23,plain,(
  sK0 = m(m(sK0,sF2),sF2)),
  inference(superposition,[],[f7,f19])).
fof(f24,plain,(
  sK0 = m(sF3,sF2)),
  inference(forward_demodulation,[],[f23,f15])).
fof(f25,plain,(
  sK0 = sF4),
  inference(forward_demodulation,[],[f24,f17])).
fof(f28,plain,(
  ~sP1(sF4)),
  inference(superposition,[],[f10,f25])).
fof(f29,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f28,f18])).
% SZS output end Proof for t"""


def test_the_halves_of_a_split_inequality_meet_in_a_certificate():
    premise = ["(x * x) = (((x * x) * x) * x)", "x = ((x * x) * (x * x))"]
    (certificate,) = certificates_from_tstp(premise, ["x = ((x * (x * x)) * (x * x))"], SPLIT)
    assert certificate["terms"][0] == "x"
