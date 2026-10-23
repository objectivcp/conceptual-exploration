"""Unit tests for the files a magma exploration saves."""

import json

from conceptual_exploration import Implication, PartialObject
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from explorations.equational_theories.etp import EtpRefutation
from explorations.equational_theories.explore import save_results
from explorations.equational_theories.magma import ETP, Equation, Magma
from explorations.equational_theories.vampire import FreeMagma


def test_partial_rows_are_saved_with_question_marks(tmp_path):
    idempotent = Equation.parse("x = x * x", id=3)
    commutative = Equation.parse("x * y = y * x", id=43)
    equations = [idempotent, commutative]
    base = ExplorationBase(attributes=equations)
    constant = Magma.constant(2, 0)
    base.add_counterexample(PartialObject(constant, {commutative}, {idempotent}))
    base.add_counterexample(PartialObject(FreeMagma(frozenset({idempotent})), {idempotent}, set()))

    save_results(base, equations, tmp_path, "test")

    complete = (tmp_path / "context.cxt").read_text().splitlines()
    partial = (tmp_path / "partial_context.cxt").read_text().splitlines()
    assert complete == ["B", "", "1", "2", "", "M1", "Eq3", "Eq43", ".X"]
    assert partial == ["B", "", "2", "2", "", "M1", "F1", "Eq3", "Eq43", ".X", "X?"]


def test_the_duals_of_free_magmas_and_refutations_are_saved_with_their_own_laws(tmp_path):
    left_zero = Equation.parse("x = x * y", id=4)
    right_zero = Equation.parse("x = y * x", id=5)
    idempotent = Equation.parse("x = x * x", id=3)
    equations = [idempotent, left_zero, right_zero]
    base = ExplorationBase(attributes=equations, mappings=[ETP.get_duality_mapping(equations)])
    base.add_counterexample(PartialObject(FreeMagma(frozenset({left_zero})), {left_zero}, {right_zero}))
    base.add_counterexample(PartialObject(EtpRefutation(4, 5), {left_zero}, {right_zero}))

    save_results(base, equations, tmp_path, "test")

    free = {f["name"]: f for f in json.loads((tmp_path / "free_magmas.json").read_text())}
    assert (free["F1"]["premise"], free["F1^op"]["premise"]) == ([4], [5])
    refutations = {r["name"]: r for r in json.loads((tmp_path / "etp_refutations.json").read_text())}
    assert (refutations["R1"]["refutes"], refutations["R1^op"]["refutes"]) == ([4, 5], [5, 4])


def test_with_associativity_assumed_the_duality_compares_words(tmp_path):
    from explorations.equational_theories.explore import run_magma_exploration

    laws = [
        {"id": 66, "equation": "x = (y * (x * (y * y)))"},
        {"id": 73, "equation": "x = (y * (y * (x * y)))"},
        {"id": 4512, "equation": "(x * (y * z)) = ((x * y) * z)"},
    ]
    path = tmp_path / "laws.json"
    path.write_text(json.dumps(laws))
    run_magma_exploration(path, max_search_size=2, report_interval=0, results_dir=tmp_path / "out", axioms=[4512])
    rules = json.loads((tmp_path / "out" / "implications.json").read_text())
    assert {r["source"] for r in rules} >= {"mapped"}


def test_the_rules_are_saved_with_their_images_and_laws_as_words_for_semigroups(tmp_path):
    idempotent = Equation.parse("x = x * x", id=3)
    other = Equation.parse("x = x * (x * x)", id=8)
    left, right = Equation.parse("x = x * y", id=4), Equation.parse("x = y * x", id=5)
    laws = [idempotent, left, right, other, Equation.parse("x * (y * z) = (x * y) * z", id=4512)]
    background = [Implication([left], [idempotent]), Implication([right], [idempotent])]
    base = ExplorationBase(attributes=laws, background_implications=background,
                           mappings=[ETP.get_duality_mapping(laws, associative=True)])
    base.accept(Implication([idempotent], [other]), ImplicationSource.CONFIRMED)
    base.add_background(Implication([], [laws[-1]]))
    save_results(base, laws, tmp_path, "test", words=True)
    rules = (tmp_path / "simplified_implications.txt").read_text().splitlines()
    assert rules[2:] == [
        "Background (2 rules and their images):",
        "[B1] Eq5: x = yx  =>  Eq3: x = xx   (background)",
        "[B1^op] Eq4: x = xy  =>  Eq3: x = xx   (mapped background from [B1])",
        "[B2] ∅  =>  Eq4512: (x * (y * z)) = ((x * y) * z)   (background)",
        "",
        "Rules (1 rules, as numbered in exploration.log, and their images):",
        "[1] Eq3: x = xx  =>  Eq8: x = xxx   (confirmed)",
    ]
    save_results(base, laws, tmp_path, "test")
    assert (tmp_path / "simplified_implications.txt").read_text().splitlines()[-1] == (
        "[1] Eq3: x = (x * x)  =>  Eq8: x = (x * (x * x))   (confirmed)"
    )
