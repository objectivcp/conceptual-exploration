"""Unit tests for the files a magma exploration saves."""

import json

from conceptual_exploration import PartialObject
from conceptual_exploration.exploration.base import ExplorationBase
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
