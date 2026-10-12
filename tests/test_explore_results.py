"""Unit tests for the files a magma exploration saves."""

from conceptual_exploration import PartialObject
from conceptual_exploration.exploration.base import ExplorationBase
from explorations.equational_theories.explore import save_results
from explorations.equational_theories.magma import Equation, Magma
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
