"""Unit tests for certificates of non-implication by Knuth-Bendix completion."""

import json

import pytest

from conceptual_exploration.core.implication import Implication
from conceptual_exploration.experts.base import Undecided
from explorations.equational_theories.completion import (
    CompletionExpert,
    CompletionFailed,
    Const,
    certified,
    complete,
    kbo_greater,
    law,
    lpo_greater,
    main,
    normal_form,
)
from explorations.equational_theories.explore import run_magma_exploration
from explorations.equational_theories.magma import Equation
from explorations.equational_theories.vampire import FreeMagma

X = "x"
XX = (X, X)


def test_the_order_prefers_larger_terms_with_at_least_the_same_variables():
    assert kbo_greater(XX, X)
    assert not kbo_greater(X, XX)
    assert not kbo_greater(("x", "y"), ("y", "x")) and not kbo_greater(("y", "x"), ("x", "y"))
    assert not kbo_greater((X, X), ("y", "y"))


def test_the_path_orders_orient_what_the_knuth_bendix_order_cannot():
    # x * x = (x * y) * z: the right side has fewer x.
    s = ((X, "y"), "z")
    assert not kbo_greater(s, XX) and not kbo_greater(XX, s)
    assert lpo_greater(s, XX) and not lpo_greater(XX, s)
    # x * ((y * x) * x) = (x * y) * y: only with the arguments compared right to left.
    u, v = (X, (("y", X), X)), ((X, "y"), "y")
    assert not lpo_greater(u, v) and not lpo_greater(v, u)
    assert lpo_greater(u, v, right_to_left=True) and not lpo_greater(v, u, right_to_left=True)
    assert not lpo_greater(XX, ("y", "y")) and not lpo_greater(("y", "y"), XX)


def test_completion_with_a_path_order():
    premise = [(XX, ((X, "y"), "z"))]
    with pytest.raises(CompletionFailed, match="cannot orient"):
        complete(premise)
    rules = complete(premise, order="lpo")
    assert rules == [((("x0", "x1"), "x2"), ("x0", "x0"))]
    # It implies (x * x) * y = x * x, but not x = x * x.
    assert certified(rules, premise, [((XX, "y"), XX), (X, XX)], order="lpo") == [False, True]
    with pytest.raises(ValueError, match="does not decrease"):
        certified(rules, premise, [])


def test_completion_names_a_term_that_takes_a_single_value():
    # x * x = y * y: no order compares the two sides, but every square is one element.
    premise = [(XX, ("y", "y"))]
    rules = complete(premise)
    assert rules == [(("x0", "x0"), Const("c0"))]
    # It implies (x * x) * z = (y * y) * z, but not x = x * x.
    assert certified(rules, premise, [((XX, "z"), (("y", "y"), "z")), (X, XX)]) == [False, True]
    # A variable named like the constant is not the constant.
    assert certified(rules, [(("c0", "c0"), ("y", "y"))], [("c0", ("c0", "c0"))]) == [True]
    for greater in (kbo_greater, lpo_greater):
        assert greater(XX, Const("c0")) and not greater(Const("c0"), X) and not greater(X, Const("c0"))
        assert greater(Const("c1"), Const("c0")) and not greater(Const("c0"), Const("c1"))


def test_a_constant_lets_completion_separate_e209_from_e203_e219_e231():
    # Before constants, only Vampire's saturation refuted this implication.
    premise = [law(Equation.parse(e)) for e in
               ("x = (x * (x * x)) * x", "x = (y * (x * x)) * y", "x = (y * (y * y)) * x")]
    rules = complete(premise)
    assert (("x0", ("x0", "x0")), Const("c0")) in rules
    assert certified(rules, premise, [law(Equation.parse("x = (x * (y * x)) * y"))]) == [True]


def test_completion_decides_the_consequences_of_idempotence():
    rules = complete([(X, XX)])
    assert normal_form((X, (X, X)), rules) == normal_form(X, rules)
    assert certified(rules, [(X, XX)], [((X, "y"), ("y", X)), (X, (X, (X, X)))]) == [True, False]


def test_a_law_and_its_consequences_are_not_separated():
    # x = (x * x) * x implies its instance x * x = ((x * x) * (x * x)) * (x * x),
    # but not idempotence.
    premise = [(X, (XX, X))]
    rules = complete(premise)
    assert certified(rules, premise, [(XX, ((XX, XX), XX)), (X, XX)]) == [False, True]


def test_invalid_certificates_are_rejected():
    with pytest.raises(ValueError, match="does not decrease"):
        certified([(X, XX)], [], [])
    with pytest.raises(ValueError, match="premise law"):
        certified([], [(X, XX)], [])
    # Both rules rewrite (x * y) * z, to different normal forms.
    with pytest.raises(ValueError, match="critical pair"):
        certified([((("x", "y"), "z"), "x"), ((("x", "y"), "z"), "z")], [], [])


def test_the_command_certifies_free_magmas_including_duals_recorded_under_their_original(tmp_path):
    laws = [("x = x * y", 4), ("x = y * x", 5), ("x = x * x", 3), ("x * y = y * x", 43)]
    equations = tmp_path / "laws.json"
    equations.write_text(json.dumps([{"equation": e, "id": n} for e, n in laws]))
    results = tmp_path / "results"
    results.mkdir()
    (results / "free_magmas.json").write_text(json.dumps([
        {"name": "F1", "dual_of": None, "premise": [3], "positive": [3], "negative": [4, 5, 43]},
        # As written before the fix: the dual of the free magma over x = x * y
        # with the original's premise.
        {"name": "F2", "dual_of": None, "premise": [4], "positive": [3, 4], "negative": [5, 43]},
        {"name": "F2^op", "dual_of": "F2", "premise": [4], "positive": [3, 5], "negative": [4, 43]},
    ]))
    main([str(results), "--equations", str(equations), "-o", str(tmp_path / "certificates.json")])
    certificates = {tuple(c["premise"]): c for c in json.loads((tmp_path / "certificates.json").read_text())}
    assert {key: (c["certified"], c["uncertified"]) for key, c in certificates.items()} == {
        (3,): ([4, 5, 43], []), (4,): ([5, 43], []), (5,): ([4, 43], []),
    }
    assert law(Equation.parse("x = x * y")) == ("x", ("x", "y"))


def test_the_command_tries_the_path_orders_when_the_knuth_bendix_order_fails(tmp_path):
    laws = [("x * x = (x * y) * z", 363), ("x * x = y * (z * x)", 318), ("x = x * x", 3)]
    equations = tmp_path / "laws.json"
    equations.write_text(json.dumps([{"equation": e, "id": n} for e, n in laws]))
    results = tmp_path / "results"
    results.mkdir()
    (results / "free_magmas.json").write_text(json.dumps([
        {"name": "F1", "dual_of": None, "premise": [3], "positive": [3], "negative": [318, 363]},
        {"name": "F2", "dual_of": None, "premise": [363], "positive": [363], "negative": [3, 318]},
        {"name": "F2^op", "dual_of": "F2", "premise": [318], "positive": [318], "negative": [3, 363]},
    ]))
    main([str(results), "--equations", str(equations), "-o", str(tmp_path / "certificates.json")])
    certificates = {tuple(c["premise"]): c for c in json.loads((tmp_path / "certificates.json").read_text())}
    assert {key: (c["order"], c["certified"]) for key, c in certificates.items()} == {
        (3,): ("kbo", [318, 363]), (363,): ("lpo", [3, 318]), (318,): ("lpo-rl", [3, 363]),
    }


def test_the_expert_proves_refutes_with_a_free_magma_or_falls_back():
    idempotent = Equation.parse("x = x * x", id=3)
    eq8 = Equation.parse("x = x * (x * x)", id=8)
    eq23 = Equation.parse("x = (x * x) * x", id=23)
    commutative = Equation.parse("x * y = y * x", id=43)
    expert = CompletionExpert([idempotent, eq8, eq23, commutative])

    assert expert.validate(Implication([idempotent], [eq8, eq23])) is None
    refutation = expert.validate(Implication([eq8], [idempotent]))
    assert refutation.object == FreeMagma(frozenset({eq8}))
    assert (refutation.positive, refutation.negative) == ({eq8}, {idempotent, eq23, commutative})
    # Commutativity cannot be oriented, and there is no fallback.
    assert expert.validate(Implication([commutative], [idempotent])) == Undecided()
    assert expert.answers == {"proved": 1, "free magma": 1, "completion failed": 1}


def test_an_exploration_of_one_variable_laws_by_completion(tmp_path):
    laws = [("x = x", 1), ("x = x * x", 3), ("x = x * (x * x)", 8), ("x = (x * x) * x", 23),
            ("x * x = x * (x * x)", 307), ("x * x = (x * x) * x", 359)]
    equations = tmp_path / "laws.json"
    equations.write_text(json.dumps([{"equation": e, "id": n} for e, n in laws]))
    state, base = run_magma_exploration(equations, report_interval=0, expert_kind="completion")
    assert not base.unconfirmed_implications and not base.open_questions
    assert all(isinstance(version.original, FreeMagma) for version in base.context.objects)
    by_id = {eq.id: eq for eq in base.attributes}
    assert by_id[8] in base.implications.closure({by_id[3]})
    assert by_id[3] not in base.implications.closure({by_id[8]})
