"""Unit tests for certificates of non-implication by Knuth-Bendix completion."""

import json

import pytest

from explorations.equational_theories.completion import (
    certified,
    complete,
    kbo_greater,
    law,
    main,
    normal_form,
)
from explorations.equational_theories.magma import Equation

X = "x"
XX = (X, X)


def test_the_order_prefers_larger_terms_with_at_least_the_same_variables():
    assert kbo_greater(XX, X)
    assert not kbo_greater(X, XX)
    assert not kbo_greater(("x", "y"), ("y", "x")) and not kbo_greater(("y", "x"), ("x", "y"))
    assert not kbo_greater((X, X), ("y", "y"))


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
