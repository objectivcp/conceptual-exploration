"""Unit tests for the expert that answers magma questions with Vampire."""

import shutil

import pytest

from conceptual_exploration import Implication
from explorations.equational_theories.magma import Equation, Magma
from explorations.equational_theories.vampire import VampireExpert, parse_model, tptp_law

pytestmark = pytest.mark.skipif(shutil.which("vampire") is None, reason="Vampire not installed")


def implication(premise, conclusion):
    return Implication(
        frozenset(map(Equation.parse, premise)), frozenset(map(Equation.parse, conclusion))
    )


def test_tptp_law_quantifies_the_variables():
    assert tptp_law(Equation.parse("x * y = y * x")) == "![Vx,Vy]: m(Vx,Vy) = m(Vy,Vx)"


def test_parse_model_reads_a_cayley_table():
    output = "\n".join(
        f"m('fmb_$i_{a + 1}','fmb_$i_{b + 1}') = 'fmb_$i_{(a + b) % 2 + 1}'"
        for a in range(2) for b in range(2)
    )
    assert parse_model(output) == ((0, 1), (1, 0))
    assert parse_model("no model") is None


def test_proves_a_valid_implication():
    expert = VampireExpert(initial_magmas=[], prove_time_limit=5, model_time_limit=5)
    # From x = (x * x) * (x * x) and x * x = ((x * x) * x) * x by substitution and rewriting.
    question = implication(
        ["x = (x * x) * (x * x)", "x * x = ((x * x) * x) * x"], ["x = (x * (x * x)) * (x * x)"]
    )
    assert expert.validate(question) is None
    assert expert.is_conclusive()
    assert expert.last_status == "proved"


def test_refutes_with_a_checked_model_that_joins_the_pool():
    expert = VampireExpert(initial_magmas=[], prove_time_limit=5, model_time_limit=5)
    question = implication(["x * x = x * (x * x)"], ["x = x * x"])
    counterexample = expert.validate(question)
    assert counterexample is not None and counterexample.refutes(question)
    assert expert.last_status == "model"
    assert expert.cached_magmas == [counterexample.object]
    # Asked again, the pool answers without running Vampire.
    assert expert.validate(question).object == counterexample.object
    assert expert.last_status == "pool"
    assert expert.answers == {"model": 1, "pool": 1}


def test_pool_is_checked_first():
    constant = Magma.constant(2, 0)
    expert = VampireExpert(initial_magmas=[constant])
    counterexample = expert.validate(implication([], ["x = x * x"]))
    assert counterexample.object == constant
    assert expert.last_status == "pool"


def scripted(expert, answer):
    """Make the expert's Vampire calls answer through `answer(conjecture, options)`,
    which gets the problem's conjecture line. Returns the list of model
    searches made, as their time limits."""
    searches = []

    def run(problem, options, time_limit):
        conjecture = next(line for line in problem.splitlines() if "conjecture" in line)
        if "fmb" in options:
            searches.append(time_limit)
        return answer(conjecture, options)
    expert._run = run
    return searches


IDEMPOTENT = "m(Vx,Vx)"
QUESTION = implication(["x * x = x * (x * x)"], ["x = x * x", "x = x * (x * x)"])
# The constant magma on two elements, which refutes QUESTION.
CONSTANT_MODEL = "\n".join(
    f"m('fmb_$i_{a}','fmb_$i_{b}') = 'fmb_$i_1'" for a in (1, 2) for b in (1, 2)
)


def laws(whole, idempotent, other="Theorem", model=""):
    """Answers: `whole` for the conjunction, `idempotent` for x = x * x alone,
    `other` for the other laws, and `model` for every model search."""
    def answer(conjecture, options):
        if "fmb" in options:
            return ("CounterSatisfiable", model) if model else ("Timeout", "")
        if "&" in conjecture:
            return whole, ""
        return (idempotent if conjecture.endswith(f"Vx = {IDEMPOTENT})).") else other), ""
    return answer


def test_a_free_magma_refutes_when_a_law_fails():
    expert = VampireExpert(initial_magmas=[], workers=2)
    # Shown false as a whole, no finite model in the brief search, and each law
    # decided on its own: x = x * x fails, x = x * (x * x) is proved.
    searches = scripted(expert, laws("CounterSatisfiable", "CounterSatisfiable"))
    counterexample = expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion)
    assert counterexample.refutes(QUESTION)
    assert expert.last_status == "free magma"
    assert counterexample.negative == {Equation.parse("x = x * x")}
    assert Equation.parse("x = x * (x * x)") in counterexample.positive
    # Only the brief model search ran.
    assert searches == [expert.quick_model_time_limit]


def test_proving_each_law_proves_the_implication():
    expert = VampireExpert(initial_magmas=[], workers=2)
    scripted(expert, laws("Timeout", "Theorem"))
    assert expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion) is None
    assert expert.is_conclusive()
    assert expert.last_status == "proved"


def test_the_full_model_search_runs_when_the_free_magma_does_not_refute():
    expert = VampireExpert(initial_magmas=[], workers=2)
    model = iter(["", CONSTANT_MODEL])

    def answer(conjecture, options):
        if "fmb" in options:
            found = next(model)
            return ("CounterSatisfiable", found) if found else ("Timeout", "")
        return laws("CounterSatisfiable", "Timeout")(conjecture, options)
    searches = scripted(expert, answer)
    counterexample = expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion)
    assert counterexample.refutes(QUESTION)
    assert expert.last_status == "model"
    assert searches == [expert.quick_model_time_limit, expert.model_time_limit]


def test_shown_false_but_undecided_leaves_the_question_open():
    from conceptual_exploration import Undecided

    expert = VampireExpert(initial_magmas=[], workers=2)
    # False as a whole; x = x * (x * x) proved, x = x * x undecided.
    scripted(expert, laws("CounterSatisfiable", "Timeout"))
    answer = expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion)
    assert isinstance(answer, Undecided) and not answer.unconfirmed
    assert answer.proved == {Equation.parse("x = x * (x * x)")}
    assert not answer.object.refutes(QUESTION)
    assert expert.last_status == "open"


def test_undecided_rest_is_unconfirmed_when_nothing_speaks_against_it():
    from conceptual_exploration import Undecided

    expert = VampireExpert(initial_magmas=[], workers=2)
    # Undecided as a whole; x = x * (x * x) proved, x = x * x undecided.
    scripted(expert, laws("Timeout", "Timeout"))
    answer = expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion)
    assert isinstance(answer, Undecided) and answer.unconfirmed
    assert answer.proved == {Equation.parse("x = x * (x * x)")}
    assert expert.last_status == "unconfirmed"
    # Asked again, the answer is remembered.
    expert._run = None
    assert expert.validate(QUESTION, QUESTION.premise | QUESTION.conclusion) == answer


def test_nothing_decided_is_unconfirmed():
    expert = VampireExpert(initial_magmas=[], workers=2)
    scripted(expert, lambda conjecture, options: ("Timeout", ""))
    question = implication(["x * x = x * (x * x)"], ["x = x * x"])
    answer = expert.validate(question)
    assert answer.unconfirmed and not answer.proved
    assert expert.last_status == "unconfirmed"
