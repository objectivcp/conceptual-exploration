"""Unit tests for reading the data of the Equational Theories Project."""

import json

import pytest

from conceptual_exploration.core.implication import Implication
from conceptual_exploration.exploration.base import ImplicationSource
from explorations.equational_theories.etp import (
    EtpLaws,
    ImplicationGraph,
    canonical_form,
    graph_background,
    load_magmas,
    load_tables,
    main,
)
from explorations.equational_theories.explore import run_magma_exploration
from explorations.equational_theories.magma import ETP, Equation

# The first five laws of the ETP, and which implies which: everything implies
# x = x, x = y implies everything, and x = x * y and x = y * x imply x = x * x.
LAWS = ["x = x", "x = y", "x = x ◇ x", "x = x ◇ y", "x = y ◇ x"]
IMPLIES = {(a, b) for a in range(1, 6) for b in range(1, 6)
           if a == b or b == 1 or a == 2 or (a in (4, 5) and b == 3)}


def rle(outcomes):
    runs = []
    for value in outcomes:
        if runs and runs[-2] == value:
            runs[-1] += 1
        else:
            runs += [value, 1]
    return runs


@pytest.fixture
def etp(tmp_path):
    equations = tmp_path / "equations.txt"
    equations.write_text("\n".join(LAWS) + "\n", encoding="utf-8")
    graph = tmp_path / "graph.json"
    outcomes = [7 if (a, b) in IMPLIES else 6 for a in range(1, 6) for b in range(1, 6)]
    graph.write_text(json.dumps({"rle_encoded_array": rle(outcomes)}))
    return equations, graph


def test_laws_are_the_same_whatever_their_variables_and_sides():
    assert canonical_form(Equation.parse("x = y * x")) == canonical_form(Equation.parse("b * a = a"))
    assert canonical_form(Equation.parse("x = y * x")) != canonical_form(Equation.parse("x = x * y"))


def test_laws_are_numbered_by_line_and_found_by_their_text(etp):
    laws = EtpLaws.load(etp[0])
    assert laws.law(4) == Equation.parse("x = x * y", id=4)
    assert laws.id_of(Equation.parse("b * a = a")) == 5
    assert laws.id_of(Equation.parse("x * y = y * x")) is None
    assert [eq.id for eq in laws.with_duals([4])] == [4, 5]


def test_an_id_that_is_not_the_etp_number_is_an_error(etp):
    laws = EtpLaws.load(etp[0])
    with pytest.raises(ValueError, match="Eq4"):
        laws.identify([Equation.parse("x = y * x", id=4)])


def test_the_graph_tells_which_law_implies_which(etp):
    graph = ImplicationGraph.load(etp[1])
    assert graph.size == 5
    assert graph.implies(4, 3) and not graph.implies(3, 4)


def test_an_undecided_implication_is_an_error():
    graph = ImplicationGraph(bytes([7, 8, 6, 7]), 2)
    with pytest.raises(ValueError, match="Eq1 implies Eq2"):
        graph.implies(1, 2)


def test_the_background_has_the_single_premise_implications(etp):
    laws, graph = EtpLaws.load(etp[0]), ImplicationGraph.load(etp[1])
    trivial = Equation.parse("y = y")
    idempotent = Equation.parse("x = x * x", id=3)
    left_zero = Equation.parse("x = x * y")
    commutative = Equation.parse("x * y = y * x")
    background = graph_background([trivial, idempotent, left_zero, commutative], graph, laws)
    assert background == [
        Implication([], [trivial]),
        Implication([left_zero], [idempotent]),
    ]


def test_tables_are_read_from_etp_files(tmp_path):
    path = tmp_path / "refutations.txt"
    path.write_text(
        "Table [[0, 1], [1, 0]]\n"
        "Proves [1, 43]\n"
        "3 [[0,0],[0,0]]\n"
        "4 [[0,1],[1,0]]\n",
        encoding="utf-8",
    )
    magmas = load_tables(path)
    assert [m.table for m in magmas] == [((0, 1), (1, 0)), ((0, 0), (0, 0))]
    assert magmas[0].name == "refutations:1"
    assert load_magmas(path) == magmas


def test_the_command_writes_the_laws_with_their_duals(etp, tmp_path):
    output = tmp_path / "laws.json"
    main([str(etp[0]), "4", "-o", str(output)])
    laws = ETP.load_equations(output)
    assert [(eq.id, f"{eq.lhs} = {eq.rhs}") for eq in laws] == [
        (4, "x = (x * y)"), (5, "x = (y * x)"),
    ]


def test_an_exploration_takes_the_graph_as_background(etp, tmp_path):
    equations = tmp_path / "laws.json"
    main([str(etp[0]), "3", "4", "-o", str(equations)])
    _, base = run_magma_exploration(
        equations, report_interval=0, max_search_size=2,
        etp_graph=etp[1], etp_equations=etp[0],
    )
    background = {i for i, s in base.implication_sources.items() if s is ImplicationSource.BACKGROUND}
    idempotent = Equation.parse("x = (x * x)", id=3)
    assert Implication([Equation.parse("x = (x * y)", id=4)], [idempotent]) in background
    assert not base.accepted_implications
