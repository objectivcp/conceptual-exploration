"""Unit tests for reading the data of the Equational Theories Project."""

import json

import pytest

from conceptual_exploration.core.implication import Implication
from conceptual_exploration.exploration.base import ImplicationSource
from explorations.equational_theories.etp import (
    EtpLaws,
    EtpRefutation,
    ImplicationGraph,
    canonical_form,
    graph_background,
    graph_refutations,
    load_magmas,
    load_tables,
    main,
    order,
    representatives,
    semigroup_representatives,
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


def test_refutations_are_objects_known_on_the_laws_the_graph_decides(etp):
    laws, graph = EtpLaws.load(etp[0]), ImplicationGraph.load(etp[1])
    trivial, idempotent, left_zero, right_zero = (
        Equation.parse(text) for text in ("x = x", "x = x * x", "x = x * y", "x = y * x")
    )
    objects = {o.object: o for o in graph_refutations([trivial, idempotent, left_zero, right_zero], graph, laws)}
    assert set(objects) == {EtpRefutation(a, b) for a, b in [(1, 3), (1, 4), (1, 5), (3, 4), (3, 5), (4, 5), (5, 4)]}
    refutation = objects[EtpRefutation(4, 5)]
    assert (refutation.positive, refutation.negative) == ({trivial, idempotent, left_zero}, {right_zero})
    assert objects[EtpRefutation(1, 3)].negative == {idempotent, left_zero, right_zero}


def test_an_exploration_takes_the_refutations_of_the_graph_as_objects(etp, tmp_path):
    equations = tmp_path / "laws.json"
    main([str(etp[0]), "3", "4", "-o", str(equations)])
    _, base = run_magma_exploration(
        equations, report_interval=0, max_search_size=1,
        etp_graph=etp[1], etp_equations=etp[0], etp_refutations=True, results_dir=tmp_path / "results",
    )
    # x = x * y and x = y * x refute each other in the graph, and no magma of
    # size 1 accounts for either refutation.
    seeded = {v.original for v in base.context.objects if isinstance(v.original, EtpRefutation)}
    assert seeded == {EtpRefutation(4, 5), EtpRefutation(5, 4)}
    saved = json.loads((tmp_path / "results" / "etp_refutations.json").read_text(encoding="utf-8"))
    assert {tuple(r["refutes"]) for r in saved} == {(4, 5), (5, 4)}


# Laws with two classes of equivalent laws: x = x * y and its dual x = y * x,
# a class without a self-dual law, and x = x * x and x * y = y * x, both
# self-dual; x = x * (x * y) and its dual x = (y * x) * x are classes of
# their own.
CLASS_LAWS = [
    "x = x", "x = y", "x = x ◇ y", "x = y ◇ x", "x = x ◇ x",
    "x ◇ y = y ◇ x", "x = x ◇ (x ◇ y)", "x = (y ◇ x) ◇ x",
]
EQUIVALENT = [{3, 4}, {5, 6}]


def class_graph():
    def implies(a, b):
        return a == b or b == 1 or a == 2 or any({a, b} <= c for c in EQUIVALENT)
    n = len(CLASS_LAWS)
    return ImplicationGraph(bytes(7 if implies(a, b) else 6 for a in range(1, n + 1) for b in range(1, n + 1)), n)


def test_laws_that_imply_each_other_form_a_class():
    assert class_graph().equivalence_classes(range(1, 9)) == [[1], [2], [3, 4], [5, 6], [7], [8]]


def test_representatives_are_closed_under_duality():
    laws = EtpLaws([Equation.parse(law.replace("◇", "*"), id=k) for k, law in enumerate(CLASS_LAWS, start=1)])
    classes = class_graph().equivalence_classes(range(1, 9))
    assert representatives(laws, classes) == {
        1: [1], 2: [2], 3: [3, 4], 4: [3, 4], 5: [5, 6], 7: [7], 8: [8],
    }


def test_the_command_writes_representatives_with_their_classes(tmp_path):
    equations = tmp_path / "equations.txt"
    equations.write_text("\n".join(CLASS_LAWS) + "\n", encoding="utf-8")
    graph = tmp_path / "graph.json"
    graph.write_text(json.dumps({"rle_encoded_array": rle(class_graph().outcomes)}))
    output = tmp_path / "laws.json"
    main([str(equations), "--max-order", "1", "--graph", str(graph), "-o", str(output)])
    entries = json.loads(output.read_text(encoding="utf-8"))
    assert [(e["id"], e["class"]) for e in entries] == [(1, [1]), (2, [2]), (3, [3, 4]), (4, [3, 4]), (5, [5])]
    # x * y = y * x has two operations and is left out of the class of x = x * x.
    assert order(ETP.load_equations(output)[2]) == 1


def test_semigroup_representatives_are_closed_under_reversing_words():
    # Words: x = xxy reverses to x = yxx, and x = xy to x = yx.
    texts = ["x = x", "x = x * (x * y)", "x = y * x", "x = x * y", "x = y * (x * x)"]
    laws = EtpLaws([Equation.parse(text, id=k) for k, text in enumerate(texts, start=1)])
    classes = [[1], [2, 3], [4, 5]]
    assert semigroup_representatives(laws, classes) == {
        1: [1], 2: [2, 3], 3: [2, 3], 4: [4, 5], 5: [4, 5],
    }
