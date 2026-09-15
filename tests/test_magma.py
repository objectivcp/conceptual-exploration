"""Unit tests for the Magma and Equational Theories Project (ETP) exploration domain."""

from conceptual_exploration import AttributeExploration, Implication
from conceptual_exploration.exploration.base import ExplorationBase
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert, Op, Term, Var


def test_term_parsing_and_eval():
    t1 = Term.parse("x")
    assert isinstance(t1, Var)
    assert t1.name == "x"
    assert t1.vars() == {"x"}

    t2 = Term.parse("x * y")
    assert isinstance(t2, Op)
    assert t2.left == Var("x")
    assert t2.right == Var("y")
    assert t2.vars() == {"x", "y"}

    t3 = Term.parse("((x * y) * z)")
    assert isinstance(t3, Op)
    assert t3.vars() == {"x", "y", "z"}
    assert t3.size() == 5
    assert t3.op_count() == 2

    # Evaluation on a simple 2-element magma (Z2 addition: 0+1=1, 1+1=0)
    z2 = Magma.cyclic_addition(2)
    env = {"x": 1, "y": 1, "z": 0}
    # ((1 + 1) + 0) = 0 + 0 = 0
    assert t3.eval(env, z2.table) == 0


def test_term_duality():
    t = Term.parse("(x * y) * z")
    dual_t = t.dual()
    assert str(dual_t) == "(z * (y * x))"


def test_equation_parsing_and_holds():
    comm = Equation.parse("x * y = y * x", name="Commutativity")
    assoc = Equation.parse("(x * y) * z = x * (y * z)", name="Associativity")
    idem = Equation.parse("x * x = x", name="Idempotence")

    # Trivial magma satisfies all equations
    trivial = Magma.trivial()
    assert comm.holds_in_magma(trivial)
    assert assoc.holds_in_magma(trivial)
    assert idem.holds_in_magma(trivial)

    # Z_2(+) is commutative and associative, but not idempotent (1+1=0 != 1)
    z2_add = Magma.cyclic_addition(2)
    assert comm.holds_in_magma(z2_add)
    assert assoc.holds_in_magma(z2_add)
    assert not idem.holds_in_magma(z2_add)

    # Z_2(-) is not associative: (0-1)-1 = 1-1 = 0, but 0-(1-1) = 0-0 = 0... wait in Z2 + and - are the same!
    # Let's test Z_3(-): (0 - 1) - 1 = 2 - 1 = 1 mod 3. 0 - (1 - 1) = 0 - 0 = 0 != 1
    z3_sub = Magma.cyclic_subtraction(3)
    assert not assoc.holds_in_magma(z3_sub)
    assert not comm.holds_in_magma(z3_sub)

    # Left projection (x * y = x) is associative, idempotent, but not commutative for n >= 2
    left_proj = Magma.left_projection(2)
    assert assoc.holds_in_magma(left_proj)
    assert idem.holds_in_magma(left_proj)
    assert not comm.holds_in_magma(left_proj)


def test_magma_duality():
    # Left projection opposite is right projection
    lp = Magma.left_projection(3)
    rp = lp.dual()
    assert rp.table == Magma.right_projection(3).table

    left_abs = Equation.parse("x * y = x", name="Left-Absorption")
    right_abs = Equation.parse("y * x = x", name="Right-Absorption")

    assert lp.holds(left_abs)
    assert not lp.holds(right_abs)
    assert rp.holds(right_abs)
    assert not rp.holds(left_abs)


def test_magma_expert_counterexample():
    comm = Equation.parse("x * y = y * x", name="Commutativity")
    assoc = Equation.parse("(x * y) * z = x * (y * z)", name="Associativity")

    expert = MagmaExpert([comm, assoc], max_search_size=3)
    # Question: Does Commutativity imply Associativity?
    impl = Implication(frozenset([comm]), frozenset([assoc]))
    counterexample = expert.validate(impl)
    assert counterexample is not None
    assert comm in counterexample.positive
    assert assoc in counterexample.negative


def test_magma_expert_timeout_is_inconclusive():
    import z3

    comm = Equation.parse("x * y = y * x", name="Commutativity")
    assoc = Equation.parse("(x * y) * z = x * (y * z)", name="Associativity")
    impl = Implication(frozenset([comm]), frozenset([assoc]))

    # A solver that never decides: no counterexample, but nothing is ruled out either.
    expert = MagmaExpert([comm, assoc], max_search_size=3, initial_magmas=[])
    expert._find_table_z3 = lambda size, premises, conclusions: (z3.unknown, None)
    assert expert.validate(impl) is None
    assert not expert.is_conclusive()

    # The verdict is per call, so a later decided run clears the earlier timeout.
    expert._find_table_z3 = lambda size, premises, conclusions: (z3.unsat, None)
    assert expert.validate(impl) is None
    assert expert.is_conclusive()

    # A counterexample at a later size is definitive, so a timeout at an
    # earlier size must not leave the expert stuck reporting "undecided".
    expert = MagmaExpert([comm, assoc], max_search_size=3, initial_magmas=[])
    search = expert._find_table_z3
    expert._find_table_z3 = (
        lambda size, premises, conclusions:
        (z3.unknown, None) if size == 1 else search(size, premises, conclusions)
    )
    counterexample = expert.validate(impl)
    assert counterexample is not None
    assert counterexample.refutes(impl)
    assert expert.is_conclusive()


def test_counterexample_search_sorts_equations():
    """Equations must reach Z3 in a stable order, or runs stop being reproducible.

    Premises and conclusions normally arrive as frozensets, whose iteration order
    varies with PYTHONHASHSEED; Z3 can answer a reordered query with a different
    (equally valid) model, which sends the whole exploration down another path.
    """
    import z3

    seen = []
    expert = MagmaExpert(max_search_size=3, initial_magmas=[])

    def record(size, premises, conclusions):
        seen.append((list(premises), list(conclusions)))
        return z3.unsat, None

    expert._find_table_z3 = record
    expert._search_counterexample(
        frozenset([ETP.get_equation(43), ETP.get_equation(381), ETP.get_equation(3)]),
        frozenset([ETP.get_equation(4512), ETP.get_equation(9)]),
        3,
    )

    assert seen, "expected the search to consult the solver"
    for premises, conclusions in seen:
        assert premises == sorted(premises)
        assert conclusions == sorted(conclusions)


def test_inconclusive_expert_accepts_as_unconfirmed():
    from conceptual_exploration.experts.base import Expert
    from conceptual_exploration.exploration.base import ImplicationSource

    eq_idem = Equation.parse("x = x * x", name="Idempotence", id=3)
    eq_left_zero = Equation.parse("x = x * y", name="Left-Zero", id=4)
    attributes = [eq_left_zero, eq_idem]

    class UndecidedExpert(Expert[Magma, Equation]):
        """Never refutes anything, and never manages to decide either."""

        def validate(self, implication, attributes=None):
            return None

        def is_conclusive(self) -> bool:
            return False

    base = ExplorationBase[Magma, Equation](attributes=attributes)
    AttributeExploration(base, UndecidedExpert()).run()

    assert base.unconfirmed_implications
    for impl in base.unconfirmed_implications:
        assert base.implication_sources[impl] is ImplicationSource.UNCONFIRMED
        # Unconfirmed implications are still accepted, not silently dropped.
        assert impl in base.accepted_implications

    # The default expert behaviour is unchanged: conclusive means confirmed.
    base = ExplorationBase[Magma, Equation](attributes=attributes)
    AttributeExploration(base, MagmaExpert(attributes=attributes, max_search_size=3)).run()
    assert not base.unconfirmed_implications
    assert base.accepted_implications


def test_etp_catalog():
    famous = ETP.get_famous_equations()
    assert len(famous) >= 15
    eq_comm = ETP.get_equation(43)
    assert "Commutativity" in (eq_comm.name or "")
    eq_assoc = ETP.get_equation(381)
    assert "Associativity" in (eq_assoc.name or "")


def test_magma_attribute_exploration():
    # Explore a set of ETP equations
    eq_singleton = Equation.parse("x = y", name="Singleton", id=2)
    eq_idem = Equation.parse("x = x * x", name="Idempotence", id=3)
    eq_left_zero = Equation.parse("x = x * y", name="Left-Zero", id=4)
    eq_right_zero = Equation.parse("x = y * x", name="Right-Zero", id=5)
    eq_comm = Equation.parse("x * y = y * x", name="Commutativity", id=43)

    attributes = [eq_singleton, eq_idem, eq_left_zero, eq_right_zero, eq_comm]
    duality_map = ETP.get_duality_mapping(attributes)

    base = ExplorationBase[Magma, Equation](
        attributes=attributes,
        mappings=[duality_map],
    )
    expert = MagmaExpert(attributes=attributes, max_search_size=3)
    exploration = AttributeExploration(base, expert, evaluate_all=True)

    state = exploration.run()
    assert state.questions_asked > 0
    assert len(base.accepted_implications) > 0

    # Singleton (x = y) should imply all other equations
    singleton_impls = [
        impl for impl in base.accepted_implications
        if eq_singleton in impl.premise
    ]
    assert len(singleton_impls) > 0

    # Left-Zero (x = x * y) implies Idempotence (x = x * x)
    assert base.implications.entails(
        Implication(frozenset([eq_left_zero]), frozenset([eq_idem]))
    )
    # Right-Zero (x = y * x) implies Idempotence (x = x * x)
    assert base.implications.entails(
        Implication(frozenset([eq_right_zero]), frozenset([eq_idem]))
    )


if __name__ == "__main__":
    test_term_parsing_and_eval()
    test_term_duality()
    test_equation_parsing_and_holds()
    test_magma_duality()
    test_magma_expert_counterexample()
    test_magma_expert_timeout_is_inconclusive()
    test_counterexample_search_sorts_equations()
    test_inconclusive_expert_accepts_as_unconfirmed()
    test_etp_catalog()
    test_magma_attribute_exploration()
    print("All Magma ETP tests passed successfully!")
