"""Unit tests for the translation of Vampire's proofs into Lean."""

from explorations.equational_theories.etp import EtpLaws
from explorations.equational_theories.lean_proofs import (
    Rule,
    lean_definition,
    lean_theorem,
    rules_from_log,
    tptp_problem,
)
from explorations.equational_theories.magma import Equation

LAWS = EtpLaws([Equation.parse(law, id=k) for k, law in enumerate(
    ["x = x", "x = y", "x = (x * y) * x", "x * y = y * x"], start=1)])
RULE = Rule(1, (3, 4), (2,))

# Vampire's proof of the rule, as printed with --proof_extra full (abridged).
PROOF = """% SZS output start Proof for t
1. ! [X0,X1] : X0 = mul(mul(X0,X1),X0) [input(axiom) h1 "t.p"]
2. ! [X0,X1] : mul(X0,X1) = mul(X1,X0) [input(axiom) h2 "t.p"]
3. ! [X0,X1] : X0 = X1 [input(conjecture) goal "t.p"]
4. ~ ! [X0,X1] : X0 = X1 [negated conjecture 3]
5. ? [X0,X1] : X0 != X1 [ennf transformation 4]
6. sK0 != sK1 [skolemize 5]
7. ![X0:$i, X1:$i]: mul(mul(X0,X1),X0) = X0 [cnf transformation 1] {a:0,w:7}
8. ![X0:$i, X1:$i]: mul(X0,X1) = mul(X1,X0) [cnf transformation 2] {a:0,w:7}
9. sK0 != sK1 [cnf transformation 6] {a:0,w:3,goal:1}
10. ![X0:$i, X1:$i]: mul(X0,mul(X0,X1)) = X0 [forward demodulation 7,8,lhs=mul(X0,X1),target=mul(mul(X0,X1),X0)] {a:0,w:7}
38. ![X0:$i, X1:$i]: X0 = X1 [superposition 10,10,selected=(X0),other=(X0)] {a:3,w:3}
63. $false [forward subsumption resolution 9,38,selected=(sK0 != X0)] {a:4,w:0,goal:1}
% SZS output end Proof for t
"""


def test_rules_are_read_from_the_log():
    log = (
        "Discovered Implication Basis (Reduced, 2 rules):\n"
        "  [1] Eq25: x = ((x * y) * x), Eq43: (x * y) = (y * x) -> Eq2: x = y\n"
        "  [2] Eq8: x = (x * (x * x)), Eq25: x = ((x * y) * x) -> Eq3: x = (x * x)\n"
        "\nOpen Questions:\n"
    )
    assert rules_from_log(log) == [Rule(1, (25, 43), (2,)), Rule(2, (8, 25), (3,))]


def test_laws_are_defined_as_in_the_etp():
    assert lean_definition(LAWS, 3) == (
        "/-- Eq3: x = ((x * y) * x) -/\n"
        "abbrev Equation3 (G : Type _) [Magma G] := ∀ x y : G, x = ((x ◇ y) ◇ x)\n"
    )


def test_the_premise_laws_are_named_for_vampire():
    assert tptp_problem(LAWS, RULE) == (
        "fof(h1, axiom, ![XX,XY]: XX = mul(mul(XX,XY),XX)).\n"
        "fof(h2, axiom, ![XX,XY]: mul(XX,XY) = mul(XY,XX)).\n"
        "fof(goal, conjecture, (![XX,XY]: XX = XY)).\n"
    )


def test_each_clause_becomes_a_step_from_its_hypothesis():
    theorem = lean_theorem(LAWS, RULE, PROOF)
    assert theorem.startswith(
        "theorem Equation3_4_implies_Equation2 (G : Type _) [Magma G] "
        "(h1 : Equation3 G) (h2 : Equation4 G) : Equation2 G := by\n"
    )
    assert "  obtain ⟨sK0, sK1, nh⟩ := nh\n" in theorem
    assert "  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)\n" in theorem
    assert "  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h2 ..)\n" in theorem
    assert "  have eq9 : sK0 ≠ sK1 := mod_symm nh\n" in theorem
    assert "  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8\n" in theorem
    assert theorem.endswith("  subsumption eq9 eq38\n")
