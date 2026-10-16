"""Lean proofs of the rules an exploration of ETP laws found.

Each rule of the reduced basis in an exploration's log is proved by Vampire,
and its proof is translated into Lean as the ETP translated the proofs of its
single-premise implications (equational_theories/Generated/VampireProven in
https://github.com/teorth/equational_theories): every clause of the proof
becomes a `have` justified by the ETP's `superpose` or `subsumption` tactics,
which redo the inference in Lean. The laws are defined as in the ETP, so that
the theorems state the same implications as the ETP's would.

usage: lean_proofs.py EQUATIONS_TXT LOG -o LEAN_DIR [--module NAME] [--prover9]

The Lean project in LEAN_DIR must contain NAME/Superposition.lean, the ETP's
tactics; NAME/Basic.lean (the laws) and NAME/Proofs.lean are written.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.etp import EtpLaws
from explorations.equational_theories.magma import Equation, Term, Var


@dataclass(frozen=True)
class Rule:
    """A rule of a reduced basis, by the ETP numbers of its laws."""

    number: int
    premise: tuple[int, ...]
    conclusion: tuple[int, ...]

    @property
    def name(self) -> str:
        premise = "_".join(map(str, self.premise))
        return f"Equation{premise}_implies_Equation{'_'.join(map(str, self.conclusion))}"


def rules_from_log(text: str) -> list[Rule]:
    """The rules of the reduced basis printed in an exploration's log."""
    basis = text[text.index("Discovered Implication Basis"):]
    rules = []
    for line in basis.splitlines()[1:]:
        match = re.match(r"  \[(\d+)\] (.*) -> (.*)$", line)
        if match is None:
            break
        premise, conclusion = (tuple(int(n) for n in re.findall(r"Eq(\d+):", side)) for side in match.groups()[1:])
        rules.append(Rule(int(match.group(1)), premise, conclusion))
    return rules


def _variables(term: Term, seen: list[str]) -> list[str]:
    if isinstance(term, Var):
        if term.name not in seen:
            seen.append(term.name)
    else:
        _variables(term.left, seen)
        _variables(term.right, seen)
    return seen


def _ordered_variables(equation: Equation) -> list[str]:
    return _variables(equation.rhs, _variables(equation.lhs, []))


def _lean_term(term: Term) -> str:
    return term.name if isinstance(term, Var) else f"({_lean_term(term.left)} ◇ {_lean_term(term.right)})"


def lean_definition(laws: EtpLaws, number: int) -> str:
    """The ETP's definition of a law, its variables bound in the order of
    their first occurrence."""
    law = laws.law(number)
    variables = _ordered_variables(law)
    binder = f"∀ {' '.join(variables)} : G, " if variables else ""
    return (
        f"/-- Eq{number}: {law.lhs} = {law.rhs} -/\n"
        f"abbrev Equation{number} (G : Type _) [Magma G] := {binder}{_lean_term(law.lhs)} = {_lean_term(law.rhs)}\n"
    )


def _tptp_term(term: Term) -> str:
    return "X" + term.name.upper() if isinstance(term, Var) else f"mul({_tptp_term(term.left)},{_tptp_term(term.right)})"


def _tptp_law(law: Equation) -> str:
    variables = sorted(law.lhs.vars() | law.rhs.vars())
    binder = f"![{','.join('X' + v.upper() for v in variables)}]: " if variables else ""
    return f"{binder}{_tptp_term(law.lhs)} = {_tptp_term(law.rhs)}"


def tptp_problem(laws: EtpLaws, rule: Rule) -> str:
    """The rule as a TPTP problem, the premise laws named h1, h2, ..."""
    lines = [f"fof(h{k}, axiom, {_tptp_law(laws.law(n))})." for k, n in enumerate(rule.premise, start=1)]
    goal = " & ".join(f"({_tptp_law(laws.law(n))})" for n in rule.conclusion)
    lines.append(f"fof(goal, conjecture, {goal}).")
    return "\n".join(lines) + "\n"


def vampire_proof(laws: EtpLaws, rule: Rule, vampire: str = "vampire", time_limit: int = 60) -> str:
    """Vampire's proof of the rule, with every inference spelt out."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
        file.write(tptp_problem(laws, rule))
        path = Path(file.name)
    try:
        output = subprocess.run(
            [vampire, "--proof_extra", "full", "-t", str(time_limit), str(path)],
            capture_output=True, text=True,
        ).stdout
    finally:
        path.unlink(missing_ok=True)
    if "SZS status Theorem" not in output:
        raise RuntimeError(f"Vampire did not prove rule {rule.number}")
    return output


def _lean_clause(statement: str) -> str:
    match = re.match(r"!\[([^\]]*)\]: (.*)", statement)
    variables, body = ([], statement) if match is None else (
        [v.split(":")[0].strip() for v in match.group(1).split(",")], match.group(2)
    )
    # mul(a,b) becomes (a ◇ b).
    body = body.replace("mul", "").replace(",", " ◇ ").replace("!=", "≠")
    return (f"({' '.join(variables)} : G) " if variables else "") + f": {body}"


_PREPROCESSING = re.compile(r"(negated conjecture|ennf transformation|skolemize|flattening|rectify) (\d+)$")


def lean_theorem(laws: EtpLaws, rule: Rule, proof: str) -> str:
    """The Lean theorem of a rule with one law in its conclusion, its proof
    the translation of Vampire's."""
    if len(rule.conclusion) != 1:
        raise ValueError(f"Rule {rule.number} has several laws in its conclusion")
    goal = rule.conclusion[0]
    hypotheses = " ".join(f"(h{k} : Equation{n} G)" for k, n in enumerate(rule.premise, start=1))
    skolem = ", ".join(f"sK{i}" for i in range(len(_ordered_variables(laws.law(goal)))))
    lines = [
        f"theorem {rule.name} (G : Type _) [Magma G] {hypotheses} : Equation{goal} G := by",
        "  apply Classical.byContradiction",
        "  intro nh",
        "  simp only [Classical.not_forall] at nh",
        f"  obtain ⟨{skolem}, nh⟩ := nh",
    ]
    origin: dict[str, str] = {}  # the input each preprocessed formula comes from
    steps = proof[proof.index("SZS output start"):proof.index("SZS output end")]
    for number, statement, justification in re.findall(
            r"^(\d+)\. (.+?) \[([^\]]+)\](?: \{[^}]*\})?$", steps, re.M):
        if match := re.match(r"input\(axiom\) (h\d+)", justification):
            origin[number] = match.group(1)
        elif justification.startswith("input(conjecture)"):
            origin[number] = "nh"
        elif match := _PREPROCESSING.match(justification):
            origin[number] = origin[match.group(2)]
        elif match := re.match(r"cnf transformation (\d+)$", justification):
            source = origin[match.group(1)]
            argument = "nh" if source == "nh" else f"({source} ..)"
            lines.append(f"  have eq{number} {_lean_clause(statement)} := mod_symm {argument}")
        elif statement == "$false":
            if match := re.match(r"(?:forward |backward )?subsumption resolution (\d+),(\d+)", justification):
                lines.append(f"  subsumption eq{match.group(1)} eq{match.group(2)}")
            elif match := re.match(r"(?:trivial inequality removal|equality resolution) (\d+)", justification):
                lines.append(f"  subsumption eq{match.group(1)} rfl")
            else:
                raise NotImplementedError(justification)
        elif match := re.match(r"(superposition|forward demodulation|backward demodulation) (\d+),(\d+)", justification):
            inference = f"{match.group(1)} {match.group(2)},{match.group(3)}"
            lines.append(
                f"  have eq{number} {_lean_clause(statement)} := "
                f"superpose eq{match.group(3)} eq{match.group(2)} -- {inference}"
            )
        else:
            raise NotImplementedError(justification)
    return "\n".join(lines) + "\n"


def _ladr_term(term: Term) -> str:
    return "x" + term.name if isinstance(term, Var) else f"({_ladr_term(term.left)} * {_ladr_term(term.right)})"


def prover9_proves(laws: EtpLaws, rule: Rule, prover9: str = "prover9", time_limit: int = 60) -> bool:
    """Whether Prover9 proves the rule, as an independent check."""
    def law(n: int) -> str:
        return f"{_ladr_term(laws.law(n).lhs)} = {_ladr_term(laws.law(n).rhs)}."
    problem = (
        f"assign(max_seconds, {time_limit}).\nformulas(assumptions).\n"
        + "".join(law(n) + "\n" for n in rule.premise)
        + "end_of_list.\nformulas(goals).\n" + "\n".join(law(n) for n in rule.conclusion) + "\nend_of_list.\n"
    )
    output = subprocess.run([prover9], input=problem, capture_output=True, text=True).stdout
    return "THEOREM PROVED" in output


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Write Lean proofs of the rules of an exploration of ETP laws.")
    parser.add_argument("etp_equations", type=Path, metavar="EQUATIONS_TXT", help="the ETP's equations.txt")
    parser.add_argument("log", type=Path, metavar="LOG", help="the exploration.log of the exploration")
    parser.add_argument("-o", "--output", type=Path, required=True, metavar="LEAN_DIR",
                        help="the Lean project to write the proofs into")
    parser.add_argument("--module", default="Order2", metavar="NAME",
                        help="the directory of the Lean files in the project (default: Order2)")
    parser.add_argument("--prover9", action="store_true", help="also check every rule with Prover9")
    args = parser.parse_args(argv)
    laws = EtpLaws.load(args.etp_equations)
    rules = rules_from_log(args.log.read_text(encoding="utf-8"))
    module = args.output / args.module
    numbers = sorted({n for rule in rules for n in rule.premise + rule.conclusion})
    (module / "Basic.lean").write_text(
        f"import {args.module}.Superposition\n\n"
        "/-! Magmas and the ETP laws of the rules, defined as in the ETP. -/\n\n"
        "class Magma (α : Type _) where\n  op : α → α → α\n\n"
        "infix:65 \" ◇ \" => Magma.op\n\n" + "\n".join(lean_definition(laws, n) for n in numbers),
        encoding="utf-8",
    )
    theorems = []
    for rule in rules:
        theorems.append(f"/-- Rule {rule.number} of the reduced basis. -/\n"
                        + lean_theorem(laws, rule, vampire_proof(laws, rule)))
        if args.prover9 and not prover9_proves(laws, rule):
            print(f"Prover9 did not prove rule {rule.number}", file=sys.stderr)
    (module / "Proofs.lean").write_text(
        f"import {args.module}.Basic\n\n"
        f"/-! The rules of the reduced basis in {args.log.parent.name}/{args.log.name}, from Vampire's proofs. -/\n\n"
        + "\n".join(theorems),
        encoding="utf-8",
    )
    print(f"Wrote {len(rules)} theorems to {module / 'Proofs.lean'}")


if __name__ == "__main__":
    main()
