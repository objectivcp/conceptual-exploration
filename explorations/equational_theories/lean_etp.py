"""The result of an exploration of semigroup laws as Lean files in the ETP's form.

The files import the Equational Theories Project's library
(https://github.com/teorth/equational_theories), so that their theorems are
about its definitions, and state the result as the ETP states its own:

- Laws are the ETP's `Equation{N}`, numbered by the ETP's scheme
  (scripts/find_equation_id.py), which extends past the ETP's 4694 laws of
  order at most 4; those past it are declared with the ETP's `equation N :=`
  command, in the ETP's canonical form.
- Each certificate (certificates.py) is a theorem
  `Equation3_56_4512_implies_Equation4 (G : Type*) [Magma G] (h3 :
  Equation3 G) ... : Equation4 G`, with the premise laws its proof uses; one
  with a single hypothesis is an `@[equational_result]`. A step of a chain
  rewrites one subterm with an instance of a hypothesis or a lemma, and
  becomes a `conv` that goes to that subterm and rewrites it with the
  instance, written out. The class equivalences are two such implications.
- Each semigroup of the context is a `finOpTable`, and an
  `@[equational_result]` theorem `∃ (G : Type) (_ : Magma G) (_ : Finite G),
  Facts G [satisfied] [refuted]`, as in the ETP's Generated/All4x4Tables:
  the refuted laws are all those of the exploration it refutes, and the
  satisfied ones, as in the ETP, a few from which the others of its row
  follow by the implications proved, chosen to be cheap to decide. A
  satisfied law is decided by `decideFin!`, and a refuted one by
  `decideFin!` at a counterexample.

usage: lean_etp.py RESULTS_DIR CERTIFICATES --etp ETP_DIR -o LEAN_DIR [--module NAME] [--classes]

ETP_DIR is a checkout of the ETP, such as the one lake puts in
LEAN_DIR/.lake/packages/equational_theories; NAME/*.lean and NAME.lean are
written in LEAN_DIR.
"""

from __future__ import annotations

import argparse
import functools
import importlib.util
import itertools
import json
import lzma
import math
import re
import sys
import tomllib
import types
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.certificates import (
    _difference, _match, _subterm, parse_law, parse_term, show, word_law,
)
from explorations.equational_theories.verify import law_key, read_context


class TranslationError(ValueError):
    pass


# The ETP's numbering.

@functools.cache
def _bell(n: int) -> int:
    row = [1]
    for _ in range(n):
        new = [row[-1]]
        for value in row:
            new.append(new[-1] + value)
        row = new
    return row[0]


def etp_numbering(etp: Path):
    """The ETP's find_equation_id.py, unchanged, with the three integer
    functions it imports from sympy supplied here."""
    numbers = types.ModuleType("sympy.functions.combinatorial.numbers")
    numbers.bell, numbers.binomial = _bell, math.comb
    numbers.catalan = lambda n: math.comb(2 * n, n) // (n + 1)
    for name in ("sympy", "sympy.functions", "sympy.functions.combinatorial"):
        sys.modules.setdefault(name, types.ModuleType(name))
    sys.modules["sympy.functions.combinatorial.numbers"] = numbers
    spec = importlib.util.spec_from_file_location("find_equation_id", etp / "scripts" / "find_equation_id.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class EtpLaws:
    """Laws by their ETP numbers, and the ETP's form of each number: its
    declaration if the ETP declares it, among its 4694 laws or a few
    others, and otherwise the canonical form of its numbering."""

    def __init__(self, etp: Path):
        self.ids = etp_numbering(etp)
        self.used: set[int] = set()
        self.declared: dict[int, str] = {}
        for path in sorted((etp / "equational_theories" / "Equations").glob("*.lean")):
            for line in path.read_text(encoding="utf-8").splitlines():
                match = re.match(r"\s*equation (\d+)\s*:=\s*(.*?)\s*$", line)
                if match:
                    self.declared[int(match.group(1))] = match.group(2)

    def number(self, law: tuple) -> int:
        number = self.ids.Equation.from_str(f"{show(law[0])} = {show(law[1])}").id
        self.used.add(number)
        return number

    def text(self, number: int) -> str:
        """The ETP's form, as in its `equation` declarations."""
        return self.declared.get(number) or str(self.ids.Equation.from_id(number))

    def definition(self, number: int) -> tuple:
        return parse_law(self.text(number).replace("◇", "*"))


# Terms and chains.

def _variables(term, seen: list[str]) -> list[str]:
    if isinstance(term, str):
        if term not in seen:
            seen.append(term)
    else:
        _variables(term[0], seen)
        _variables(term[1], seen)
    return seen


def law_variables(law: tuple) -> list[str]:
    """The variables of a law in order of first occurrence, as the ETP's
    `equation` command quantifies them."""
    return _variables(law[1], _variables(law[0], []))


def lean_term(term) -> str:
    return term if isinstance(term, str) else f"({lean_term(term[0])} ◇ {lean_term(term[1])})"


def lean_law(law: tuple) -> str:
    return f"∀ {' '.join(law_variables(law))} : G, {lean_term(law[0])} = {lean_term(law[1])}"


def _rename(term, mapping: dict):
    return mapping.get(term, term) if isinstance(term, str) else (_rename(term[0], mapping), _rename(term[1], mapping))


def _step(s, t, law: tuple):
    """How t follows from s by the law: the path to the subterm rewritten,
    whether the law is used from right to left, and the substitution."""
    path = _difference(s, t)
    for depth in range(len(path), -1, -1):
        u, v = _subterm(s, path[:depth]), _subterm(t, path[:depth])
        for backwards, (lhs, rhs) in ((False, law), (True, law[::-1])):
            substitution: dict = {}
            if _match(lhs, u, substitution) and _match(rhs, v, substitution):
                return path[:depth], backwards, substitution
    raise TranslationError(f"{show(t)} does not follow from {show(s)}")


def _shortened(terms: list, by: list[str]) -> tuple[list, list[str]]:
    """The chain without its detours: from each term on, to its last
    occurrence."""
    kept_terms, kept_by = [], []
    k = 0
    while True:
        last = max(i for i, term in enumerate(terms) if term == terms[k])
        kept_terms.append(terms[last])
        if last == len(terms) - 1:
            return kept_terms, kept_by
        kept_by.append(by[last])
        k = last + 1


def _to_definition(law: tuple, defined: tuple) -> tuple[dict, bool]:
    """A renaming of the variables of `law` that makes it `defined`, and
    whether its sides must be swapped."""
    for swapped, target in ((False, defined), (True, defined[::-1])):
        substitution: dict = {}
        if _match(law[0], target[0], substitution) and _match(law[1], target[1], substitution):
            values = list(substitution.values())
            if all(isinstance(v, str) for v in values) and len(set(values)) == len(values):
                return substitution, swapped
    raise TranslationError("The law is not its definition up to renaming")


# Implications.

def implication_theorem(certificate: dict, laws: EtpLaws) -> tuple[str, str]:
    """The name and the text of the theorem of a certificate: the premise
    laws its proof uses imply its conclusion."""
    premise = [laws.number(parse_law(p)) for p in certificate["premise"]]
    conclusion = laws.number(parse_law(certificate["conclusion"]))
    cites = certificate["by"] + [c for lemma in certificate.get("lemmas", []) for c in lemma["by"]]
    used = sorted({premise[int(c[1:])] for c in cites if c[0] == "h"})
    hypothesis = {f"h{k}": f"h{number}" for k, number in enumerate(premise)}
    definitions = {number: laws.definition(number) for number in set(premise)}
    lemmas: list[tuple] = []
    lines: list[str] = []

    def chain(terms: list, by: list[str], indent: str) -> None:
        terms, by = _shortened(terms, by)
        for cite, s, t in zip(by, terms, terms[1:]):
            if cite[0] == "h":
                law, name = definitions[premise[int(cite[1:])]], hypothesis[cite]
            else:
                law, name = lemmas[int(cite[1:])], cite
            path, backwards, substitution = _step(s, t, law)
            arguments = "".join(f" {lean_term(substitution[v])}" for v in law_variables(law))
            # The left side of the goal is its first argument.
            lines.append(f"{indent}conv => enter [{', '.join(str(i + 1) for i in [0, *path])}]; "
                         f"rw [{'← ' if backwards else ''}{name}{arguments}]")
        # conv closes the goal when its sides become the same.
        if len(terms) == 1:
            lines.append(f"{indent}rfl")

    for lemma in certificate.get("lemmas", []):
        terms = [parse_term(t) for t in lemma["terms"]]
        ends = (terms[0], terms[-1])
        variables = law_variables(ends)
        # Variables only inside the chain can be anything: the first one.
        inner = {v: variables[0] for t in terms for v in _variables(t, []) if v not in variables}
        lines.append(f"  have l{len(lemmas)} : {lean_law(ends)} := by")
        lines.append(f"    intro {' '.join(variables)}")
        lemmas.append(ends)
        chain([_rename(t, inner) for t in terms], lemma["by"], "    ")
    defined = laws.definition(conclusion)
    renaming, swapped = _to_definition(parse_law(certificate["conclusion"]), defined)
    variables = law_variables(defined)
    terms = [parse_term(t) for t in certificate["terms"]]
    inner = {v: variables[0] for t in terms for v in _variables(t, []) if v not in renaming}
    terms = [_rename(t, {**inner, **renaming}) for t in terms]
    by = list(certificate["by"])
    if swapped:
        terms, by = terms[::-1], by[::-1]
    lines.append(f"  intro {' '.join(variables)}")
    chain(terms, by, "  ")
    name = f"Equation{'_'.join(map(str, used))}_implies_Equation{conclusion}"
    hypotheses = "".join(f" (h{n} : Equation{n} G)" for n in used)
    attribute = "@[equational_result]\n" if len(used) == 1 else ""
    body = "\n".join(lines)
    return name, f"{attribute}theorem {name} (G : Type*) [Magma G]{hypotheses} : Equation{conclusion} G := by\n{body}\n"


# Semigroups.

def _variable_count(law: tuple) -> int:
    return len(law_variables(law))


@dataclass
class Semigroup:
    """A semigroup of the context: the laws listed as satisfied, each with
    the number of evaluations that deciding it by brute force takes, and
    the laws refuted."""

    name: str
    table: list[list[int]]
    satisfied: list[tuple[int, int]]
    refuted: list[int]


def facts(results: Path, attributes: dict[str, tuple], certificates: list[dict], laws: EtpLaws,
          assumed: list[str]) -> list[Semigroup]:
    """The semigroups of the context, each with the assumed laws and as few
    others as needed for the implications of the certificates to give the
    rest of its row, the cheapest first, as satisfied."""
    objects, names, rows = read_context(results / "context.cxt")
    index = {name: i for i, name in enumerate(names)}
    by_key = {law_key(attributes[name], False): name for name in names}
    rules = []
    for certificate in certificates:
        keys = [law_key(parse_law(p), False) for p in certificate["premise"]]
        target = law_key(parse_law(certificate["conclusion"]), False)
        if all(key in by_key for key in keys + [target]):
            rules.append((sum(1 << index[by_key[key]] for key in keys), 1 << index[by_key[target]]))
    trivial = sum(1 << index[name] for name in names if attributes[name][0] == attributes[name][1])

    def closure(mask: int) -> int:
        mask |= trivial
        changed = True
        while changed:
            changed = False
            for premise, conclusion in rules:
                if premise & ~mask == 0 and conclusion & ~mask:
                    mask |= conclusion
                    changed = True
        return mask

    tables = {m["name"]: m["table"] for m in json.loads((results / "magmas.json").read_text(encoding="utf-8"))}
    result = []
    for name, row in zip(objects, rows):
        table = tables[name]
        satisfied = [a for a, entry in zip(names, row) if entry == "X"]
        intent = sum(1 << index[a] for a in satisfied)
        cost = {a: len(table) ** _variable_count(attributes[a]) for a in satisfied}
        chosen = list(assumed)
        mask = closure(sum(1 << index[a] for a in chosen))
        for a in sorted(satisfied, key=cost.get):
            if not mask >> index[a] & 1:
                chosen.append(a)
                mask = closure(mask | 1 << index[a])
        if mask != intent:
            raise TranslationError(f"The implications do not give the row of {name}")
        for a in sorted(chosen[len(assumed):], key=cost.get, reverse=True):
            rest = [b for b in chosen if b != a]
            if closure(sum(1 << index[b] for b in rest)) == intent:
                chosen = rest
        refuted = [a for a, entry in zip(names, row) if entry == "."]
        result.append(Semigroup(name, table, sorted((laws.number(attributes[a]), cost[a]) for a in chosen),
                                sorted(laws.number(attributes[a]) for a in refuted)))
    return result


# Deciding a law with many evaluations at once makes the kernel slow out of
# proportion; such a law is decided in parts, each with some of its first
# variables fixed, of at most this many evaluations.
PART = 100_000


def _magma(source: str, semigroup: Semigroup) -> str:
    return f"«{source} {semigroup.name}»"


def table_definition(source: str, semigroup: Semigroup) -> str:
    rows = json.dumps(semigroup.table).replace(" ", "")
    return (f"@[implicit_reducible]\ndef {_magma(source, semigroup)} : Magma (Fin {len(semigroup.table)}) where\n"
            f"  op := finOpTable \"{rows}\"\n")


def _fixed(n: int, number: int, size: int) -> int:
    """How many of the first variables of a law of n variables to fix for
    parts of at most PART evaluations."""
    fixed = 0
    while fixed < n and size ** (n - fixed) > PART:
        fixed += 1
    return fixed


def parts(source: str, semigroup: Semigroup, number: int, laws: EtpLaws) -> list[tuple[str, str, int]]:
    """The parts of deciding a law in a semigroup: name, theorem and cost."""
    law = laws.definition(number)
    variables = law_variables(law)
    size = len(semigroup.table)
    fixed = _fixed(len(variables), number, size)
    result = []
    for values in itertools.product(range(size), repeat=fixed):
        literal = {v: f"({k} : Fin {size})" for v, k in zip(variables, values)}
        free = variables[fixed:]
        body = f"{lean_term(_rename(law[0], literal))} = {lean_term(_rename(law[1], literal))}"
        statement = f"∀ {' '.join(free)} : Fin {size}, {body}" if free else body
        name = f"«{source} {semigroup.name} satisfies {number} at {' '.join(map(str, values))}»"
        result.append((name, f"theorem {name} : {statement} := by decideFin!\n", size ** len(free)))
    return result


def assembled(source: str, semigroup: Semigroup, number: int, laws: EtpLaws) -> tuple[str, str]:
    """The theorem that the semigroup satisfies the law, from its parts, by
    cases on the values of the variables they fix."""
    size = len(semigroup.table)
    variables = law_variables(laws.definition(number))
    fixed = _fixed(len(variables), number, size)
    name = f"«{source} {semigroup.name} satisfies {number}»"

    def cases(prefix: tuple, indent: str) -> list[str]:
        if len(prefix) == fixed:
            part = f"«{source} {semigroup.name} satisfies {number} at {' '.join(map(str, prefix))}»"
            return [f"{indent}{part}"]
        lines = [f"{indent}fun x{len(prefix)} => match x{len(prefix)} with"]
        for k in range(size):
            inner = cases(prefix + (k,), indent + "    ")
            lines.append(f"{indent}  | ⟨{k}, _⟩ =>")
            lines += inner
        # Lean does not rule out the values past the last case for large sizes
        lines += [f"{indent}  | ⟨_ + {size}, h⟩ =>", f"{indent}    absurd h (by omega)"]
        return lines

    body = "\n".join(cases((), "  "))
    return name, f"theorem {name} : Equation{number} (Fin {size}) :=\n{body}\n"


def counterexample(table: list[list[int]], law: tuple) -> tuple[int, ...]:
    """Values of the law's variables at which the table violates it, with
    the least largest value."""
    variables = law_variables(law)

    def value(term, at: dict) -> int:
        return at[term] if isinstance(term, str) else table[value(term[0], at)][value(term[1], at)]

    for largest in range(len(table)):
        for values in itertools.product(range(largest + 1), repeat=len(variables)):
            if largest in values:
                at = dict(zip(variables, values))
                if value(law[0], at) != value(law[1], at):
                    return values
    raise ValueError("The table satisfies the law")


def facts_theorem(source: str, semigroup: Semigroup, laws: EtpLaws) -> str:
    """The ETP's statement of the semigroup's facts; the laws decided in
    parts come first. Searching for the first counterexample to a refuted
    law can take long, so each is given one."""
    size = len(semigroup.table)
    in_parts = [n for n, cost in semigroup.satisfied if cost > PART]
    satisfied = in_parts + [n for n, cost in semigroup.satisfied if cost <= PART]
    proofs = ([f"«{source} {semigroup.name} satisfies {n}»" for n in in_parts]
              + ["by decideFin!"] * (len(satisfied) - len(in_parts))
              + [f"fun h => absurd (h {' '.join(map(str, counterexample(semigroup.table, laws.definition(n))))}) "
                 "(by decideFin!)" for n in semigroup.refuted])
    return (f"/-! {semigroup.name} of {source}: {', '.join(map(str, sorted(satisfied)))} hold, "
            f"and the others of its row follow -/\n"
            # for the anonymous constructor of hundreds of proofs
            f"set_option maxRecDepth 10000 in\n"
            f"@[equational_result]\ntheorem «Facts from {source} {semigroup.name}» :\n"
            f"  ∃ (G : Type) (_ : Magma G) (_: Finite G), "
            f"Facts G [{', '.join(map(str, satisfied))}] [{', '.join(map(str, semigroup.refuted))}] :=\n"
            f"    ⟨Fin {size}, {_magma(source, semigroup)}, Finite.of_fintype _,\n"
            + ",\n".join(f"      {proof}" for proof in proofs) + "⟩\n")


def _packed(items: list[tuple[str, float]], budget: float) -> list[list[str]]:
    """Texts in files of at most `budget` cost each, a costlier text alone."""
    files: list[list[str]] = [[]]
    spent = 0.0
    for text, cost in items:
        if files[-1] and spent + cost > budget:
            files.append([])
            spent = 0.0
        files[-1].append(text)
        spent += cost
    return files


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="The result of an exploration as Lean files in the ETP's form.")
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR")
    parser.add_argument("certificates", type=Path, metavar="CERTIFICATES")
    parser.add_argument("--etp", type=Path, required=True, metavar="ETP_DIR", help="a checkout of the ETP")
    parser.add_argument("-o", "--output", type=Path, required=True, metavar="LEAN_DIR")
    parser.add_argument("--module", default="Order5")
    parser.add_argument("--classes", action="store_true",
                        help="also the laws of the classes, whose certificates certify.py --classes wrote")
    parser.add_argument("--root", type=Path, default=Path("."),
                        help="the directory the exploration was run from (default: the current one)")
    args = parser.parse_args(argv)
    settings = tomllib.loads((args.results / "settings.toml").read_text(encoding="utf-8"))
    equations = json.loads((args.root / settings["equations"]).read_text(encoding="utf-8"))
    attributes = {(f"Eq{e['id']}" if "id" in e else e["name"]): parse_law(e["equation"]) for e in equations}
    axiom_ids = {str(a) for a in settings.get("axiom", [])}
    assumed = [name for name in attributes if name.startswith("Eq") and name[2:] in axiom_ids]
    laws = EtpLaws(args.etp)
    opener = lzma.open if args.certificates.suffix == ".xz" else open
    with opener(args.certificates, "rt", encoding="utf-8") as file:
        certificates = [json.loads(line) for line in file if line.strip()]
    if args.classes:
        for entry in equations:
            for word in entry.get("class", []):
                laws.number(word_law(word))

    theorems: dict[str, tuple[str, int]] = {}
    for certificate in certificates:
        name, text = implication_theorem(certificate, laws)
        steps = len(certificate["by"]) + sum(len(lemma["by"]) for lemma in certificate.get("lemmas", []))
        theorems.setdefault(name, (text, steps))
    semigroups = facts(args.results, attributes, certificates, laws, assumed)

    directory = args.output / args.module
    directory.mkdir(parents=True, exist_ok=True)
    for old in directory.glob("*.lean"):
        old.unlink()
    declared = sorted(n for n in laws.used if n not in laws.declared)
    (directory / "Equations.lean").write_text(
        "import equational_theories.Equations.All\n\n"
        f"/-! The laws of {args.results.name} the ETP does not declare, numbered by its scheme -/\n\n"
        + "".join(f"equation {n} := {laws.text(n)}\n" for n in declared), encoding="utf-8")
    header = {
        "Implications": (f"import {args.module}.Equations\nimport equational_theories.EquationalResult\n"
                         "import Mathlib.Tactic.TypeStar\n\nset_option linter.unusedVariables false\n\n"),
        "Semigroups": (f"import Mathlib.Data.Finite.Prod\nimport {args.module}.Equations\n"
                       "import equational_theories.FactsSyntax\nimport equational_theories.MemoFinOp\n"
                       "import equational_theories.DecideBang\nimport equational_theories.EquationalResult\n\n"
                       "set_option linter.unusedVariables false\n\n"),
    }
    files = []
    source = args.results.name
    for k, texts in enumerate(_packed(list(theorems.values()), 2000)):
        (directory / f"Implications{k}.lean").write_text(header["Implications"] + "\n".join(texts), encoding="utf-8")
        files.append(f"Implications{k}")
    # The tables, the parts of the laws decided in parts, and the facts.
    (directory / "SemigroupTables.lean").write_text(
        header["Semigroups"] + "\n".join(table_definition(source, s) for s in semigroups), encoding="utf-8")
    files.append("SemigroupTables")
    chunks = [(s, number, part) for s in semigroups for number, cost in s.satisfied if cost > PART
              for part in parts(source, s, number, laws)]

    def local(semigroup: Semigroup, texts: list[str]) -> str:
        magma = _magma(source, semigroup)
        return f"section\nattribute [local instance] {magma}\n\n" + "\n".join(texts) + "\nend\n"

    part_files = _packed([(local(s, [text]), cost) for s, _, (_, text, cost) in chunks], 10 * PART)
    for k, texts in enumerate(part_files):
        (directory / f"SemigroupParts{k}.lean").write_text(
            header["Semigroups"].replace("\n\n", f"\nimport {args.module}.SemigroupTables\n\n", 1)
            + "\n".join(texts), encoding="utf-8")
        files.append(f"SemigroupParts{k}")
    imports = "".join(f"import {args.module}.SemigroupParts{k}\n" for k in range(len(part_files)))
    facts_texts = []
    for s in semigroups:
        whole = [assembled(source, s, number, laws)[1] for number, cost in s.satisfied if cost > PART]
        facts_texts.append(((local(s, whole) if whole else "") + facts_theorem(source, s, laws),
                            sum(cost for _, cost in s.satisfied if cost <= PART) + len(s.refuted)))
    for k, texts in enumerate(_packed(facts_texts, 2 * PART)):
        (directory / f"Semigroups{k}.lean").write_text(
            header["Semigroups"].replace("\n\n", f"\nimport {args.module}.SemigroupTables\n{imports}\n", 1)
            + "\n".join(texts), encoding="utf-8")
        files.append(f"Semigroups{k}")
    (args.output / f"{args.module}.lean").write_text(
        "".join(f"import {args.module}.{name}\n" for name in ["Equations", *files]), encoding="utf-8")
    print(f"Wrote {len(declared)} laws, {len(theorems)} implications and {len(semigroups)} semigroups "
          f"in {len(files) + 1} files to {directory}")


if __name__ == "__main__":
    main()
