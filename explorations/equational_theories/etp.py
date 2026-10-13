"""Data of the Equational Theories Project (ETP) as input to an exploration.

The ETP decided every implication between two of its 4694 laws, numbered by
their line in its equations.txt. Three of its files are read here:

- equations.txt, the laws, one per line, with ◇ for the operation
  (https://github.com/teorth/equational_theories/blob/main/data/equations.txt);
- graph.json, the implication graph its website shows: the 4694 x 4694
  outcomes, row the premise and column the conclusion, run-length encoded
  (https://teorth.github.io/equational_theories/implications/graph.json);
- files of finite magmas with one "Table [[...]]" per magma, such as those in
  equational_theories/Generated/All4x4Tables/data, or with an equation number
  before each table, as in data/smallest_magma_examples.txt.

The graph gives every implication with a single premise between laws of the
ETP, which an exploration can take as background implications and then only
ask about implications whose premise has several laws. Its magmas can seed the
expert's pool or the context.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections.abc import Iterable, Sequence
from math import isqrt
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from conceptual_exploration.core.implication import Implication
from explorations.equational_theories.magma import Equation, Magma, Op, Term, Var

GRAPH_URL = "https://teorth.github.io/equational_theories/implications/graph.json"
EQUATIONS_URL = "https://raw.githubusercontent.com/teorth/equational_theories/main/data/equations.txt"

# The outcomes of graph.json, as numbered by the ETP website.
_TRUE = {3, 7}  # explicit and implicit proofs of the implication
_FALSE = {2, 6}  # explicit and implicit proofs of its negation


def _variables_in_order(term: Term, seen: list[str]) -> None:
    if isinstance(term, Var):
        if term.name not in seen:
            seen.append(term.name)
    else:
        _variables_in_order(term.left, seen)
        _variables_in_order(term.right, seen)


def canonical_form(equation: Equation) -> str:
    """The same string for two laws exactly when one becomes the other by
    renaming variables and swapping sides.

    Each side order is written with the variables renamed in the order of
    their first occurrence, and the smaller string is taken.
    """
    forms = []
    for lhs, rhs in ((equation.lhs, equation.rhs), (equation.rhs, equation.lhs)):
        seen: list[str] = []
        _variables_in_order(lhs, seen)
        _variables_in_order(rhs, seen)
        renaming = {name: Var(f"v{k}") for k, name in enumerate(seen)}
        forms.append(f"{lhs.substitute(renaming)} = {rhs.substitute(renaming)}")
    return min(forms)


class EtpLaws:
    """The laws of the ETP, numbered from 1 by their line in equations.txt."""

    def __init__(self, laws: Sequence[Equation]) -> None:
        self.laws = list(laws)
        self._ids = {canonical_form(eq): eq.id for eq in self.laws}

    @classmethod
    def load(cls, path: str | Path) -> EtpLaws:
        lines = Path(path).read_text(encoding="utf-8").splitlines()
        return cls([
            Equation.parse(line.replace("◇", "*"), id=number)
            for number, line in enumerate(lines, start=1)
        ])

    def __len__(self) -> int:
        return len(self.laws)

    def law(self, number: int) -> Equation:
        return self.laws[number - 1]

    def id_of(self, equation: Equation) -> int | None:
        """The number of the ETP law equal to `equation` up to renaming
        variables and swapping sides, or None if the ETP does not list it."""
        return self._ids.get(canonical_form(equation))

    def identify(self, equations: Iterable[Equation]) -> dict[Equation, int]:
        """The ETP number of each of `equations` the ETP lists.

        Raises ValueError if an equation's own id is not the number of the
        law the ETP lists under it.
        """
        numbers = {}
        for eq in equations:
            number = self.id_of(eq)
            if eq.id is not None and eq.id != number:
                listed = f"Eq{number}" if number is not None else "no number"
                raise ValueError(
                    f"{eq} has id {eq.id}, but the ETP lists Eq{eq.id} as "
                    f"{self.law(eq.id) if 1 <= eq.id <= len(self) else 'nothing'} "
                    f"and this law under {listed}"
                )
            if number is not None:
                numbers[eq] = number
        return numbers

    def with_duals(self, numbers: Iterable[int]) -> list[Equation]:
        """The laws with the given numbers and their duals, in the order of
        their numbers."""
        chosen = set()
        for number in numbers:
            chosen.add(number)
            dual = self.id_of(self.law(number).dual())
            if dual is None:
                raise ValueError(f"The ETP does not list the dual of Eq{number}")
            chosen.add(dual)
        return [self.law(number) for number in sorted(chosen)]


class ImplicationGraph:
    """The ETP's decisions about the implications between two of its laws."""

    def __init__(self, outcomes: bytes | bytearray, size: int) -> None:
        if len(outcomes) != size * size:
            raise ValueError(f"{len(outcomes)} outcomes for {size} laws")
        self.outcomes = outcomes
        self.size = size

    @classmethod
    def load(cls, path: str | Path) -> ImplicationGraph:
        """Read graph.json, whose run-length encoding lists each outcome and
        how many times it repeats, row by row."""
        runs = json.loads(Path(path).read_text(encoding="utf-8"))["rle_encoded_array"]
        outcomes = bytearray(sum(runs[1::2]))
        position = 0
        for value, count in zip(runs[::2], runs[1::2]):
            outcomes[position:position + count] = bytes([value]) * count
            position += count
        size = isqrt(len(outcomes))
        return cls(outcomes, size)

    def implies(self, premise: int, conclusion: int) -> bool:
        """Whether law `premise` implies law `conclusion`, by ETP number.

        Raises ValueError if the ETP has not proved the implication or its
        negation.
        """
        outcome = self.outcomes[(premise - 1) * self.size + conclusion - 1]
        if outcome in _TRUE:
            return True
        if outcome in _FALSE:
            return False
        raise ValueError(f"The ETP has not decided whether Eq{premise} implies Eq{conclusion}")


def graph_background(
        equations: Sequence[Equation],
        graph: ImplicationGraph,
        laws: EtpLaws,
) -> list[Implication[Equation]]:
    """The implications with at most one premise between `equations` that
    the ETP graph decides, as background implications.

    Each equation the ETP lists implies the others it implies by the graph,
    and the empty premise implies those that x = x implies, which are valid
    in every magma. Equations the ETP does not list take no part.
    """
    numbers = laws.identify(equations)
    listed = [eq for eq in equations if eq in numbers]
    background = []
    trivial = laws.id_of(Equation(Var("x"), Var("x")))
    valid = [eq for eq in listed if graph.implies(trivial, numbers[eq])]
    if valid:
        background.append(Implication((), valid))
    for eq in listed:
        conclusion = [
            other for other in listed
            if other != eq and other not in valid and graph.implies(numbers[eq], numbers[other])
        ]
        if conclusion:
            background.append(Implication([eq], conclusion))
    return background


_TABLE = re.compile(r"\[\s*\[[\d,\s\[\]]*\]\s*\]")


def load_tables(path: str | Path) -> list[Magma]:
    """The magmas of an ETP file of tables, one table such as
    [[0, 1], [1, 0]] per line, after "Table" or an equation number; other
    lines are ignored. A table repeated is read once."""
    magmas = []
    seen = set()
    name = Path(path).stem
    for number, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), start=1):
        match = _TABLE.search(line)
        if match is None:
            continue
        table = tuple(tuple(row) for row in json.loads(match.group()))
        if table in seen:
            continue
        seen.add(table)
        magmas.append(Magma(len(table), table, name=f"{name}:{number}"))
    return magmas


def load_magmas(path: str | Path) -> list[Magma]:
    """Magmas from a JSON file in the format of saved results (.json) or from
    an ETP file of tables (any other suffix)."""
    from explorations.equational_theories.magma import ETP

    if Path(path).suffix == ".json":
        return ETP.load_magmas(path)
    return load_tables(path)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Write ETP laws, closed under duality, as an equations file for explore.py."
    )
    parser.add_argument("etp_equations", type=Path, metavar="EQUATIONS_TXT",
                        help=f"the ETP's equations.txt ({EQUATIONS_URL})")
    parser.add_argument("numbers", type=int, nargs="+", metavar="N",
                        help="ETP numbers of the laws; their duals are added")
    parser.add_argument("-o", "--output", type=Path, metavar="PATH",
                        help="where to write the equations (default: standard output)")
    args = parser.parse_args(argv)
    laws = EtpLaws.load(args.etp_equations)
    chosen = laws.with_duals(args.numbers)
    text = "[\n" + ",\n".join(
        "  " + json.dumps({"id": eq.id, "equation": f"{eq.lhs} = {eq.rhs}"}, ensure_ascii=False)
        for eq in chosen
    ) + "\n]\n"
    if args.output is None:
        sys.stdout.write(text)
    else:
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
