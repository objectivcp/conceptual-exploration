"""The result of an exploration as data in the ETP's form.

Laws are named by their ETP numbers (lean_etp.py's numbering, which extends
the ETP's 4694 laws by its own scheme) and written as the ETP writes them,
with ◇. Writes in DATA_DIR:

- laws.txt: the laws of the exploration, one `N: law` a line;
- implications.json and implications.txt, the latter with the laws written
  out: the implications found, simplified as simplified_implications.txt
  has them (premises and conclusions cut to what the symmetries and the
  other implications do not give, those then redundant dropped), the
  background implications first, each followed by its dual image; an
  implication whose premise only one-element magmas satisfy concludes
  everything. With CERTIFICATES, an unconfirmed implication that the
  certificates entail counts as proved. With --background-label, the
  background implications carry it as their origin (`(background: ETP)`),
  with `and reversal` (`and duality` for magmas) when their conclusions do
  not follow from the background implications without their duals, and
  their duals name them; with --etp-data, an implication is marked new when
  a law of its conclusion follows from no single law of its premise, nor
  from an assumed law, by chains of the ETP's implications and their duals
  (reversals among semigroups), through any ETP laws (an implication
  concluding everything, when none implies x = y): the ETP studies
  implications from one law, and assumed laws such as associativity make
  every premise larger than one law;
- magmas.txt: each finite magma of the context, as `Table [[...]]` followed
  by the laws it satisfies and those it refutes, as in the ETP's `Facts`;
  with --reduce, only the magmas whose rows are not intersections of the
  rows of other objects, free magmas included;
- free_magmas.json, if the exploration has free magmas: each with its
  premise and the laws known to hold and to fail in it, and the rewrite
  system that certifies the failures, if completion.py wrote one.

usage: etp_export.py RESULTS_DIR --etp ETP_DIR -o DATA_DIR [--certificates CERTIFICATES]
                     [--background-label TEXT] [--etp-data DIR]
                     [--equations FILE] [--axiom LAW ...] [--reduce] [--root DIR]

--etp-data is the directory fetch_etp.py writes, with the ETP's graph.json
and equations.txt. --equations and --axiom stand in for the settings.toml of
explorations run before it was saved.
"""

from __future__ import annotations

import argparse
import json
import lzma
import sys
import tomllib
from collections.abc import Sequence
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from conceptual_exploration.core.implication import Implication
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from conceptual_exploration.exploration.basis import simplified_implications
from explorations.equational_theories.certificates import parse_law
from explorations.equational_theories import etp as etp_data
from explorations.equational_theories.etp import ImplicationClosure, ImplicationGraph
from explorations.equational_theories.lean_etp import EtpLaws
from explorations.equational_theories.magma import ETP, Equation
from explorations.equational_theories.verify import (
    exploration_setting, irreducible, law_key, object_tables, read_context,
)


def key(equation: Equation):
    """How implications.json and the context name a law."""
    return equation.id if equation.id is not None else equation.name


def _closure(mask: int, implications: list[tuple[int, int]]) -> int:
    changed = True
    while changed:
        changed = False
        for premise, conclusion in implications:
            if premise & ~mask == 0 and conclusion & ~mask:
                mask |= conclusion
                changed = True
    return mask


class Export:
    def __init__(self, results: Path, equations_file: Path, axioms: Sequence[str], etp: Path,
                 certificates: Path | None = None, duality: bool = True,
                 background_label: str | None = None, closure: ImplicationClosure | None = None,
                 map_unconfirmed: bool = True):
        self.results = results
        self.equations = ETP.load_equations(equations_file)
        entries = json.loads(equations_file.read_text(encoding="utf-8"))
        self.by_key = {key(eq): eq for eq in self.equations}
        self.assumed = [eq for eq in self.equations if str(key(eq)) in {str(a) for a in axioms}]
        associativity = Equation.parse("x * (y * z) = (x * y) * z")
        self.associative = any(eq.is_equivalent_to(associativity) for eq in self.assumed)
        self.laws = EtpLaws(etp)
        texts = {(e["id"] if "id" in e else e["name"]): e["equation"] for e in entries}
        self.number = {eq: self.laws.number(parse_law(texts[key(eq)])) for eq in self.equations}
        self.certified = self._certified(certificates) if certificates else None
        self.duality = duality
        self.background_label = background_label
        # As the exploration had it: with --ask-unconfirmed-duals, the dual of
        # an unconfirmed implication is not its image but an implication of
        # its own, accepted or refuted in turn.
        self.map_unconfirmed = map_unconfirmed
        self.closure = closure
        self.bit = {eq: 1 << i for i, eq in enumerate(self.equations)}
        # Laws that hold everywhere: the assumed ones and the trivial ones.
        self.always = (sum(self.bit[eq] for eq in self.assumed)
                       | sum(self.bit[eq] for eq in self.equations if eq.lhs == eq.rhs))
        self.raw_background: list[tuple[int, int]] = []

    def _certified(self, path: Path) -> list[tuple[int, int]]:
        """The certified implications, as masks over the equations."""
        bit = {eq: 1 << i for i, eq in enumerate(self.equations)}
        texts = {law_key(parse_law(f"{eq.lhs} = {eq.rhs}"), self.associative): eq for eq in self.equations}
        opener = lzma.open if path.suffix == ".xz" else open
        implications = []
        with opener(path, "rt", encoding="utf-8") as file:
            for line in file:
                if line.strip():
                    certificate = json.loads(line)
                    laws = [texts.get(law_key(parse_law(p), self.associative))
                            for p in [*certificate["premise"], certificate["conclusion"]]]
                    if None not in laws:
                        implications.append((sum(bit[eq] for eq in laws[:-1]), bit[laws[-1]]))
        return implications

    def _entailed(self, implication: Implication[Equation]) -> bool:
        mask = _closure(sum(self.bit[eq] for eq in implication.premise) | self.always, self.certified)
        return all(mask & self.bit[eq] for eq in implication.conclusion)

    def _direct(self, premise, conclusion) -> bool:
        """Whether the background implications, without their duals, give
        the conclusion from the premise."""
        mask = _closure(sum(self.bit[eq] for eq in premise) | self.always, self.raw_background)
        return all(mask & self.bit[eq] for eq in conclusion)

    def bases(self) -> tuple[ExplorationBase, ExplorationBase]:
        """The exploration's implications, as accepted, and its background
        alone, each in a base with the duality."""
        mappings = [ETP.get_duality_mapping(self.equations, associative=self.associative)] if self.duality else []
        base = ExplorationBase(attributes=self.equations, mappings=mappings, map_unconfirmed=self.map_unconfirmed)
        background = ExplorationBase(attributes=self.equations, mappings=mappings)
        for entry in json.loads((self.results / "implications.json").read_text(encoding="utf-8")):
            implication = Implication([self.by_key[k] for k in entry["premise"]],
                                      [self.by_key[k] for k in entry["conclusion"]])
            source = entry["source"]
            if source == "background":
                self.raw_background.append((sum(self.bit[eq] for eq in implication.premise),
                                            sum(self.bit[eq] for eq in implication.conclusion)))
                base.add_background(implication)
                background.accept(implication, ImplicationSource.CONFIRMED)
            elif source == "confirmed":
                base.accept(implication, ImplicationSource.CONFIRMED)
            elif source == "unconfirmed":
                proved = self.certified is not None and self._entailed(implication)
                base.accept(implication, ImplicationSource.CONFIRMED if proved else ImplicationSource.UNCONFIRMED)
            # Mapped implications are the images the bases add themselves.
        return base, background

    def implications(self) -> list[dict]:
        """The simplified background implications and the simplified
        implications found, each followed by its dual."""
        base, background = self.bases()
        mapping = base.mappings[0] if base.mappings else (lambda eq: eq)
        listed, seen = [], set()
        for tag, simplified, background_implications in (("B", simplified_implications(background), True),
                                                         ("", simplified_implications(base), False)):
            for k, implication in enumerate(simplified, start=1):
                source = "background" if background_implications else (
                    "proved" if implication.source is ImplicationSource.CONFIRMED else "unconfirmed")
                own = (implication.premise, implication.conclusion)
                image = (frozenset(map(mapping, implication.premise)),
                         frozenset(map(mapping, implication.conclusion)))
                entries = [(f"{tag}{k}", own, source)]
                # An unconfirmed implication whose dual was asked in turn has no dual.
                if image != own and (self.map_unconfirmed or source != "unconfirmed"):
                    entries.append((f"{tag}{k}^op", image, f"dual of {tag}{k}"))
                for name, (premise, conclusion), provenance in entries:
                    numbers = (sorted(self.number[eq] for eq in premise), sorted(self.number[eq] for eq in conclusion))
                    identity = (tuple(numbers[0]), () if implication.everything else tuple(numbers[1]))
                    if identity in seen:
                        continue
                    seen.add(identity)
                    entry = {"name": name, "premise": numbers[0],
                             "conclusion": "everything" if implication.everything else numbers[1], "source": provenance}
                    if background_implications and self.background_label and provenance == source:
                        entry["origin"] = self.background_label + (
                            "" if self._direct(premise, conclusion)
                            else " and reversal" if self.associative else " and duality")
                    if self.closure is not None:
                        entry["new"] = self.new(numbers[0], [2] if implication.everything else numbers[1])
                    listed.append(entry)
        return listed

    def new(self, premise: list[int], conclusion: list[int]) -> bool:
        """Whether a law of the conclusion follows from no single law of the
        premise, nor from an assumed law, by the ETP's implications and their
        duals."""
        sources = set(premise) | {self.number[eq] for eq in self.assumed}
        implied = 0
        for law in sources:
            implied |= self.closure.implied(law)

        def known(law: int) -> bool:
            return law == 1 or law in sources or law <= self.closure.size and implied >> (law - 1) & 1
        return not all(map(known, conclusion))

    def law_text(self, number: int) -> str:
        return self.laws.text(number)

    def magmas(self, reduce: bool) -> list[tuple[list[list[int]], list[int], list[int]]]:
        """Each finite magma of the context, a table once: its table, the
        laws it satisfies and those it refutes; with `reduce`, only those
        whose rows are not intersections of the rows of other objects."""
        objects, names, rows = read_context(self.results / "context.cxt")
        tables = object_tables(self.results)
        numbers = [self.number[self.by_key[_context_key(name)]] for name in names]
        masks = {name: sum(1 << j for j, entry in enumerate(row) if entry == "X") for name, row in zip(objects, rows)}
        kept = irreducible(masks) if reduce else set(objects)
        found, seen = [], set()
        for name in objects:
            if name in tables and name in kept and (masks[name], json.dumps(tables[name])) not in seen:
                seen.add((masks[name], json.dumps(tables[name])))
                found.append((tables[name], masks[name]))
        everything = range(len(names))
        return [(table, sorted(numbers[j] for j in everything if mask >> j & 1),
                 sorted(numbers[j] for j in everything if not mask >> j & 1)) for table, mask in found]

    def free_magmas(self) -> list[dict]:
        path = self.results / "free_magmas.json"
        if not path.exists():
            return []
        certificates = {}
        certified = self.results / "free_magma_certificates.json"
        if certified.exists():
            for entry in json.loads(certified.read_text(encoding="utf-8")):
                certificates[frozenset(map(str, entry["premise"]))] = entry
        listed = []
        for magma in json.loads(path.read_text(encoding="utf-8")):
            entry = {
                "premise": sorted(self.number[self.by_key[k]] for k in magma["premise"]),
                "satisfies": sorted(self.number[self.by_key[k]] for k in magma["positive"]),
                "refutes": sorted(self.number[self.by_key[k]] for k in magma["negative"]),
            }
            certificate = certificates.get(frozenset(map(str, magma["premise"])))
            if certificate is not None:
                entry["rewrite_system"] = certificate["rules"]
                entry["certified_refutations"] = sorted(self.number[self.by_key[k]] for k in certificate["certified"])
            listed.append(entry)
        return listed


def etp_closure(directory: Path, associative: bool) -> ImplicationClosure:
    """The closure of the ETP's implications and their duals: among
    semigroups, the reversal of a law, right-associated, is its dual."""
    laws = etp_data.EtpLaws.load(directory / "equations.txt")

    def dual(number: int) -> int | None:
        image = laws.law(number).dual()
        if associative:
            image = Equation(image.lhs.right_associated(), image.rhs.right_associated())
        return laws.id_of(image)
    return ImplicationClosure(ImplicationGraph.load(directory / "graph.json"), dual)


def _context_key(name: str):
    """A law as the context names it: Eq{id}, or its name."""
    return int(name[2:]) if name.startswith("Eq") and name[2:].isdigit() else name


def write(export: Export, directory: Path, reduce: bool) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    numbers = sorted(export.number.values())
    (directory / "laws.txt").write_text("".join(f"{n}: {export.law_text(n)}\n" for n in numbers), encoding="utf-8")
    implications = export.implications()
    (directory / "implications.json").write_text(
        "[\n" + ",\n".join(json.dumps(implication) for implication in implications) + "\n]\n", encoding="utf-8")

    def laws(listed):
        return ", ".join(f"E{n}: {export.law_text(n)}" for n in listed) or "∅"

    def label(entry):
        source = f"{entry['source']}: {entry['origin']}" if "origin" in entry else entry["source"]
        return f"{source}, new" if entry.get("new") else source
    lines = [f"[{r['name']}] {laws(r['premise'])} => "
             f"{'everything' if r['conclusion'] == 'everything' else laws(r['conclusion'])}   ({label(r)})"
             for r in implications]
    (directory / "implications.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    magmas = export.magmas(reduce)
    (directory / "magmas.txt").write_text("".join(
        f"Table {json.dumps(table)}\nSatisfies {json.dumps(satisfied)}\nRefutes {json.dumps(refuted)}\n\n"
        for table, satisfied, refuted in magmas), encoding="utf-8")
    free = export.free_magmas()
    if free:
        (directory / "free_magmas.json").write_text(
            "[\n" + ",\n".join(json.dumps(entry) for entry in free) + "\n]\n", encoding="utf-8")
    proved = sum(r["source"] in ("proved", "background") for r in implications)
    new = f"{sum(1 for r in implications if r.get('new'))} new to the ETP, " if export.closure else ""
    print(f"Wrote {len(numbers)} laws, {len(implications)} implications ({proved} proved or background, "
          f"the rest duals"
          f"{' or unconfirmed' if any(r['source'] == 'unconfirmed' for r in implications) else ''}), {new}"
          f"{len(magmas)} magmas and {len(free)} free magmas to {directory}")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="The result of an exploration as data in the ETP's form.")
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR")
    parser.add_argument("--etp", type=Path, required=True, metavar="ETP_DIR", help="a checkout of the ETP")
    parser.add_argument("-o", "--output", type=Path, required=True, metavar="DATA_DIR")
    parser.add_argument("--certificates", type=Path, default=None)
    parser.add_argument("--equations", type=Path, default=None, help="the equations file, if no settings.toml")
    parser.add_argument("--axiom", nargs="*", default=None, help="the axioms, if no settings.toml")
    parser.add_argument("--reduce", action="store_true", help="only the magmas with irreducible rows")
    parser.add_argument("--background-label", default=None, metavar="TEXT",
                        help="the origin of the background implications, such as ETP")
    parser.add_argument("--etp-data", type=Path, default=None, metavar="DIR",
                        help="the ETP's graph.json and equations.txt, to mark the implications new to the ETP")
    parser.add_argument("--root", type=Path, default=Path("."),
                        help="the directory the exploration was run from (default: the current one)")
    args = parser.parse_args(argv)
    equations, axioms = exploration_setting(args.results, args.root, args.equations, args.axiom)
    settings_path = args.results / "settings.toml"
    settings = tomllib.loads(settings_path.read_text(encoding="utf-8")) if settings_path.exists() else {}
    export = Export(args.results, equations, axioms, args.etp, args.certificates,
                    duality=not settings.get("no-duality", False), background_label=args.background_label,
                    map_unconfirmed=not settings.get("ask-unconfirmed-duals", False))
    if args.etp_data:
        export.closure = etp_closure(args.etp_data, export.associative)
    write(export, args.output, args.reduce)


if __name__ == "__main__":
    main()
