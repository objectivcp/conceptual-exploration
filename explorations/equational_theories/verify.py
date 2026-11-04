"""Check the result of an exploration of laws from its evidence.

usage: verify.py RESULTS_DIR CERTIFICATES [--classes] [--equations FILE --axiom LAW ...]
       verify.py RESULTS_DIR --lean LEAN_DIR ... --etp ETP_DIR [--classes] [--free-rows]

RESULTS_DIR is an exploration's output (settings.toml, context.cxt,
magmas.json, and free_magma_tables.json if some free magmas have finite
stand-ins with the same rows; --equations and --axiom stand in for the
settings.toml of explorations run before it was saved) and CERTIFICATES a file of proof certificates (certificates.py),
one JSON object a line, compressed with xz if it ends in .xz. The checks:

1. every object of the context is a finite magma of magmas.json in which the
   axioms of the exploration hold, and every entry of its row is right: each
   law is evaluated on the table by brute force;
2. every certificate is right, its premise and conclusion being laws of the
   exploration, up to renaming variables and swapping sides (and, with
   associativity as an axiom, up to bracketing): each is an implication;
3. the sets closed under these implications, the axioms and the laws whose
   sides are the same are exactly the intents of the context
   (conceptual_exploration.verification), so that the implications are a
   basis of the theory of the laws, and the number of theories is the number
   of intents;
4. with --classes, for an exploration of semigroup laws whose laws stand for
   classes, as listed in the equations file: the classes hold all semigroup
   laws up to the largest order of the laws, each once (the trivial ones
   possibly by x = x alone), and certificates
   prove each law of a class equivalent to the class's law. The classes are
   then distinct by 3, two laws with different columns being inequivalent.

None of this uses the code of the exploration: certificates.py checks the
proofs, the evaluation here the tables, and the library's verification
module the closure systems. Prints what it checked; exits with an error at
the first discrepancy.

With --lean, the evidence is instead the statements of Lean files in the
ETP's form (lean_etp.py), once Lean has checked their proofs: the laws are
read from their `equation` declarations and the ETP's, the implications
from the signatures of the theorems `(G : Type*) [Magma G] (h3 : Equation3
G) ... : EquationN G`, and the rows from the `Facts G [satisfied]
[refuted]` of the semigroups: each row is the closure of its satisfied laws
under the implications, which must give every law of the exploration but
the refuted ones; with --free-rows, the rows of the free magmas without
finite stand-ins, which rest on other evidence (completion.py), are taken
from the context. Checks 3 and 4 then run on these.
"""

from __future__ import annotations

import argparse
import itertools
import json
import lzma
import os
import random
import re
import sys
import time
import tomllib
from collections.abc import Sequence
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from conceptual_exploration.verification import VerificationError, check_closure_systems
from explorations.equational_theories.certificates import CertificateError, check_certificate, parse_law, word_law


# Laws up to renaming variables and swapping sides.

def _leaves(term) -> list[str]:
    return [term] if isinstance(term, str) else _leaves(term[0]) + _leaves(term[1])


def _shape(term, names: dict):
    if isinstance(term, str):
        return names.setdefault(term, len(names))
    return (_shape(term[0], names), _shape(term[1], names))


def law_key(law: tuple, associative: bool):
    """The law with its variables numbered in order of first occurrence, the
    smaller of its two ways round; for semigroups, on its words."""
    forms = []
    for a, b in (law, law[::-1]):
        names: dict = {}
        if associative:
            forms.append((tuple(names.setdefault(v, len(names)) for v in _leaves(a)),
                          tuple(names.setdefault(v, len(names)) for v in _leaves(b))))
        else:
            forms.append(repr((_shape(a, names), _shape(b, names))))
    return min(forms)


# Laws in finite magmas, by brute force.

def is_associative(table: Sequence[Sequence[int]]) -> bool:
    n = range(len(table))
    return all(table[table[a][b]][c] == table[a][table[b][c]] for a in n for b in n for c in n)


def nilpotency(table: Sequence[Sequence[int]]) -> tuple[int, int] | None:
    """For a semigroup with a zero z in which every product of k elements
    is z, (k, z) with k smallest, if k is at most 8."""
    size = len(table)
    powers = set(range(size))
    for k in range(2, 9):
        powers = {table[a][b] for a in powers for b in range(size)}
        if len(powers) == 1:
            (zero,) = powers
            if all(table[zero][x] == zero == table[x][zero] for x in range(size)):
                return k, zero
            return None
    return None


def holds(table: Sequence[Sequence[int]], law: tuple, nilpotent: tuple[int, int] | None = None) -> bool:
    """Whether the law holds in the magma: every assignment is tried, those of
    the last variable at once. With `nilpotent` (k, z), a side of k or more
    leaves is z, as in a nilpotent semigroup."""
    size = len(table)
    sides = list(law)
    if nilpotent is not None:
        sides = [nilpotent[1] if len(_leaves(side)) >= nilpotent[0] else side for side in sides]
    variables = sorted({v for side in sides if not isinstance(side, int) for v in _leaves(side)})
    if not variables:
        return sides[0] == sides[1] if all(isinstance(s, int) for s in sides) else True
    *fixed, last = variables
    column = list(range(size))

    def value(term, env):
        if isinstance(term, int):
            return term
        if isinstance(term, str):
            return column if term == last else env[term]
        left, right = value(term[0], env), value(term[1], env)
        if isinstance(left, list):
            return [table[a][b] for a, b in zip(left, right)] if isinstance(right, list) else \
                [table[a][right] for a in left]
        return [table[left][b] for b in right] if isinstance(right, list) else table[left][right]

    def differ(env) -> bool:
        a, b = value(sides[0], env), value(sides[1], env)
        a, b = (a if isinstance(a, list) else [a] * size), (b if isinstance(b, list) else [b] * size)
        return a != b

    # Laws that fail mostly fail on a few random assignments; then every one.
    sample = random.Random(0)
    for _ in range(64 if size ** len(fixed) > 256 else 0):
        if differ({v: sample.randrange(size) for v in fixed}):
            return False
    return not any(differ(dict(zip(fixed, values))) for values in itertools.product(range(size), repeat=len(fixed)))


# The semigroup laws up to an order, as keys of law_key.

def semigroup_laws(max_order: int) -> set:
    """All semigroup laws whose sides have at most max_order + 2 letters in
    all, as keys, the trivial ones included."""
    keys = set()
    for length in range(2, max_order + 3):
        for left in range(1, length):
            for word in _words(length):
                a, b = word[:left], word[left:]
                keys.add(law_key((_word_term(a), _word_term(b)), True))
    return keys


def _words(length: int):
    """The words of a length with variables numbered in order of first
    occurrence."""
    def extend(word, used):
        if len(word) == length:
            yield word
            return
        for v in range(used + 1):
            yield from extend(word + (v,), max(used, v + 1))
    yield from extend((), 0)


def _word_term(word: Sequence[int]):
    term = f"v{word[-1]}"
    for v in reversed(word[:-1]):
        term = (f"v{v}", term)
    return term


def read_context(path: Path) -> tuple[list[str], list[str], list[str]]:
    lines = path.read_text(encoding="utf-8").split("\n")
    if lines[0] != "B":
        raise VerificationError(f"{path} is not a Burmeister context")
    n, m = int(lines[2]), int(lines[3])
    objects, attributes = lines[5:5 + n], lines[5 + n:5 + n + m]
    rows = lines[5 + n + m:5 + n + m + n]
    return objects, attributes, rows


def irreducible(rows: dict[str, int]) -> set[str]:
    """The objects, by name, whose rows (as masks) are not the intersection
    of the rows strictly containing them, the first of each row: the others
    add no intent."""
    distinct = set(rows.values())
    kept = set()
    for mask in distinct:
        meet, above = -1, False
        for other in distinct:
            if other != mask and other & mask == mask:
                meet &= other
                above = True
        if not above or meet != mask:
            kept.add(mask)
    names, seen = set(), set()
    for name, mask in rows.items():
        if mask in kept and mask not in seen:
            seen.add(mask)
            names.add(name)
    return names


def read_certificates(path: Path) -> list[dict]:
    opener = lzma.open if path.suffix == ".xz" else open
    with opener(path, "rt", encoding="utf-8") as file:
        return [json.loads(line) for line in file if line.strip()]


def exploration_setting(results: Path, root: Path, equations: Path | None = None,
                        axioms: Sequence[str] | None = None) -> tuple[Path, list[str]]:
    """The equations file and the axioms of an exploration, from its
    settings.toml, or as given for an exploration run before it was saved."""
    path = results / "settings.toml"
    settings = tomllib.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    if equations is None and "equations" not in settings:
        raise VerificationError(f"No {path}: give the equations file")
    return (equations or root / settings["equations"],
            [str(a) for a in (axioms if axioms is not None else settings.get("axiom", []))])


def object_tables(results: Path) -> dict[str, list[list[int]]]:
    """The tables of the finite objects of an exploration, by name: its
    magmas, and the finite stand-ins for free magmas, which have the same
    rows, in free_magma_tables.json if there is one."""
    tables = {m["name"]: m["table"] for m in json.loads((results / "magmas.json").read_text(encoding="utf-8"))}
    stand_ins = results / "free_magma_tables.json"
    if stand_ins.exists():
        tables.update({m["name"]: m["table"] for m in json.loads(stand_ins.read_text(encoding="utf-8"))})
    return tables


def _setting(results: Path, root: Path, equations_path: Path | None = None, axioms: Sequence[str] | None = None):
    """The laws of an exploration, by attribute name, its axioms, and
    whether associativity is among them."""
    equations_path, axiom_ids = exploration_setting(results, root, equations_path, axioms)
    equations = json.loads(equations_path.read_text(encoding="utf-8"))
    axiom_ids = set(axiom_ids)
    laws = {}
    for entry in equations:
        name = f"Eq{entry['id']}" if "id" in entry else entry["name"]
        laws[name] = parse_law(entry["equation"])
    axioms = [name for name in laws if name[2:] in axiom_ids and name.startswith("Eq")]
    associative = any(law_key(laws[a], False) == law_key(parse_law("(x * y) * z = x * (y * z)"), False)
                      for a in axioms)
    return equations, laws, axioms, associative


def check_classes(equations: list[dict], laws: dict, attributes: Sequence[str], key_of: dict,
                  single: set) -> None:
    """Check 4: `single` holds the (premise, conclusion) keys of the proved
    implications with one law besides the axioms."""
    members: dict = {}  # law: the laws of the equations file in whose class it is
    classes_of: dict = {}
    for entry in equations:
        name = f"Eq{entry['id']}" if "id" in entry else entry["name"]
        classes_of[name] = {law_key(word_law(word), True) for word in entry["class"]}
        for key in classes_of[name]:
            members.setdefault(key, set()).add(name)
    max_order = max(len(_leaves(laws[a][0])) + len(_leaves(laws[a][1])) - 2 for a in attributes)
    # The trivial laws are one class, which the equations file may list by
    # x = x alone.
    nontrivial = lambda keys: {key for key in keys if key[0] != key[1]}
    expected, listed = nontrivial(semigroup_laws(max_order)), set(members)
    if nontrivial(listed) != expected:
        raise VerificationError(f"The classes do not list the semigroup laws of order at most {max_order}: "
                                f"{len(expected - listed)} missing, {len(nontrivial(listed) - expected)} extra")
    for key, names in members.items():
        if len({tuple(sorted(map(str, classes_of[name]))) for name in names}) != 1:
            raise VerificationError(f"The law {key} is in two classes")
        for name in names:
            own = key_of[name]
            if key != own and not ((own, key) in single and (key, own) in single):
                raise VerificationError(f"No proofs of the equivalence of {name} and {key}")
    found = {frozenset(n) for n in members.values()}
    print(f"{len(listed)} semigroup laws of order at most {max_order}, each in one class: "
          f"{len(found)} classes, each law proved equivalent to its class's", flush=True)


def verify(results: Path, certificates_path: Path, classes: bool, root: Path,
           equations_path: Path | None = None, axiom_ids: Sequence[str] | None = None) -> None:
    started = time.monotonic()
    equations, laws, axioms, associative = _setting(results, root, equations_path, axiom_ids)
    objects, attributes, rows = read_context(results / "context.cxt")
    if sorted(attributes) != sorted(laws):
        raise VerificationError("The context's attributes are not the laws of the equations file")
    index = {name: i for i, name in enumerate(attributes)}
    key_of = {name: law_key(laws[name], associative) for name in attributes}
    by_key: dict = {}
    for name, key in key_of.items():
        by_key.setdefault(key, name)

    # 1. The objects.
    tables = object_tables(results)
    intents = []
    for name, row in zip(objects, rows):
        table = tables.get(name)
        if table is None:
            raise VerificationError(f"No table for object {name}")
        if not all(len(r) == len(table) and all(0 <= x < len(table) for x in r) for r in table):
            raise VerificationError(f"{name} is not a table of a magma")
        if associative and not is_associative(table):
            raise VerificationError(f"{name} is not a semigroup")
        nilpotent = nilpotency(table) if associative else None
        intent = 0
        for attribute, entry in zip(attributes, row):
            value = holds(table, laws[attribute], nilpotent)
            if entry not in "X." or value != (entry == "X"):
                raise VerificationError(f"{name}, {attribute}: the context says {entry!r}")
            intent |= value << index[attribute]
        intents.append(intent)
    print(f"{len(objects)} objects: their rows are right", flush=True)

    # 2. The certificates.
    certificates = read_certificates(certificates_path)
    axiom_keys = {key_of[a] for a in axioms}
    implications = []
    single = set()  # (premise, conclusion) of the certificates with one law besides the axioms
    for certificate in certificates:
        premise, conclusion = check_certificate(certificate)
        keys = {law_key(law, associative) for law in premise}
        target = law_key(conclusion, associative)
        if all(key in by_key for key in keys | {target}):
            implications.append((sum(1 << index[by_key[key]] for key in keys), 1 << index[by_key[target]]))
        if len(keys - axiom_keys) == 1:
            single.add((next(iter(keys - axiom_keys)), target))
    print(f"{len(certificates)} certificates are right, {len(implications)} of them implications between the laws",
          flush=True)

    # 3. The closure systems.
    always = sum(1 << index[a] for a in axioms) | sum(
        1 << index[a] for a in attributes if laws[a][0] == laws[a][1])
    count = check_closure_systems(len(attributes), intents, implications + [(0, always)], os.cpu_count() or 1)
    print(f"The implications are a basis of the theory: {count} closed sets, the intents of the context", flush=True)

    # 4. The classes.
    if classes:
        if not associative:
            raise VerificationError("Classes are checked for semigroup laws only")
        check_classes(equations, laws, attributes, key_of, single)
    print(f"Checked in {time.monotonic() - started:.0f} s")


_EQUATION = re.compile(r"^\s*equation (\d+)\s*:=\s*(.*?)\s*$", re.M)
_THEOREM = re.compile(r"^theorem \S+ \(G : Type\*\) \[Magma G\]((?: \(h\d+ : Equation\d+ G\))*) : "
                      r"Equation(\d+) G := by$", re.M)
_HYPOTHESIS = re.compile(r"\(h\d+ : Equation(\d+) G\)")
_FACTS = re.compile(r"^@\[equational_result\]\ntheorem «Facts from ([^»]*)» :\n"
                    r"  ∃ \(G : Type\) \(_ : Magma G\) \(_: Finite G\), Facts G \[([\d, ]*)\] \[([\d, ]*)\] :=", re.M)


def verify_lean(results: Path, lean: Sequence[Path], etp: Path, classes: bool, root: Path,
                equations_path: Path | None = None, axiom_ids: Sequence[str] | None = None,
                free_rows: bool = False) -> None:
    started = time.monotonic()
    equations, laws, axioms, associative = _setting(results, root, equations_path, axiom_ids)
    attributes = list(laws)
    index = {name: i for i, name in enumerate(attributes)}
    key_of = {name: law_key(laws[name], associative) for name in attributes}
    by_key: dict = {}
    for name, key in key_of.items():
        by_key.setdefault(key, name)
    sources = sorted(p for path in lean for p in (path.glob("*.lean") if path.is_dir() else [path]))
    texts = [path.read_text(encoding="utf-8") for path in sources]
    numbered: dict[int, tuple] = {}
    for text in texts + [path.read_text(encoding="utf-8")
                         for path in sorted((etp / "equational_theories" / "Equations").glob("*.lean"))]:
        for number, law in _EQUATION.findall(text):
            if int(number) in numbered:
                raise VerificationError(f"Equation{number} is declared twice")
            numbered[int(number)] = parse_law(law.replace("◇", "*"))

    def key(number: str):
        if int(number) not in numbered:
            raise VerificationError(f"Equation{number} is not declared")
        return law_key(numbered[int(number)], associative)

    # The implications.
    implications, single, count = [], set(), 0
    axiom_keys = {key_of[a] for a in axioms}
    for text in texts:
        for hypotheses, conclusion in _THEOREM.findall(text):
            count += 1
            keys = {key(n) for n in _HYPOTHESIS.findall(hypotheses)}
            target = key(conclusion)
            if all(k in by_key for k in keys | {target}):
                implications.append((sum(1 << index[by_key[k]] for k in keys), 1 << index[by_key[target]]))
            if len(keys - axiom_keys) == 1:
                single.add((next(iter(keys - axiom_keys)), target))
    print(f"{count} implications stated, {len(implications)} of them between the laws", flush=True)

    # The rows.
    always = sum(1 << index[a] for a in axioms) | sum(
        1 << index[a] for a in attributes if laws[a][0] == laws[a][1])
    rules = implications + [(0, always)]

    def closure(mask: int) -> int:
        changed = True
        while changed:
            changed = False
            for premise, conclusion in rules:
                if premise & ~mask == 0 and conclusion & ~mask:
                    mask |= conclusion
                    changed = True
        return mask

    full, intents, named = (1 << len(attributes)) - 1, [], set()
    for text in texts:
        for name, satisfied, refuted in _FACTS.findall(text):
            named.add(name.split(" ")[-1])
            masks = []
            for numbers in (satisfied, refuted):
                mask = 0
                for n in filter(None, (s.strip() for s in numbers.split(","))):
                    if key(n) not in by_key:
                        raise VerificationError(f"{name}: Equation{n} is not a law of the exploration")
                    mask |= 1 << index[by_key[key(n)]]
                masks.append(mask)
            # The table satisfies the axioms, such as associativity, by its facts.
            if any(not masks[0] >> index[a] & 1 for a in axioms):
                raise VerificationError(f"{name}: its facts do not include the axioms")
            intent = closure(masks[0])
            if intent & masks[1] or intent | masks[1] != full:
                raise VerificationError(f"{name}: the implications do not give its row from its facts")
            intents.append(intent)
    print(f"{len(intents)} magmas: their facts give their rows", flush=True)
    if free_rows:
        # The free magmas, as the context has them: finite magmas need facts.
        objects, context_attributes, rows = read_context(results / "context.cxt")
        tables, added = object_tables(results), 0
        for name, row in zip(objects, rows):
            if name not in named and name not in tables:
                intents.append(sum(1 << index[a] for a, entry in zip(context_attributes, row) if entry == "X"))
                added += 1
        print(f"{added} free magmas, their rows taken from the context", flush=True)

    count = check_closure_systems(len(attributes), intents, rules, os.cpu_count() or 1)
    print(f"The implications are a basis of the theory: {count} closed sets, the intents of the objects",
          flush=True)
    if classes:
        if not associative:
            raise VerificationError("Classes are checked for semigroup laws only")
        check_classes(equations, laws, attributes, key_of, single)
    print(f"Checked in {time.monotonic() - started:.0f} s")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Check the result of an exploration of laws from its evidence.")
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR")
    parser.add_argument("certificates", type=Path, metavar="CERTIFICATES", nargs="?")
    parser.add_argument("--lean", type=Path, nargs="+", metavar="LEAN_DIR",
                        help="check the statements of the Lean files in the ETP's form in these directories "
                             "(or these files) instead")
    parser.add_argument("--etp", type=Path, metavar="ETP_DIR", help="with --lean, a checkout of the ETP")
    parser.add_argument("--classes", action="store_true",
                        help="also check the classes of semigroup laws listed in the equations file")
    parser.add_argument("--root", type=Path, default=Path("."),
                        help="the directory the exploration was run from (default: the current one)")
    parser.add_argument("--equations", type=Path, default=None, help="the equations file, if no settings.toml")
    parser.add_argument("--axiom", nargs="*", default=None, help="the axioms, if no settings.toml")
    parser.add_argument("--free-rows", action="store_true",
                        help="with --lean, take the rows of the free magmas without finite stand-ins "
                             "from the context")
    args = parser.parse_args(argv)
    if (args.certificates is None) == (args.lean is None) or (args.lean is None) != (args.etp is None):
        parser.error("give CERTIFICATES, or --lean and --etp")
    try:
        if args.lean is not None:
            verify_lean(args.results, args.lean, args.etp, args.classes, args.root, args.equations, args.axiom,
                        args.free_rows)
        else:
            verify(args.results, args.certificates, args.classes, args.root, args.equations, args.axiom)
    except (VerificationError, CertificateError) as error:
        sys.exit(f"verify.py: {error}")


if __name__ == "__main__":
    main()
