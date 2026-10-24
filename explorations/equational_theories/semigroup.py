"""Semigroup laws as pairs of words, and their classes, without the ETP's data.

Among semigroups a term is determined by its word, its variables from left to
right, so a law is a pair of words. Here the variables are numbered from 0 in
the order of their first occurrence, left side first, and the smaller of the
two ways round is taken, so that two laws are equal up to renaming variables
and swapping sides exactly when their forms are. The order of a law is the
number of operations in its two sides, len(u) + len(v) - 2, as for magma
laws; its dual among semigroups is the law with both words reversed.

The ETP's laws and graph stop at order 4. Beyond, the laws up to an order are
generated here and sorted into classes of laws equivalent among semigroups:

1. every law is evaluated on a set of semigroups: all those of a few
   elements, enumerated by Mace4, and any others given, such as the ones an
   exploration found. Two laws with different values on one of them are not
   equivalent, so only laws with the same values are compared next;
2. among those, Vampire tries to prove laws equivalent to a representative,
   the smallest law not yet in a class, in parallel, and the laws it proves
   equivalent join its class; this is repeated with the laws left;
3. for two classes whose representatives Vampire neither proved equivalent
   nor refuted, a second pass tries each implication between them again,
   with Vampire for longer and with Mace4 for a countermodel, and merges the
   classes when both are proved. The models found join the semigroups, and
   may separate other such pairs.

A law Vampire neither proves equivalent to a representative nor refutes stays
out of its class, so a class may be split that is in fact one, which an
exploration of the representatives would find; laws that are not equivalent
are never put in one class.

Run as

    semigroup.py classes results/semigroup_order5_classes --max-order 5 \\
        --seeds results/semigroup_vampire_mace4_e_etp_classes/magmas.json \\
        --etp-equations etp/equations.txt

to write the classes to classes.json in the directory given; with
--from-classes, the second pass starts from the classes of an earlier run.
Then

    semigroup.py inputs results/semigroup_order5_classes/classes.json \\
        --order4 results/semigroup_vampire_mace4_e_etp_classes/implications.json

writes the input of an exploration of the classes (see `exploration_inputs`)
to equations_semigroup5.json, background_semigroup5.json and
seeds_semigroup5.json.
"""

from __future__ import annotations

import argparse
import json
import random
import shutil
import tempfile
import threading
import time
from collections.abc import Callable, Iterable, Sequence
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from itertools import permutations
from pathlib import Path

from explorations.equational_theories.etp import EtpLaws
from explorations.equational_theories.magma import ETP, Equation, Magma, Op, Term, Var
from explorations.equational_theories.vampire import (
    VampireExpert,
    ladr_problem,
    parse_mace4_model,
    tptp_problem,
)

Word = tuple[int, ...]
Law = tuple[Word, Word]

VARIABLES = "xyzwuvtsrq"
ASSOCIATIVITY = Equation.parse("x * (y * z) = (x * y) * z")
ASSOCIATIVITY_NUMBER = 4512  # in the ETP's equations.txt


def canonical(u: Sequence[int], v: Sequence[int]) -> Law:
    """The form of the law u = v, its variables numbered by first occurrence
    and the smaller of its two ways round taken."""
    forms = []
    for a, b in ((u, v), (v, u)):
        names: dict[int, int] = {}
        forms.append((
            tuple(names.setdefault(c, len(names)) for c in a),
            tuple(names.setdefault(c, len(names)) for c in b),
        ))
    return min(forms)


def order(law: Law) -> int:
    return len(law[0]) + len(law[1]) - 2


def variables(law: Law) -> int:
    return max(law[0] + law[1]) + 1


def reversal(law: Law) -> Law:
    """The dual of the law among semigroups."""
    return canonical(law[0][::-1], law[1][::-1])


def sort_key(law: Law) -> tuple:
    return order(law), len(law[0]), law


def laws(max_order: int) -> list[Law]:
    """The laws of order at most `max_order`, the trivial x = x included,
    smallest first."""
    found = {((0,), (0,))}

    def words(length: int, word: list[int], top: int) -> Iterable[Word]:
        # Restricted growth: a variable is at most one more than those before.
        if len(word) == length:
            yield tuple(word)
            return
        for c in range(top + 2):
            word.append(c)
            yield from words(length, word, max(top, c))
            word.pop()

    for length in range(2, max_order + 3):
        for word in words(length, [], -1):
            for cut in range(1, length):
                if word[:cut] != word[cut:]:
                    found.add(canonical(word[:cut], word[cut:]))
    return sorted(found, key=sort_key)


def text(law: Law) -> str:
    """The law with letters for its variables, such as x = xyx."""
    return " = ".join("".join(VARIABLES[c] for c in word) for word in law)


def parse_law(line: str) -> Law:
    """The law written as by `text`."""
    u, v = (tuple(VARIABLES.index(c) for c in word.strip()) for word in line.split("="))
    return canonical(u, v)


def term(word: Word) -> Term:
    result: Term = Var(VARIABLES[word[-1]])
    for c in reversed(word[:-1]):
        result = Op(Var(VARIABLES[c]), result)
    return result


def equation(law: Law, id: int | None = None) -> Equation:
    """The law as a magma law, both sides right-associated, as the ETP writes
    semigroup laws."""
    return Equation(term(law[0]), term(law[1]), id=id)


def law_of(eq: Equation) -> Law:
    """The words of a magma law: its form among semigroups."""
    names: dict[str, int] = {}
    u, v = ([names.setdefault(name, len(names)) for name in side.factors()] for side in (eq.lhs, eq.rhs))
    return canonical(u, v)


class Evaluator:
    """The values of laws in one semigroup, given by its Cayley table.

    Most laws fail on some of a few random assignments. A law that does not
    is evaluated on all size ** variables assignments at once, each word as
    the list of its values, unless there are more than `budget`; its value is
    then unknown (None).
    """

    def __init__(self, table: Sequence[Sequence[int]], budget: int = 2 ** 21, samples: int = 64, seed: int = 0):
        self.table = tuple(tuple(row) for row in table)
        self.size = len(self.table)
        self.budget = budget
        self.samples = samples
        self._random = random.Random(seed)
        self._columns: dict[int, list[list[int]]] = {}

    def _value(self, word: Word, assignment: Sequence[int]) -> int:
        result = assignment[word[0]]
        for c in word[1:]:
            result = self.table[result][assignment[c]]
        return result

    def _values(self, word: Word, columns: list[list[int]]) -> list[int]:
        result = columns[word[0]]
        for c in word[1:]:
            result = [self.table[a][b] for a, b in zip(result, columns[c])]
        return result

    def columns(self, count: int) -> list[list[int]]:
        """The values of `count` variables over all assignments, the last
        variable varying fastest."""
        if count not in self._columns:
            n, total = self.size, self.size ** count
            self._columns[count] = [
                [i // n ** (count - 1 - k) % n for i in range(total)] for k in range(count)
            ]
        return self._columns[count]

    def holds(self, law: Law) -> bool | None:
        u, v = law
        count = variables(law)
        for _ in range(self.samples):
            assignment = [self._random.randrange(self.size) for _ in range(count)]
            if self._value(u, assignment) != self._value(v, assignment):
                return False
        if self.size ** count > self.budget:
            return None
        columns = self.columns(count)
        return self._values(u, columns) == self._values(v, columns)


def _evaluate(args: tuple) -> list[bool | None]:
    table, laws, budget = args
    evaluator = Evaluator(table, budget)
    return [evaluator.holds(law) for law in laws]


def evaluate(
        semigroups: Sequence[Magma],
        laws: Sequence[Law],
        budget: int = 2 ** 21,
        workers: int = 1,
) -> list[list[bool | None]]:
    """The values of the laws on each semigroup, a row per semigroup."""
    jobs = [(m.table, laws, budget) for m in semigroups]
    if workers <= 1:
        return [_evaluate(job) for job in jobs]
    with ProcessPoolExecutor(workers) as pool:
        return list(pool.map(_evaluate, jobs))


def isomorphism_form(table: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    """The same table for isomorphic magmas: the smallest relabelling."""
    n = len(table)
    best = None
    for p in permutations(range(n)):
        inverse = [0] * n
        for a, b in enumerate(p):
            inverse[b] = a
        form = tuple(tuple(p[table[inverse[r]][inverse[c]]] for c in range(n)) for r in range(n))
        if best is None or form < best:
            best = form
    return best


def small_semigroups(max_size: int, mace4: str = "mace4", commutative: bool = False) -> list[Magma]:
    """The semigroups, or the commutative ones, of at most `max_size`
    elements, up to isomorphism (but not anti-isomorphism, so that the dual
    of each is there too), by Mace4."""
    executable = shutil.which(mace4)
    if executable is None:
        raise FileNotFoundError(f"Mace4 executable {mace4!r} not found")
    problem = "formulas(assumptions).\n(x * y) * z = x * (y * z).\n"
    problem += ("x * y = y * x.\n" if commutative else "") + "end_of_list.\n"
    # Mace4 starts at two elements.
    found: dict[tuple, Magma] = {((0,),): Magma(1, ((0,),), name="S1-1")}
    for size in range(2, max_size + 1):
        output = VampireExpert._execute(
            [executable, "-n", str(size), "-N", str(size), "-m", "-1"], problem, 3600, None
        )
        for block in output.split("interpretation(")[1:]:
            table = parse_mace4_model("interpretation(" + block)
            form = isomorphism_form(table)
            found.setdefault(form, Magma(size, form, name=f"S{size}-{len(found) + 1}"))
    return list(found.values())


def vampire_status(vampire: str, premise: Law, law: Law, time_limit: float) -> str:
    """Vampire's status for premise => law among semigroups: Theorem,
    CounterSatisfiable or another, such as Timeout."""
    problem = tptp_problem([ASSOCIATIVITY, equation(premise)], [equation(law)])
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
        file.write(problem)
        path = Path(file.name)
    try:
        output = VampireExpert._execute(
            [vampire, "--mode", "casc", "--cores", "1", "--time_limit", str(time_limit), str(path)],
            None, time_limit + 30, None,
        )
    finally:
        path.unlink(missing_ok=True)
    for status in ("Theorem", "Unsatisfiable", "CounterSatisfiable", "Satisfiable"):
        if f"SZS status {status}" in output:
            return {"Unsatisfiable": "Theorem", "Satisfiable": "CounterSatisfiable"}.get(status, status)
    return "Unknown"


def countermodel(table: Sequence[Sequence[int]] | None, premise: Law, law: Law, name: str) -> Magma | None:
    """The semigroup of the table, if it satisfies the premise and violates
    the law; a table that does not is an error of the prover."""
    if table is None:
        return None
    evaluator = Evaluator(table, budget=10 ** 8)
    magma = Magma(len(table), tuple(tuple(row) for row in table), name=name)
    if not magma.holds(ASSOCIATIVITY) or evaluator.holds(premise) is False or evaluator.holds(law) is not False:
        raise ValueError(f"{name} is no countermodel to {text(premise)} => {text(law)}")
    return magma


def mace4_model(mace4: str, premise: Law, law: Law, time_limit: int, max_size: int = 100) -> Magma | None:
    """A semigroup satisfying the premise and violating the law, by Mace4
    from two elements up, or None."""
    problem = ladr_problem([ASSOCIATIVITY, equation(premise)], equation(law))
    # Without -N, Mace4 searches the size of -n only.
    command = [mace4, "-n", "2", "-N", str(max_size), "-t", str(time_limit)]
    output = VampireExpert._execute(command, problem, time_limit + 30, None)
    table = parse_mace4_model(output)
    return countermodel(table, premise, law, f"Mace4-{len(table)}") if table else None


def equivalence(status: Callable[[Law, Law], str], a: Law, b: Law) -> bool | None:
    """True if both implications are proved, False if one is refuted, None
    otherwise."""
    forward = status(a, b)
    if forward == "CounterSatisfiable":
        return False
    backward = status(b, a)
    if backward == "CounterSatisfiable":
        return False
    return True if forward == backward == "Theorem" else None


def classes(
        laws: Sequence[Law],
        rows: Sequence[Sequence[bool | None]],
        status: Callable[[Law, Law], str],
        workers: int = 1,
        report: Callable[[str], None] = lambda line: None,
) -> tuple[list[list[Law]], list[tuple[Law, Law]]]:
    """The classes of laws proved equivalent, each smallest law first, and
    the pairs of a representative and a law neither proved equivalent to it
    nor refuted.

    `rows` gives the values of the laws on each of a set of semigroups, None
    where unknown: laws with different known values are not compared.
    """
    known = [k for k, row in enumerate(rows) if None not in row]
    groups: dict[tuple, list[int]] = {}
    for i in range(len(laws)):
        groups.setdefault(tuple(rows[k][i] for k in known), []).append(i)

    def separated(i: int, j: int) -> bool:
        return any(row[i] is not None and row[j] is not None and row[i] != row[j] for row in rows)

    found: list[list[Law]] = []
    unresolved: list[tuple[Law, Law]] = []
    with ThreadPoolExecutor(workers) as pool:
        for number, group in enumerate(sorted(groups.values(), key=len, reverse=True), start=1):
            left = sorted(group, key=lambda i: sort_key(laws[i]))
            while left:
                head, rest = left[0], [i for i in left[1:] if not separated(left[0], i)]
                answers = dict(zip(rest, pool.map(lambda i: equivalence(status, laws[head], laws[i]), rest)))
                members = [head] + [i for i in rest if answers[i]]
                found.append([laws[i] for i in members])
                unresolved += [(laws[head], laws[i]) for i in rest if answers[i] is None]
                left = [i for i in left if i not in set(members)]
            if len(group) > 1:
                report(f"group {number} of {len(groups)}: {len(group)} laws, {len(found)} classes so far")
    return sorted(found, key=lambda members: sort_key(members[0])), unresolved


def settle(
        representatives: Sequence[Law],
        pairs: Sequence[tuple[int, int]],
        rows: Sequence[Sequence[bool | None]],
        refute: Callable[[Law, Law], Magma | None],
        prove: Callable[[Law, Law], str],
        workers: int = 1,
        report: Callable[[str], None] = lambda line: None,
) -> tuple[list[tuple[int, int]], list[Magma], list[tuple[int, int]]]:
    """The second pass: of the pairs of representatives, given by their
    positions, those proved equivalent, the models found and those still
    undecided.

    `refute(a, b)` gives a countermodel to a => b or None, and `prove(a, b)`
    a status for it, as by `vampire_status`: each pair is refuted first,
    either way round, since most turn out not to be equivalent. `rows` gives
    the values of the representatives on each semigroup known, None where
    unknown.
    """
    rows = [list(row) for row in rows]
    models: list[Magma] = []
    lock = threading.Lock()

    def separated(i: int, j: int) -> bool:
        with lock:
            known = list(rows)
        return any(row[i] is not None and row[j] is not None and row[i] != row[j] for row in known)

    def decide(pair: tuple[int, int]) -> bool | None:
        i, j = pair
        for a, b in ((i, j), (j, i)):
            if separated(i, j):
                return False
            model = refute(representatives[a], representatives[b])
            if model is not None:
                evaluator = Evaluator(model.table)
                row = [evaluator.holds(law) for law in representatives]
                with lock:
                    models.append(model)
                    rows.append(row)
                return False
        statuses = []
        for a, b in ((i, j), (j, i)):
            if separated(i, j):
                return False
            statuses.append(prove(representatives[a], representatives[b]))
            if statuses[-1] == "CounterSatisfiable":
                return False
        return True if statuses == ["Theorem", "Theorem"] else (False if separated(i, j) else None)

    answers: dict[tuple[int, int], bool | None] = {}
    with ThreadPoolExecutor(workers) as pool:
        for done, (pair, answer) in enumerate(zip(pairs, pool.map(decide, pairs)), start=1):
            answers[pair] = answer
            if done % 20 == 0 or done == len(pairs):
                counts = [sum(a is value for a in answers.values()) for value in (True, False, None)]
                report(f"{done} of {len(pairs)} pairs: {counts[0]} equivalent, {counts[1]} not, {counts[2]} undecided")
    return (
        [pair for pair in pairs if answers[pair]],
        models,
        [pair for pair in pairs if answers[pair] is None],
    )


def merged(found: Sequence[Sequence[Law]], equivalent: Iterable[tuple[int, int]]) -> list[list[Law]]:
    """The classes with those of each equivalent pair, given by their
    positions, made one, each smallest law first."""
    parent = list(range(len(found)))

    def root(k: int) -> int:
        while parent[k] != k:
            k = parent[k]
        return k

    for i, j in equivalent:
        parent[root(i)] = root(j)
    unions: dict[int, list[Law]] = {}
    for k, members in enumerate(found):
        unions.setdefault(root(k), []).extend(members)
    return sorted((sorted(members, key=sort_key) for members in unions.values()), key=lambda c: sort_key(c[0]))


def exploration_inputs(classes: Sequence[Sequence[dict]], order4: Sequence[dict] = ()) -> tuple[list, list]:
    """The laws and the background implications of an exploration of the
    classes of classes.json among semigroups.

    A law of each class is taken, closed under reversal for the duality
    symmetry: a law and its reversal for a class and its dual class, and for
    a self-dual class a law that is its own reversal, or else a law and its
    reversal, given as equivalent in the background. A law the ETP lists is
    identified by its number, any other by its words, and associativity,
    the ETP's Eq4512, is added for the exploration to assume.

    The background is the implications of `order4`, an exploration's
    implications.json on laws the ETP numbers, which must all hold, each law
    replaced by the law taken from its class, and their duals.
    """
    found = [[parse_law(entry["law"]) for entry in members] for members in classes]
    number = {parse_law(e["law"]): e["etp"] for members in classes for e in members if "etp" in e}
    position = {law: k for k, members in enumerate(found) for law in members}
    chosen: dict[int, list[Law]] = {}
    for k, members in enumerate(found):
        if k in chosen:
            continue
        law = members[0]
        dual = position[reversal(law)]
        if dual != k:
            chosen[k], chosen[dual] = [law], [reversal(law)]
        else:
            chosen[k] = [m for m in members if reversal(m) == m][:1] or [law, reversal(law)]

    ident = lambda law: number.get(law, text(law))
    entries = [
        {**({"id": number[law]} if law in number else {"name": text(law)}),
         "equation": str(equation(law)), "class": [text(m) for m in found[k]]}
        for k in sorted(chosen) for law in chosen[k]
    ]
    entries.append({"id": ASSOCIATIVITY_NUMBER, "equation": str(ASSOCIATIVITY), "class": []})

    background: dict[tuple, dict] = {}

    def add(premise: Iterable, conclusion: Iterable) -> None:
        premise = sorted(set(premise), key=str)
        conclusion = sorted(set(conclusion) - set(premise), key=str)
        if conclusion:
            background.setdefault((tuple(premise), tuple(conclusion)), {"premise": premise, "conclusion": conclusion})

    for laws_of_class in chosen.values():
        if len(laws_of_class) == 2:
            a, b = map(ident, laws_of_class)
            add([a], [b])
            add([b], [a])
    of_number = {n: position[law] for law, n in number.items()}
    for image in (lambda k: k, lambda k: position[reversal(found[k][0])]):
        side = lambda numbers: [
            n if n == ASSOCIATIVITY_NUMBER else ident(chosen[image(of_number[n])][0]) for n in numbers
        ]
        for implication in order4:
            add(side(implication["premise"]), side(implication["conclusion"]))
    return entries, list(background.values())


TRIVIAL: Law = ((0,), (0,))
COMMUTATIVITY = Equation.parse("x * y = y * x")
COMMUTATIVITY_NUMBER = 43  # in the ETP's equations.txt


def commutative_form(law: Law) -> Law:
    """The form of the law among commutative semigroups, where a word is
    determined by how often each variable occurs in it: each side sorted,
    the variables renamed to make the smallest pair, and x = x for a law
    whose sides become equal."""
    u, v = law
    if sorted(u) == sorted(v):
        return TRIVIAL
    forms = []
    for p in permutations(range(variables(law))):
        a, b = tuple(sorted(p[c] for c in u)), tuple(sorted(p[c] for c in v))
        forms.append(min((a, b), (b, a)))
    return min(forms)


def monomial_semigroup(
        generators: int,
        allowed: Callable[[tuple[int, ...]], bool],
        name: str,
        max_size: int | None = None,
) -> Magma | None:
    """The Rees quotient of the free commutative semigroup on `generators`
    generators by the ideal of the monomials not allowed: the allowed
    nonzero exponent vectors, a finite downward-closed set, multiplied by
    adding them, and a zero for every product not allowed.

    Such semigroups refute laws whose smallest countermodels are too big
    to search for: square-free monomials over five generators, with 32
    elements, satisfy x^2 = y^2 z w u (both sides are always 0) but not
    x^2 = x y z w u, and no smaller commutative semigroup does. The
    generators are numbered first, so that a search over the assignments
    of the variables meets distinct generators early. None if there would
    be more than `max_size` elements.
    """
    vectors, frontier = [], [tuple(int(i == k) for i in range(generators)) for k in range(generators)]
    seen = set(frontier)
    while frontier:
        vectors += [v for v in frontier if allowed(v)]
        if max_size is not None and len(vectors) + 1 > max_size:
            return None
        grown = [tuple(e + (i == k) for i, e in enumerate(v)) for v in frontier if allowed(v) for k in range(generators)]
        frontier = [v for v in dict.fromkeys(grown) if v not in seen]
        seen.update(frontier)
    vectors.sort(key=lambda v: (sum(v), [-e for e in v]))
    index = {v: k for k, v in enumerate(vectors)}
    zero = len(vectors)
    table = tuple(
        tuple(index.get(tuple(a + b for a, b in zip(v, w)), zero) if v is not None and w is not None else zero
              for w in vectors + [None])
        for v in vectors + [None]
    )
    return Magma(zero + 1, table, name=name)


def monomial_semigroups(max_size: int = 32) -> list[Magma]:
    """Monomial semigroups of at most `max_size` elements, by
    `monomial_semigroup`: the monomials over n generators that are
    square-free, have every exponent below e, have degree at most d, or are
    square-free of degree at most d."""
    families = []
    for n in range(1, 7):
        families.append((n, lambda v: max(v) < 2, f"square-free on {n}"))
        for e in range(3, 9):
            families.append((n, lambda v, e=e: max(v) < e, f"exponents below {e} on {n}"))
        for d in range(2, 9):
            families.append((n, lambda v, d=d: sum(v) <= d, f"degree at most {d} on {n}"))
            families.append((n, lambda v, d=d: max(v) < 2 and sum(v) <= d, f"square-free of degree at most {d} on {n}"))
    found: dict[tuple, Magma] = {}
    for n, allowed, name in families:
        magma = monomial_semigroup(n, allowed, f"Monomials, {name}", max_size)
        if magma is not None:
            found.setdefault(magma.table, magma)
    return list(found.values())


def commutative_inputs(
        max_order: int,
        order4_laws: Sequence[dict],
        order4: Sequence[dict],
        etp: EtpLaws,
) -> tuple[list, list]:
    """The laws and the background implications of an exploration of the
    laws of order at most `max_order` among commutative semigroups.

    The laws of order at most 4 are those of an exploration of semigroup
    laws, `order4_laws` with their ETP classes as in equations_semigroup.json
    and `order4` its implications.json, all of which must hold. Laws
    equivalent among semigroups stay equivalent among commutative
    semigroups, so of the laws of order at most 4 one is taken for each
    class of laws equivalent there or equal in commutative form, and the
    implications are mapped onto them. The laws of higher order are all
    taken, without background. Laws are given by their ETP number where
    the ETP lists them, and associativity and commutativity (Eq4512 and
    Eq43) are added for the exploration to assume.
    """
    attribute_of = {member: entry["id"] for entry in order4_laws for member in entry["class"]}
    attributes = {entry["id"] for entry in order4_laws}
    implications = [(set(i["premise"]), set(i["conclusion"])) for i in order4]

    def closure(start: set) -> frozenset:
        closed, grown = set(start), True
        while grown:
            grown = False
            for premise, conclusion in implications:
                if premise <= closed and not conclusion <= closed:
                    closed |= conclusion
                    grown = True
        return frozenset(closed & attributes)

    # Union-find over commutative forms: forms of laws equivalent among
    # semigroups are one class.
    parent: dict[Law, Law] = {}

    def root(form: Law) -> Law:
        parent.setdefault(form, form)
        while parent[form] != form:
            form = parent[form]
        return form

    by_theory: dict[frozenset, Law] = {}
    for law in laws(min(max_order, 4)):
        form = commutative_form(law)
        theory = closure({attribute_of[etp.id_of(equation(law))]})
        first = by_theory.setdefault(theory, form)
        a, b = root(first), root(form)
        if a != b:
            # The smaller form represents the class.
            parent[max(a, b, key=sort_key)] = min(a, b, key=sort_key)
    chosen = sorted({root(form) for form in parent}, key=sort_key)
    chosen += sorted({commutative_form(law) for law in laws(max_order) if order(law) > 4} - {TRIVIAL}, key=sort_key)

    ident = lambda form: etp.id_of(equation(form)) or text(form)
    entries = [
        {**({"id": ident(form)} if isinstance(ident(form), int) else {"name": text(form)}), "equation": str(equation(form))}
        for form in chosen
    ]
    entries += [
        {"id": ASSOCIATIVITY_NUMBER, "equation": str(ASSOCIATIVITY)},
        {"id": COMMUTATIVITY_NUMBER, "equation": str(COMMUTATIVITY)},
    ]
    law_of_attribute = {entry["id"]: law_of(Equation.parse(entry["equation"])) for entry in order4_laws}
    mapped = lambda n: n if n == ASSOCIATIVITY_NUMBER else ident(root(commutative_form(law_of_attribute[n])))
    background: dict[tuple, dict] = {}
    for implication in order4:
        premise = sorted({mapped(n) for n in implication["premise"]}, key=str)
        conclusion = sorted({mapped(n) for n in implication["conclusion"]} - set(premise), key=str)
        if conclusion:
            background.setdefault((tuple(premise), tuple(conclusion)), {"premise": premise, "conclusion": conclusion})
    return entries, list(background.values())


def write_inputs(args: argparse.Namespace) -> None:
    data = json.loads(args.classes.read_text())
    order4 = json.loads(args.order4.read_text()) if args.order4 else []
    entries, background = exploration_inputs(data["classes"], order4)
    write = lambda kind, value: (args.directory / f"{kind}_{args.prefix}.json").write_text(
        "[\n" + ",\n".join(json.dumps(item) for item in value) + "\n]\n"
    )
    write("equations", entries)
    write("background", background)
    write("seeds", data["semigroups"])
    print(f"{len(entries)} laws, {len(background)} background implications, {len(data['semigroups'])} seeds")


def write_commutative_inputs(args: argparse.Namespace) -> None:
    entries, background = commutative_inputs(
        args.max_order,
        json.loads(args.order4_equations.read_text()),
        json.loads(args.order4.read_text()),
        EtpLaws.load(args.etp_equations),
    )
    seeds = [
        {"name": m.name, "size": m.size, "table": [list(row) for row in m.table]}
        for m in small_semigroups(args.small_size, commutative=True) + monomial_semigroups(args.monomial_size)
    ]
    write = lambda kind, value: (args.directory / f"{kind}_{args.prefix}.json").write_text(
        "[\n" + ",\n".join(json.dumps(item) for item in value) + "\n]\n"
    )
    write("equations", entries)
    write("background", background)
    write("seeds", seeds)
    print(f"{len(entries)} laws, {len(background)} background implications, {len(seeds)} seeds")


def main(argv: Sequence[str] | None = None) -> None:
    root = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = root.add_subparsers(dest="command", required=True)
    inputs = commands.add_parser("inputs", help="Write the input of an exploration of the classes.")
    inputs.add_argument("classes", type=Path)
    inputs.add_argument("--order4", type=Path, help="An exploration's implications.json on laws of order 4.")
    inputs.add_argument("--prefix", default="semigroup5")
    inputs.add_argument("--directory", type=Path, default=Path(__file__).parent)
    commutative = commands.add_parser(
        "commutative-inputs", help="Write the input of an exploration of commutative semigroups."
    )
    commutative.add_argument("--max-order", type=int, default=5)
    commutative.add_argument("--order4-equations", type=Path, required=True, help="As equations_semigroup.json.")
    commutative.add_argument("--order4", type=Path, required=True, help="Its exploration's implications.json.")
    commutative.add_argument("--etp-equations", type=Path, required=True)
    commutative.add_argument("--small-size", type=int, default=5, help="Seed with the commutative semigroups up to this size.")
    commutative.add_argument(
        "--monomial-size", type=int, default=32, help="Seed with the monomial semigroups up to this size."
    )
    commutative.add_argument("--prefix", default="csemigroup5")
    commutative.add_argument("--directory", type=Path, default=Path(__file__).parent)
    parser = commands.add_parser("classes", help="Sort the laws into classes.")
    parser.add_argument("results_dir", type=Path)
    parser.add_argument("--max-order", type=int, default=5)
    parser.add_argument("--small-size", type=int, default=4, help="Enumerate the semigroups up to this size.")
    parser.add_argument("--seeds", type=Path, nargs="*", default=[], help="Files of further magmas (JSON).")
    parser.add_argument("--budget", type=int, default=2 ** 21, help="Most assignments evaluated per law and magma.")
    parser.add_argument("--time-limit", type=float, default=10, help="Seconds per Vampire proof.")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--etp-equations", type=Path, help="Number the laws the ETP lists by its numbers.")
    parser.add_argument("--second-vampire-time-limit", type=int, default=30, help="Seconds per Vampire run, second pass.")
    parser.add_argument("--second-mace4-time-limit", type=int, default=30, help="Seconds per Mace4 run, second pass.")
    parser.add_argument("--from-classes", type=Path, help="Run the second pass on the classes of this file.")
    args = root.parse_args(argv)
    if args.command == "inputs":
        write_inputs(args)
        return
    if args.command == "commutative-inputs":
        write_commutative_inputs(args)
        return

    vampire, mace4 = shutil.which("vampire"), shutil.which("mace4")
    if vampire is None or mace4 is None:
        raise FileNotFoundError("Vampire and Mace4 are needed")
    start = time.monotonic()
    log = lambda line: print(f"[{time.monotonic() - start:7.0f} s] {line}", flush=True)
    every = laws(args.max_order)
    log(f"{len(every)} laws of order at most {args.max_order}")

    if args.from_classes is not None:
        earlier = json.loads(args.from_classes.read_text())
        semigroups = [
            Magma(m["size"], tuple(map(tuple, m["table"])), name=m["name"]) for m in earlier["semigroups"]
        ]
        found = [[parse_law(entry["law"]) for entry in members] for members in earlier["classes"]]
        unresolved = [(parse_law(a), parse_law(b)) for a, b in earlier["unresolved"]]
        first = earlier.get("first_pass", {"classes": len(found), "unresolved": len(unresolved)})
        log(f"{len(found)} classes, {len(unresolved)} pairs unresolved, from {args.from_classes}")
    else:
        semigroups, found, unresolved = first_pass(args, every, vampire, log)
        first = {"classes": len(found), "unresolved": len(unresolved)}

    position = {law: k for k, members in enumerate(found) for law in members}
    pairs = sorted({tuple(sorted((position[a], position[b]))) for a, b in unresolved} - {(k, k) for k in range(len(found))})
    representatives = [members[0] for members in found]
    rows = evaluate(semigroups, representatives, args.budget, args.workers)

    log(f"second pass on {len(pairs)} pairs of classes")
    equivalent, models, undecided = settle(
        representatives, pairs, rows,
        lambda a, b: mace4_model(mace4, a, b, args.second_mace4_time_limit),
        lambda a, b: vampire_status(vampire, a, b, args.second_vampire_time_limit),
        args.workers, log,
    )
    found = merged(found, equivalent)
    semigroups += models
    unresolved = [(representatives[i], representatives[j]) for i, j in undecided]
    log(f"{len(found)} classes, {len(unresolved)} pairs undecided, {len(models)} models found")

    numbers = {}
    if args.etp_equations is not None:
        etp = EtpLaws.load(args.etp_equations)
        numbers = {law: etp.id_of(equation(law)) for law in every}
    entry = lambda law: {"law": text(law), "order": order(law), **({"etp": numbers[law]} if numbers.get(law) else {})}
    args.results_dir.mkdir(parents=True, exist_ok=True)
    (args.results_dir / "classes.json").write_text(json.dumps({
        "max_order": args.max_order,
        "laws": len(every),
        "first_pass": first,
        "semigroups": [{"name": m.name, "size": m.size, "table": [list(r) for r in m.table]} for m in semigroups],
        "classes": [[entry(law) for law in members] for members in found],
        "unresolved": [[text(a), text(b)] for a, b in unresolved],
    }, indent=1))
    log(f"wrote {args.results_dir / 'classes.json'}")


def first_pass(args: argparse.Namespace, every: Sequence[Law], vampire: str, log: Callable[[str], None]) -> tuple:
    """The semigroups, the classes and the unresolved pairs of the first pass."""
    semigroups = small_semigroups(args.small_size)
    log(f"{len(semigroups)} semigroups of at most {args.small_size} elements, up to isomorphism")
    tables = {m.table for m in semigroups}
    for path in args.seeds:
        for magma in ETP.load_magmas(path):
            if not magma.holds(ASSOCIATIVITY):
                continue
            for m in (magma, magma.dual()):
                # Relabelling bigger tables takes too long; a duplicate is harmless.
                form = isomorphism_form(m.table) if m.size <= 6 else m.table
                if form not in tables:
                    tables.add(form)
                    semigroups.append(Magma(m.size, form, name=m.name))
    log(f"{len(semigroups)} semigroups with the seeds and their duals")

    rows = evaluate(semigroups, every, args.budget, args.workers)
    unknown = sum(value is None for row in rows for value in row)
    log(f"evaluated, {unknown} values unknown")

    found, unresolved = classes(
        every, rows, lambda a, b: vampire_status(vampire, a, b, args.time_limit), args.workers, log
    )
    log(f"{len(found)} classes, {len(unresolved)} pairs unresolved")
    return semigroups, found, unresolved


if __name__ == "__main__":
    main()
