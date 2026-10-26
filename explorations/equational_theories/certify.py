"""Proof certificates (certificates.py) from Vampire's proofs.

Vampire proves a law from premise laws by refutation, its proof a list of
clauses each inferred from earlier ones. For unit equations every inference
is an equational step that `certificate_from_tstp` redoes, so as to write out
the terms the checker needs: an equation inferred by superposition becomes a
lemma proved by a chain of two steps through the overlapping term, found
again by unification; one inferred by demodulation, a chain of one step; and
the negated conclusion, rewritten until its two sides are equal or an
instance of an equation, becomes the chain of the conclusion. A conclusion
of several laws gives a certificate for each: AVATAR splits its negation
into a branch for each law, refuted separately, and without AVATAR a law's
literal is removed from the negated conclusion when it is refuted. Inequality
splitting, which turns s != t into ~sP(s) and sP(t), is followed as well:
the chains of s and t end where the two meet. The constants
of the definitions casc mode introduces are expanded at the end, and the Skolem
constants of the conclusion turned back into its variables.

The prover is not trusted: a certificate is checked by certificates.py, and
one that cannot be reconstructed or checked is no evidence.

usage: certify.py RESULTS_DIR -o CERTIFICATES [--classes] [--proofs PROOFS]

certifies single-law implications that, with the exploration's axioms,
entail every implication of RESULTS_DIR/implications.json (see `cover`), and
with --classes the equivalence of each law of the equations file with the
other laws of its class; verify.py checks the result with them. The proofs
the exploration saved (RESULTS_DIR/proofs.jsonl.xz, or PROOFS) are used
first, an implication being certified by a proof from fewer premise laws or
by the mirror image of a proof of its dual; Vampire is run for the rest.
"""

from __future__ import annotations

import argparse
import itertools
import json
import lzma
import re
import subprocess
import sys
import tempfile
import time
import tomllib
from collections.abc import Sequence
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.certificates import (
    CertificateError, check_certificate, parse_law, parse_term, show, word_law,
)
from explorations.equational_theories.verify import law_key


class ReconstructionError(ValueError):
    pass


# TSTP terms and formulas: a variable is a name starting in upper case, a
# constant one in lower case, and m(s,t) the product.

def _is_variable(term) -> bool:
    return isinstance(term, str) and term[0].isupper()


def _tptp(term) -> str:
    return "V" + term if isinstance(term, str) else f"m({_tptp(term[0])},{_tptp(term[1])})"


def tptp_problem(premise: Sequence[str], law: str) -> str:
    """The premise as axioms h0, h1, ... and the law as the conjecture."""
    def formula(text: str) -> str:
        lhs, rhs = parse_law(text)
        variables = sorted(_variables(lhs) | _variables(rhs))
        body = f"{_tptp(lhs)} = {_tptp(rhs)}"
        return f"![{','.join('V' + v for v in variables)}]: {body}" if variables else body
    lines = [f"fof(h{k}, axiom, {formula(p)})." for k, p in enumerate(premise)]
    lines.append(f"fof(goal, conjecture, {formula(law)}).")
    return "\n".join(lines) + "\n"


def _variables(term) -> set[str]:
    return {term} if isinstance(term, str) else _variables(term[0]) | _variables(term[1])


_TSTP_TOKEN = re.compile(r"\s*(\$false|\$true|!=|[A-Za-z_][A-Za-z0-9_]*|[()\[\],:=~!?&|])")


def _parse_formula(text: str):
    tokens = _TSTP_TOKEN.findall(text)
    position = 0

    def peek():
        return tokens[position] if position < len(tokens) else None

    def take(expected=None):
        nonlocal position
        if position == len(tokens):
            raise ReconstructionError(f"Unexpected end of {text!r}")
        token = tokens[position]
        if expected is not None and token != expected:
            raise ReconstructionError(f"Expected {expected} in {text!r}")
        position += 1
        return token

    def term():
        name = take()
        if peek() == "(":
            take("(")
            left = term()
            take(",")
            right = term()
            take(")")
            if name != "m":
                raise ReconstructionError(f"Unknown function {name} in {text!r}")
            return (left, right)
        return name

    def formula():
        token = peek()
        if token == "~":
            take()
            return ("not", formula())
        if token in ("!", "?"):
            take()
            take("[")
            while take() != "]":
                pass
            take(":")
            return ("all" if token == "!" else "some", formula())
        if token == "(":
            take("(")
            inner = formula()
            take(")")
            if peek() in ("|", "&"):
                raise ReconstructionError(f"Not a unit clause: {text!r}")
            return inner
        if token == "$false":
            take()
            return ("false",)
        if re.fullmatch(r"sP\d+", token or "") and position + 1 < len(tokens) and tokens[position + 1] == "(":
            # sP(t), of Vampire's inequality splitting
            name = take()
            take("(")
            argument = term()
            take(")")
            return ("pred", name, argument)
        left = term()
        relation = take()
        right = term()
        if relation not in ("=", "!="):
            raise ReconstructionError(f"Unknown relation {relation} in {text!r}")
        return ("eq" if relation == "=" else "neq", left, right)

    result = formula()
    if position != len(tokens):
        raise ReconstructionError(f"Not a unit clause: {text!r}")
    return result


def _proof_steps(output: str) -> list[tuple[str, str, str, str]]:
    """The proof's entries: name, role, formula and annotation."""
    start, end = output.find("SZS output start"), output.find("SZS output end")
    if start < 0 or end < 0:
        raise ReconstructionError("No proof in the output")
    body = output[output.index("\n", start) + 1:end]
    steps = []
    for entry in re.split(r"\n(?=fof\(|cnf\()", body.strip()):
        entry = " ".join(line.strip() for line in entry.splitlines() if not line.startswith("%"))
        match = re.match(r"(?:fof|cnf)\((\w+),(\w+),(.*)\)\.\s*$", entry)
        if match is None:
            continue
        name, role, rest = match.groups()
        # The formula ends at the comma that closes its outermost parentheses.
        depth = 0
        for i, char in enumerate(rest):
            depth += char in "(["
            depth -= char in ")]"
            if char == "," and depth == 0:
                break
        steps.append((name, role, rest[:i], rest[i + 1:]))
    return steps


def _parents(annotation: str) -> list[str]:
    match = re.search(r"\[((?:f\d+,?)+)\]\)\s*$", annotation)
    return match.group(1).split(",") if match else []


def _rule(annotation: str) -> str:
    match = re.match(r"\s*(inference|introduced|file)\((\w+)", annotation)
    return match.group(2) if match else ""


# Substitutions and unification on TSTP terms.

def _apply(term, substitution: dict):
    if isinstance(term, str):
        if term in substitution:
            return _apply(substitution[term], substitution)
        return term
    return (_apply(term[0], substitution), _apply(term[1], substitution))


def _occurs(variable: str, term, substitution: dict) -> bool:
    term = _apply(term, substitution)
    return term == variable if isinstance(term, str) else (
        _occurs(variable, term[0], substitution) or _occurs(variable, term[1], substitution))


def _unify(s, t, substitution: dict) -> bool:
    s, t = _apply(s, substitution), _apply(t, substitution)
    if s == t:
        return True
    if _is_variable(s):
        if _occurs(s, t, substitution):
            return False
        substitution[s] = t
        return True
    if _is_variable(t):
        return _unify(t, s, substitution)
    if isinstance(s, str) or isinstance(t, str):
        return False
    return _unify(s[0], t[0], substitution) and _unify(s[1], t[1], substitution)


def _match(pattern, term, substitution: dict) -> bool:
    """One-way matching of the variables of `pattern`."""
    if _is_variable(pattern):
        if pattern in substitution:
            return substitution[pattern] == term
        substitution[pattern] = term
        return True
    if isinstance(pattern, str) or isinstance(term, str):
        return pattern == term
    return _match(pattern[0], term[0], substitution) and _match(pattern[1], term[1], substitution)


def _renaming(pair, target) -> dict | None:
    """A renaming of the variables of `pair` that makes it `target`."""
    substitution: dict = {}
    if not (_match(pair[0], target[0], substitution) and _match(pair[1], target[1], substitution)):
        return None
    values = list(substitution.values())
    if not all(_is_variable(v) for v in values) or len(set(values)) != len(values):
        return None
    return substitution


def _positions(term, path=()):
    yield path, term
    if isinstance(term, tuple):
        yield from _positions(term[0], path + (0,))
        yield from _positions(term[1], path + (1,))


def _replace(term, path, new):
    if not path:
        return new
    return (_replace(term[0], path[1:], new), term[1]) if path[0] == 0 else (term[0], _replace(term[1], path[1:], new))


def _rename_apart(pair, suffix: str):
    renaming = {v: v + suffix for v in _variables(pair[0]) | _variables(pair[1]) if _is_variable(v)}
    return _apply(pair[0], renaming), _apply(pair[1], renaming)


def _occurrences(term, s, t) -> list:
    """Terms from `term` to `term` with every outermost occurrence of s
    replaced by t, one occurrence a step."""
    paths, stack = [], [((), term)]
    while stack:
        path, subterm = stack.pop()
        if subterm == s:
            paths.append(path)
        elif isinstance(subterm, tuple):
            stack += [(path + (1,), subterm[1]), (path + (0,), subterm[0])]
    terms = [term]
    for path in paths:
        terms.append(_replace(terms[-1], path, t))
    return terms


def _rewrites(source, pair, unify: bool):
    """The ways of rewriting the sides of `pair` with the equation `source`,
    in either direction: at one position, or, as Vampire's simultaneous
    superposition does, at every occurrence of the rewritten subterm. Yields
    (substitution, chains), each chain the terms from a side of the
    instantiated pair to the side of the result, one step by `source` each.
    With `unify`, the pair may be instantiated too; `source` must not share
    variables with it."""
    for lhs, rhs in (source, source[::-1]):
        for side in (0, 1):
            for path, subterm in _positions(pair[side]):
                if _is_variable(subterm):
                    continue
                substitution: dict = {}
                if not (_unify if unify else _match)(lhs, subterm, substitution):
                    continue
                instance = [_apply(pair[0], substitution), _apply(pair[1], substitution)]
                old, new = _apply(lhs, substitution), _apply(rhs, substitution)
                single = [[instance[0]], [instance[1]]]
                single[side].append(_replace(instance[side], path, new))
                yield substitution, single
                every = [_occurrences(instance[0], old, new), _occurrences(instance[1], old, new)]
                if every != single:
                    yield substitution, every


def _literals(text: str) -> list[str]:
    """The disjuncts of a formula, split at its outermost |."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for i, char in enumerate(text):
            depth += char == "("
            depth -= char == ")"
            if depth == 0:
                break
        if i != len(text) - 1:
            break
        text = text[1:-1].strip()
    parts, depth, start = [], 0, 0
    for i, char in enumerate(text):
        depth += char in "(["
        depth -= char in ")]"
        if char == "|" and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    return parts + [text[start:]]


# The AVATAR labels of the clauses of a branch, `| spl7_1`, and the
# inferences that only combine branches.
_LABEL = re.compile(r"\s*\|\s*~?spl\d+_\d+(?=\s*\)*\s*$)")
_AVATAR = ("avatar_split_clause", "avatar_contradiction_clause", "sat_conversion", "rat")


class _Proof:
    def __init__(self, premise: Sequence[str], conclusion: Sequence[str], output: str):
        self.premise = [parse_law(p) for p in premise]
        self.laws = {law: parse_law(law) for law in conclusion}
        self.lemmas: list[dict] = []
        self.lemma_pairs: list[tuple] = []
        self.equations: dict[str, tuple[tuple, str]] = {}  # name: (pair, citation)
        # name: (pair, left chain, right chain, the negated conclusion law it comes from)
        self.negatives: dict[str, tuple] = {}
        # Inequality splitting turns a literal s != t into ~sP(s) and sP(t):
        # name: (predicate, positive, chain from its side of the root, root),
        # and the definitions ~sP(s) until the splitting says which side.
        self.halves: dict[str, tuple] = {}
        self.split_names: dict[str, tuple] = {}
        self.definitions: dict[str, object] = {}
        self.steps = _proof_steps(output)
        self.annotations = {name: annotation for name, _, _, annotation in self.steps}

    def expand(self, term):
        if isinstance(term, str):
            return self.expand(self.definitions[term]) if term in self.definitions else term
        return (self.expand(term[0]), self.expand(term[1]))

    def citation_of(self, pair) -> str | None:
        """A premise or lemma of which the equation is a variant."""
        tptp_premise = [(_to_tptp(p[0]), _to_tptp(p[1])) for p in self.premise]
        for cited, known in [(f"h{k}", p) for k, p in enumerate(tptp_premise)] + \
                [(f"l{k}", p) for k, p in enumerate(self.lemma_pairs)]:
            if _renaming(known, pair) is not None or _renaming(known[::-1], pair) is not None:
                return cited
        return None

    def add_lemma(self, pair, terms: list, by: list) -> str:
        self.lemmas.append((terms, by))
        self.lemma_pairs.append(pair)
        return f"l{len(self.lemmas) - 1}"

    def expanded(self, terms: list, by: list, rename=lambda term: term) -> dict:
        """A chain with the definitions expanded, without the steps that
        this makes trivial: those through definitions, among others."""
        terms = [rename(self.expand(t)) for t in terms]
        kept_terms, kept_by = terms[:1], []
        for cite, term in zip(by, terms[1:]):
            if term == kept_terms[-1]:
                continue
            if cite is None:
                raise ReconstructionError("A step left without a citation")
            kept_terms.append(term)
            kept_by.append(cite)
        return {"terms": [show(_from_tptp(t)) for t in kept_terms], "by": kept_by}

    def justify_equation(self, pair, parents: list[str]) -> str:
        cited = self.citation_of(pair)
        if cited is not None:
            return cited
        if self.expand(pair[0]) == self.expand(pair[1]):
            return self.add_lemma(pair, [pair[0], pair[1]], [None])
        sources = [self.equations[p] for p in parents if p in self.equations]
        # One step from the equation's left side to its right side.
        for source, citation in sources:
            for _, (left, right) in _rewrites(_rename_apart(source, "_s"), (pair[0], pair[0]), unify=False):
                if len(left) == 1 and right[-1] == pair[1]:
                    return self.add_lemma(pair, [pair[0], pair[1]], [citation])
        # Superposition: from the result back to the instance of the clause
        # rewritten, by the clause to its other side, and on to the result.
        for (into, into_cite), (source, source_cite) in itertools.permutations(
                sources + sources[:1] * (len(sources) == 1), 2):
            for _, (left, right) in _rewrites(_rename_apart(source, "_s"), _rename_apart(into, "_i"), unify=True):
                candidate = (left[-1], right[-1])
                for target in (pair, pair[::-1]):
                    renaming = _renaming(candidate, target)
                    if renaming is None:
                        continue
                    terms = [_rename(t, renaming) for t in left[::-1] + right]
                    by = [source_cite] * (len(left) - 1) + [into_cite] + [source_cite] * (len(right) - 1)
                    if target is not pair:
                        terms, by = terms[::-1], by[::-1]
                    return self.add_lemma(pair, terms, by)
        raise ReconstructionError(f"Cannot justify {show(pair[0])} = {show(pair[1])} from {parents}")

    def justify_negative(self, pairs: list, parents: list[str]) -> tuple[list, list]:
        """The literals of a negative clause, each (pair, left chain, right
        chain, root), the chains (terms, citations) from the sides of the
        negated conclusion law it comes from, its root; and the literals of
        the parent clause that the inference removed."""
        negative = [self.negatives[p] for p in parents if p in self.negatives]
        sources = [self.equations[p] for p in parents if p in self.equations]
        if not negative:
            return [(pair, ([pair[0]], []), ([pair[1]], []), pair) for pair in pairs], []
        if len(negative) != 1:
            raise ReconstructionError("An inference from two negative clauses")
        remaining, literals = list(negative[0]), [None] * len(pairs)
        # The literals carried over first, then those rewritten.
        for rewrite in (False, True):
            for k, pair in enumerate(pairs):
                for literal in remaining if literals[k] is None else []:
                    literals[k] = self.carried(literal, pair, sources if rewrite else None)
                    if literals[k] is not None:
                        remaining.remove(literal)
                        break
        if None in literals:
            raise ReconstructionError(f"Cannot justify a literal of {pairs} from {parents}")
        return literals, remaining

    def carried(self, literal, pair, sources):
        """The literal `pair` from the parent's `literal`: the same up to
        definitions, or, with `sources`, rewritten by one of them."""
        old, left, right, root = literal
        if sources is None:
            for target, swapped in ((pair, False), (pair[::-1], True)):
                if tuple(map(self.expand, old)) == tuple(map(self.expand, target)):
                    new = [(left[0] + [target[0]], left[1] + [None]), (right[0] + [target[1]], right[1] + [None])]
                    return (pair, *((new[0], new[1]) if not swapped else (new[1], new[0])), root)
            return None
        for source, citation in sources:
            for substitution, chains in _rewrites(_rename_apart(source, "_s"), old, unify=True):
                candidate = (chains[0][-1], chains[1][-1])
                for target, swapped in ((pair, False), (pair[::-1], True)):
                    renaming = _renaming(candidate, target)
                    if renaming is None:
                        continue
                    new = [([_rename(_apply(t, substitution), renaming) for t in chain[0]]
                            + [_rename(t, renaming) for t in steps[1:]],
                            chain[1] + [citation] * (len(steps) - 1))
                           for chain, steps in ((left, chains[0]), (right, chains[1]))]
                    return (pair, *((new[0], new[1]) if not swapped else (new[1], new[0])), root)
        return None

    def close(self, literal, parents: list[str]) -> tuple[str, dict]:
        """The law and its certificate, from an inference that removes a
        literal: its sides are equal, or an instance of an equation."""
        sources = [self.equations[p] for p in parents if p in self.equations]
        pair, left, right, root = literal
        substitution: dict = {}
        if _unify(pair[0], pair[1], substitution):
            middle: tuple[list, list] = ([], [])
        else:
            for (source, citation), (lhs, rhs) in ((s, o) for s in sources for o in (s[0], s[0][::-1])):
                lhs, rhs = _rename_apart((lhs, rhs), "_s")
                substitution = {}
                if _unify(lhs, pair[0], substitution) and _unify(rhs, pair[1], substitution):
                    middle = ([_apply(pair[1], substitution)], [citation])
                    break
            else:
                raise ReconstructionError("Cannot reconstruct the refutation")
        left_terms = [_apply(t, substitution) for t in left[0]]
        right_terms = [_apply(t, substitution) for t in right[0]]
        terms = left_terms + middle[0] + right_terms[::-1][1:] if middle[0] else left_terms + right_terms[::-1][1:]
        by = left[1] + middle[1] + right[1][::-1]
        return self.certificate(terms, by, root)

    def half(self, name: str, positive: bool, atom, rule: str, parents: list[str]) -> None:
        """A literal sP(t) or ~sP(t) of inequality splitting: from the
        negative literal it splits, or rewritten from another."""
        _, predicate, argument = atom
        expand = self.expand
        if rule == "inequality_splitting":
            literals = [self.negatives[p] for p in parents if p in self.negatives]
            named = [p for p in parents if p in self.split_names]
            if len(literals) != 1 or len(literals[0]) != 1 or len(named) != 1:
                raise ReconstructionError("Cannot split the inequality")
            ((literal,),), (named,) = literals, named
            pair, left, right, root = literal
            given = self.split_names[named][2]
            for side, other, chains in ((0, 1, (left, right)), (1, 0, (right, left))):
                if expand(given) == expand(pair[side]) and expand(argument) == expand(pair[other]):
                    self.halves[named] = (predicate, False, (chains[0][0] + [given], chains[0][1] + [None]), root)
                    self.halves[name] = (predicate, True, (chains[1][0] + [argument], chains[1][1] + [None]), root)
                    return
            raise ReconstructionError("Cannot split the inequality")
        halves = [self.halves[p] for p in parents if p in self.halves]
        if len(halves) != 1:
            raise ReconstructionError(f"Cannot justify {predicate}({show(argument)}) from {parents}")
        _, _, (terms, by), root = halves[0]
        if expand(terms[-1]) == expand(argument):
            self.halves[name] = (predicate, positive, (terms + [argument], by + [None]), root)
            return
        for source, citation in [self.equations[p] for p in parents if p in self.equations]:
            for substitution, chains in _rewrites(_rename_apart(source, "_s"), (terms[-1], "c_"), unify=True):
                if chains[1] != ["c_"] or chains[0][-1] != argument:
                    continue
                self.halves[name] = (predicate, positive,
                                     ([_apply(t, substitution) for t in terms] + chains[0][1:],
                                      by + [citation] * (len(chains[0]) - 1)), root)
                return
        raise ReconstructionError(f"Cannot justify {predicate}({show(argument)}) from {parents}")

    def meet(self, parents: list[str]) -> tuple[str, dict]:
        """The law and its certificate, from ~sP(s) and sP(t) with s and t
        the same."""
        halves = {positive: (terms, by, root) for predicate, positive, (terms, by), root
                  in (self.halves[p] for p in parents if p in self.halves)}
        if set(halves) != {False, True}:
            raise ReconstructionError("The refutation does not use both halves of an inequality")
        (left, left_by, root), (right, right_by, _) = halves[False], halves[True]
        if self.expand(left[-1]) != self.expand(right[-1]):
            raise ReconstructionError("The halves of the inequality do not meet")
        return self.certificate(left + right[::-1][1:], left_by + right_by[::-1], root)

    def negative(self, name: str, pairs: list, parents: list[str], proved: list) -> None:
        """A negative clause, and the laws of the literals its inference
        removed from its parent, by subsumption or equality resolution."""
        self.negatives[name], removed = self.justify_negative(pairs, parents)
        for literal in removed:
            try:
                proved.append(self.close(literal, parents))
            except ReconstructionError:
                pass  # removed for another reason: its law is not proved here

    def certificate(self, terms: list, by: list[str], root) -> tuple[str, dict]:
        # The chains of a negative clause follow its sides, which Vampire
        # may have swapped: the chain runs between the root's sides, either way.
        if terms[0] != root[0]:
            terms, by = terms[::-1], by[::-1]
        if (terms[0], terms[-1]) != root:
            raise ReconstructionError("The chain does not join the sides of the negated conclusion")
        # The Skolem constants of the conclusion back to its variables, and
        # other variables left in the chain to fresh ones. The root may be
        # written with the constants of definitions.
        expanded = (self.expand(root[0]), self.expand(root[1]))
        for (text, (lhs, rhs)), (target, swapped) in itertools.product(
                self.laws.items(), [(expanded, False), (expanded[::-1], True)]):
            substitution: dict = {}
            if (_match(_to_tptp(lhs), target[0], substitution) and _match(_to_tptp(rhs), target[1], substitution)
                    and all(isinstance(value, str) for value in substitution.values())):
                break
        else:
            raise ReconstructionError("The negated conclusion is not the conclusion's")
        back = {constant: variable for variable, constant in substitution.items()}
        if len(back) != len(substitution):
            raise ReconstructionError("Two variables of the conclusion share a Skolem constant")
        if swapped:
            terms, by = terms[::-1], by[::-1]
        return text, _pruned([self.expanded(t, b) for t, b in self.lemmas],
                             self.expanded(terms, by, lambda term: _rename(term, back)))

    def run(self) -> list[tuple[str, dict]]:
        """The laws proved, each with its certificate's lemmas and chain. A
        step that cannot be redone loses only what depends on it: with
        AVATAR, the other branches' laws are still proved."""
        proved: list[tuple[str, dict]] = []
        failed: set[str] = set()
        for name, role, text, annotation in self.steps:
            rule, parents = _rule(annotation), _parents(annotation)
            text, branch = _LABEL.sub("", text), _LABEL.search(text) is not None
            if rule == "avatar_sat_refutation":
                return proved
            if any(parent in failed for parent in parents):
                failed.add(name)
                continue
            try:
                if self.step(name, role, text, rule, parents, branch, proved):
                    return proved
            except ReconstructionError:
                if text.strip(" ()") == "$false" and not branch:
                    raise
                failed.add(name)
        raise ReconstructionError("The proof does not end in $false")

    def step(self, name: str, role: str, text: str, rule: str, parents: list[str], branch: bool,
             proved: list[tuple[str, dict]]) -> bool:
        """Redoes one step of the proof; whether it ends the proof."""
        if rule == "avatar_split_clause" and re.fullmatch(r"\(?\s*spl\d+_\d+\s*\)?", text.strip()):
            # A branch closed by its equation itself.
            equations = [self.equations[p] for p in parents if p in self.equations]
            if len(equations) == 1:
                (pair, citation), = equations
                proved.append(self.certificate([pair[0], pair[1]], [citation], pair))
            return False
        if rule in _AVATAR or (role == "definition" and "<=>" in text):
            return False
        if rule == "definition" or (role == "definition"):
            formula = _parse_formula(text)
            if formula[0] == "not" and formula[1][0] == "pred":
                self.split_names[name] = formula[1]
                return False
            if formula[0] != "eq" or not isinstance(formula[1], str):
                raise ReconstructionError(f"Unknown definition {text}")
            self.definitions[formula[1]] = formula[2]
            pair = (formula[1], formula[2])
            self.equations[name] = (pair, self.add_lemma(pair, [formula[1]], []))
            return False
        if role in ("conjecture", "negated_conjecture"):
            return False
        literals = _literals(text)
        if len(literals) > 1:
            # A negative clause of several laws' literals, or the conclusion
            # and its negations before clausification, which carry nothing
            # the chains need.
            try:
                formulas = [_parse_formula(literal) for literal in literals]
            except ReconstructionError:
                return False
            if any(formula[0] != "neq" for formula in formulas):
                return False
            self.negative(name, [(f[1], f[2]) for f in formulas], parents, proved)
            return False
        try:
            formula = _parse_formula(text)
        except ReconstructionError:
            if "&" in text:
                return False
            raise
        while formula[0] == "all":
            formula = formula[1]
        if role == "axiom":
            # Named as by `tptp_problem` here or in vampire.py.
            match = re.search(r"'(?:h|premise)(\d+)'\)\s*$", self.annotations[name])
            if match is None or formula[0] != "eq":
                raise ReconstructionError(f"Unknown axiom {name}")
            self.equations[name] = ((formula[1], formula[2]), f"h{match.group(1)}")
        elif formula[0] == "eq":
            pair = (formula[1], formula[2])
            self.equations[name] = (pair, self.justify_equation(pair, parents))
        elif formula[0] == "neq":
            self.negative(name, [(formula[1], formula[2])], parents, proved)
        elif formula[0] == "pred" or (formula[0] == "not" and formula[1][0] == "pred"):
            self.half(name, formula[0] == "pred", formula if formula[0] == "pred" else formula[1], rule, parents)
        elif formula[0] == "false" and any(p in self.halves for p in parents):
            proved.append(self.meet(parents))
            return not branch
        elif formula[0] == "false":
            if not any(p in self.negatives for p in parents):
                raise ReconstructionError("The refutation does not use a negative clause")
            _, removed = self.justify_negative([], parents)
            proved += [self.close(literal, parents) for literal in removed]
            return not branch
        # Other formulas (the conclusion, its negations before
        # Skolemization) carry nothing the chains need.
        return False


def _pruned(lemmas: list[dict], chain: dict) -> dict:
    """The certificate with only the lemmas its chain needs, renumbered, and
    each lemma that only restates another replaced by it."""
    alias: dict[str, str] = {}
    for k, lemma in enumerate(lemmas):
        if len(lemma["by"]) == 1:
            cited = alias.get(lemma["by"][0], lemma["by"][0])
            alias[f"l{k}"] = cited
    resolve = lambda cite: alias.get(cite, cite)
    needed, stack = set(), [resolve(c) for c in chain["by"]]
    while stack:
        cite = stack.pop()
        if cite.startswith("l") and cite not in needed:
            needed.add(cite)
            stack += [resolve(c) for c in lemmas[int(cite[1:])]["by"]]
    kept = sorted(int(c[1:]) for c in needed)
    number = {f"l{k}": f"l{i}" for i, k in enumerate(kept)}
    renumber = lambda cite: number.get(resolve(cite), resolve(cite))
    return {
        "lemmas": [{"terms": lemmas[k]["terms"], "by": [renumber(c) for c in lemmas[k]["by"]]} for k in kept],
        "terms": chain["terms"],
        "by": [renumber(c) for c in chain["by"]],
    }


def _rename(term, mapping: dict):
    """The term with its names replaced simultaneously."""
    if isinstance(term, str):
        return mapping.get(term, term)
    return (_rename(term[0], mapping), _rename(term[1], mapping))


def _to_tptp(term):
    """A certificate term in TSTP's form, its variables V-prefixed as in
    `tptp_problem`; Vampire renames them, which matching ignores."""
    return "V" + term if isinstance(term, str) else (_to_tptp(term[0]), _to_tptp(term[1]))


def _from_tptp(term):
    if isinstance(term, str):
        return term[1:] if term.startswith("V") and len(term) > 1 else term
    return (_from_tptp(term[0]), _from_tptp(term[1]))


def certificates_from_tstp(premise: Sequence[str], conclusion: Sequence[str], output: str) -> list[dict]:
    """The certificates of a Vampire proof (in TSTP, as casc mode prints it)
    of the laws of `conclusion` from those of `premise`, checked: one for
    each law the proof refutes the negation of."""
    certificates = []
    for law, chain in _Proof(premise, conclusion, output).run():
        certificate = {"premise": list(premise), "conclusion": law, **chain}
        try:
            check_certificate(certificate)
        except CertificateError as error:
            raise ReconstructionError(f"The reconstructed certificate is wrong: {error}") from error
        certificates.append(certificate)
    return certificates


def certificate_from_tstp(premise: Sequence[str], law: str, output: str) -> dict:
    """The certificate of a Vampire proof of `law` from the laws of
    `premise`, checked."""
    certificates = certificates_from_tstp(premise, [law], output)
    if not certificates:
        raise ReconstructionError("The proof proves no law")
    return certificates[0]


CASC = ("--mode", "casc")
# For proofs whose casc strategy splits clauses with AVATAR, which the
# reconstruction does not handle.
NO_SPLITTING = ("--avatar", "off", "--proof", "tptp")


def vampire_proof(premise: Sequence[str], law: str, time_limit: float, cores: int = 1,
                  options: Sequence[str] = CASC, vampire: str = "vampire") -> str | None:
    """Vampire's output, if it proves the law."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
        file.write(tptp_problem(premise, law))
        path = Path(file.name)
    try:
        output = subprocess.run(
            [vampire, *options, "--cores", str(cores), "--time_limit", str(time_limit), str(path)],
            capture_output=True, text=True, timeout=time_limit + 60,
        ).stdout
    except subprocess.TimeoutExpired:
        return None
    finally:
        path.unlink(missing_ok=True)
    return output if "SZS status Theorem" in output else None


def certify(premise: Sequence[str], law: str, time_limit: float, cores: int = 1) -> dict | str:
    """A checked certificate of the law from the premise, or why there is
    none: Vampire in casc mode, then without clause splitting."""
    reasons = []
    for options in (CASC, NO_SPLITTING):
        output = vampire_proof(premise, law, time_limit, cores, options)
        if output is None:
            reasons.append(f"{' '.join(options)}: no proof")
            continue
        try:
            return certificate_from_tstp(premise, law, output)
        except ReconstructionError as error:
            reasons.append(f"{' '.join(options)}: {error}")
    return "; ".join(reasons)


# Certificates from the proofs an exploration saved.

def _mirror(term):
    return term if isinstance(term, str) else (_mirror(term[1]), _mirror(term[0]))


def _mirror_law(text: str) -> str:
    lhs, rhs = parse_law(text)
    return f"{show(_mirror(lhs))} = {show(_mirror(rhs))}"


def mirrored(certificate: dict) -> dict:
    """The certificate of the dual implication, every term mirrored: each
    step then rewrites with the mirror image of the law it cites."""
    terms = lambda chain: [show(_mirror(parse_term(term))) for term in chain]
    return {
        "premise": [_mirror_law(law) for law in certificate["premise"]],
        "conclusion": _mirror_law(certificate["conclusion"]),
        "lemmas": [{"terms": terms(lemma["terms"]), "by": lemma["by"]} for lemma in certificate.get("lemmas", [])],
        "terms": terms(certificate["terms"]),
        "by": certificate["by"],
    }


def _reconstructed(record: dict) -> list[dict] | str:
    try:
        return certificates_from_tstp(record["premise"], record["conclusion"], record["proof"])
    except (ReconstructionError, RecursionError) as error:
        return str(error)


class SavedProofs:
    """The certificates of the Vampire proofs of a file the exploration
    saved, by the laws of their premises and conclusions."""

    def __init__(self, path: Path, associative: bool, processes: int):
        self.associative = associative
        with lzma.open(path, "rt", encoding="utf-8") as file:
            records = [r for r in map(json.loads, file) if r["prover"] == "vampire"]
        self.proofs, self.failed = len(records), 0
        self.by_conclusion: dict = {}
        with ProcessPoolExecutor(processes) as pool:
            for result in pool.map(_reconstructed, records, chunksize=4):
                if isinstance(result, str):
                    self.failed += 1
                    continue
                for certificate in result:
                    premise = frozenset(self.key(law) for law in certificate["premise"])
                    self.by_conclusion.setdefault(self.key(certificate["conclusion"]), []).append(
                        (premise, certificate))

    def key(self, text: str):
        return law_key(parse_law(text), self.associative)

    def certificate(self, premise: Sequence[str], law: str) -> dict | None:
        """A certificate of the law from some of the premise laws, or the
        mirror image of one of the dual implication."""
        for mirror, image in ((False, lambda text: text), (True, _mirror_law)):
            keys = {self.key(image(p)) for p in premise}
            for proved, certificate in self.by_conclusion.get(self.key(image(law)), []):
                if proved <= keys:
                    return mirrored(certificate) if mirror else certificate
        return None


# The implications and equivalences of an exploration's result to certify.

def _law_names(equations: list[dict]) -> dict:
    return {(entry["id"] if "id" in entry else entry["name"]): entry["equation"] for entry in equations}


def cover(results: Path, equations: list[dict], axioms: Sequence) -> list[tuple[list, object]]:
    """Single-law implications, (premise, conclusion) by the names of
    implications.json, that together with the axioms entail every
    implication of it. Each implication's conclusion laws are taken from the
    strongest, those of the fewest objects of the context, each only if the
    ones taken so far do not entail it."""
    names = list(_law_names(equations))
    bit = {name: 1 << i for i, name in enumerate(names)}
    context_name = {(f"Eq{n}" if isinstance(n, int) else n): n for n in names}
    lines = (results / "context.cxt").read_text(encoding="utf-8").split("\n")
    n, m = int(lines[2]), int(lines[3])
    attributes, rows = lines[5 + n:5 + n + m], lines[5 + n + m:5 + n + m + n]
    extent = {context_name[a]: sum(row[j] == "X" for row in rows) for j, a in enumerate(attributes)}
    trivial = [name for name, text in _law_names(equations).items() if len(set(parse_law(text))) == 1]
    always = sum(bit[a] for a in list(axioms) + trivial)
    rules: list[tuple[int, int]] = []

    def closure(mask: int) -> int:
        changed = True
        while changed:
            changed = False
            for premise, conclusion in rules:
                if premise & ~mask == 0 and conclusion & ~mask:
                    mask |= conclusion
                    changed = True
        return mask

    chosen = []
    for entry in json.loads((results / "implications.json").read_text(encoding="utf-8")):
        premise = sorted(set(entry["premise"]) | set(axioms), key=names.index)
        mask = sum(bit[p] for p in premise) | always
        for law in sorted(entry["conclusion"], key=lambda law: extent[law]):
            if not bit[law] & closure(mask):
                rules.append((mask, bit[law]))
                chosen.append((premise, law))
    return chosen


def class_equivalences(equations: list[dict], axioms: Sequence) -> list[tuple[list[str], str]]:
    """Both implications between each law of the equations file and each
    other law of its class, as (premise, conclusion) laws."""
    axiom_laws = [_law_names(equations)[a] for a in axioms]
    pairs = []
    for entry in equations:
        own = parse_law(entry["equation"])
        for word in entry["class"]:
            member = word_law(word)
            if law_key_words(member) == law_key_words(own):
                continue
            text = f"{show(member[0])} = {show(member[1])}"
            pairs.append(([entry["equation"], *axiom_laws], text))
            pairs.append(([text, *axiom_laws], entry["equation"]))
    return pairs


def law_key_words(law: tuple) -> tuple:
    """A semigroup law up to renaming variables and swapping sides."""
    def leaves(term):
        return [term] if isinstance(term, str) else leaves(term[0]) + leaves(term[1])
    forms = []
    for a, b in (law, law[::-1]):
        names: dict = {}
        forms.append(tuple(tuple(names.setdefault(v, len(names)) for v in leaves(side)) for side in (a, b)))
    return min(forms)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Certify the implications of an exploration's result.")
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR")
    parser.add_argument("-o", "--output", type=Path, required=True, metavar="CERTIFICATES",
                        help="the file to write, one certificate a line, compressed with xz if it ends in .xz")
    parser.add_argument("--classes", action="store_true",
                        help="also certify the equivalence of each law with the laws of its class")
    parser.add_argument("--jobs", type=int, default=8, help="Vampire processes at once (default: 8)")
    parser.add_argument("--time-limit", type=float, default=10, help="seconds for each proof (default: 10)")
    parser.add_argument("--root", type=Path, default=Path("."),
                        help="the directory the exploration was run from (default: the current one)")
    parser.add_argument("--proofs", type=Path, default=None,
                        help="the proofs the exploration saved (default: RESULTS_DIR/proofs.jsonl.xz, if any)")
    args = parser.parse_args(argv)
    settings = tomllib.loads((args.results / "settings.toml").read_text(encoding="utf-8"))
    equations = json.loads((args.root / settings["equations"]).read_text(encoding="utf-8"))
    names = _law_names(equations)
    axioms = [a for a in names if str(a) in {str(x) for x in settings.get("axiom", [])}]
    associativity = law_key(parse_law("x * (y * z) = (x * y) * z"), False)
    associative = any(law_key(parse_law(names[a]), False) == associativity for a in axioms)
    tasks = [([names[p] for p in premise], names[law]) for premise, law in cover(args.results, equations, axioms)]
    implications = len(tasks)
    if args.classes:
        tasks += class_equivalences(equations, axioms)
    print(f"{implications} implications{f' and {len(tasks) - implications} class equivalences' if args.classes else ''}"
          " to certify", flush=True)
    started, results, failures = time.monotonic(), [], []
    proofs = args.proofs or args.results / "proofs.jsonl.xz"
    if args.proofs is not None or proofs.exists():
        saved = SavedProofs(proofs, associative, args.jobs)
        left = []
        for premise, law in tasks:
            certificate = saved.certificate(premise, law)
            if certificate is None:
                left.append((premise, law))
            else:
                results.append(certificate)
        print(f"{len(results)} certified by the {saved.proofs} proofs saved ({saved.failed} not reconstructed) "
              f"or their mirror images, in {time.monotonic() - started:.0f} s", flush=True)
        tasks = left
    with ThreadPoolExecutor(args.jobs) as pool:
        for k, ((premise, law), result) in enumerate(
                zip(tasks, pool.map(lambda task: certify(*task, args.time_limit), tasks)), start=1):
            if isinstance(result, dict):
                results.append(result)
            else:
                failures.append((premise, law, result))
            if k % 500 == 0:
                print(f"{k} done, {len(failures)} failed, {time.monotonic() - started:.0f} s", flush=True)
    # What one core did not prove, all of them may, with more time.
    retried = []
    for premise, law, reason in failures:
        result = certify(premise, law, 6 * args.time_limit, args.jobs)
        if isinstance(result, dict):
            results.append(result)
        else:
            retried.append((premise, law, f"{reason}; on {args.jobs} cores: {result}"))
    failures = retried
    opener = lzma.open if args.output.suffix == ".xz" else open
    with opener(args.output, "wt", encoding="utf-8") as file:
        for certificate in results:
            file.write(json.dumps(certificate, separators=(",", ":")) + "\n")
    print(f"Wrote {len(results)} certificates to {args.output} in {time.monotonic() - started:.0f} s", flush=True)
    for premise, law, reason in failures:
        print(f"Not certified: {premise} => {law}: {reason}", flush=True)
    if failures:
        sys.exit(1)


if __name__ == "__main__":
    main()
