"""Certificates of non-implication between magma laws, by Knuth-Bendix
completion.

A rewrite system R certifies that the laws P do not imply a law s = t when
- every rule of R decreases in the Knuth-Bendix order (all weights 1), so
  that R terminates;
- every critical pair of R is joinable, so that R is confluent;
- every law of P is joinable in R, so that R entails P;
- s and t have different normal forms, so that R does not entail s = t.
Then P does not imply s = t either. The conditions are checked on R itself,
however it was found; `complete` finds R by Huet's completion of P, which
may fail on an equation that the order cannot orient or run out of time.

usage: completion.py RESULTS_DIR --equations FILE [-o CERTIFICATES]

certifies the negative entries of the free magmas in RESULTS_DIR/free_magmas.json,
which rest on Vampire's saturation, with the laws of FILE.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections.abc import Iterable, Iterator, Sequence
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.magma import ETP, Equation, Term, Var

# A term is a variable name or a pair of terms, and a rule a pair of terms.
Tree = str | tuple
Rule = tuple[Tree, Tree]


class CompletionFailed(Exception):
    pass


def tree(term: Term) -> Tree:
    return term.name if isinstance(term, Var) else (tree(term.left), tree(term.right))


def law(equation: Equation) -> Rule:
    return tree(equation.lhs), tree(equation.rhs)


def show(t: Tree) -> str:
    return t if isinstance(t, str) else f"({show(t[0])} * {show(t[1])})"


def _size(t: Tree) -> int:
    return 1 if isinstance(t, str) else 1 + _size(t[0]) + _size(t[1])


def _occurrences(t: Tree, counts: dict[str, int]) -> dict[str, int]:
    if isinstance(t, str):
        counts[t] = counts.get(t, 0) + 1
    else:
        _occurrences(t[0], counts)
        _occurrences(t[1], counts)
    return counts


def kbo_greater(s: Tree, t: Tree) -> bool:
    """s > t in the Knuth-Bendix order with all weights 1."""
    if s == t:
        return False
    in_s = _occurrences(s, {})
    if any(in_s.get(v, 0) < n for v, n in _occurrences(t, {}).items()):
        return False
    if _size(s) != _size(t):
        return _size(s) > _size(t)
    if isinstance(s, str) or isinstance(t, str):
        return False
    return kbo_greater(s[0], t[0]) if s[0] != t[0] else kbo_greater(s[1], t[1])


def _match(pattern: Tree, t: Tree, sub: dict[str, Tree]) -> dict[str, Tree] | None:
    if isinstance(pattern, str):
        if pattern in sub:
            return sub if sub[pattern] == t else None
        return {**sub, pattern: t}
    if isinstance(t, str):
        return None
    sub = _match(pattern[0], t[0], sub)
    return None if sub is None else _match(pattern[1], t[1], sub)


def _substitute(t: Tree, sub: dict[str, Tree]) -> Tree:
    if isinstance(t, str):
        return sub.get(t, t)
    return _substitute(t[0], sub), _substitute(t[1], sub)


def _walk(t: Tree, sub: dict[str, Tree]) -> Tree:
    while isinstance(t, str) and t in sub:
        t = sub[t]
    return t


def _occurs(v: str, t: Tree, sub: dict[str, Tree]) -> bool:
    t = _walk(t, sub)
    if isinstance(t, str):
        return t == v
    return _occurs(v, t[0], sub) or _occurs(v, t[1], sub)


def _unify(a: Tree, b: Tree, sub: dict[str, Tree]) -> dict[str, Tree] | None:
    a, b = _walk(a, sub), _walk(b, sub)
    if a == b:
        return sub
    if isinstance(a, str):
        return None if _occurs(a, b, sub) else {**sub, a: b}
    if isinstance(b, str):
        return _unify(b, a, sub)
    sub = _unify(a[0], b[0], sub)
    return None if sub is None else _unify(a[1], b[1], sub)


def _resolve(t: Tree, sub: dict[str, Tree]) -> Tree:
    t = _walk(t, sub)
    return t if isinstance(t, str) else (_resolve(t[0], sub), _resolve(t[1], sub))


def _rewrite_once(t: Tree, rules: Sequence[Rule]) -> Tree | None:
    for lhs, rhs in rules:
        sub = _match(lhs, t, {})
        if sub is not None:
            return _substitute(rhs, sub)
    if isinstance(t, str):
        return None
    left = _rewrite_once(t[0], rules)
    if left is not None:
        return left, t[1]
    right = _rewrite_once(t[1], rules)
    return None if right is None else (t[0], right)


def normal_form(t: Tree, rules: Sequence[Rule]) -> Tree:
    """t rewritten with `rules` until no rule applies; the rules must terminate."""
    while (u := _rewrite_once(t, rules)) is not None:
        t = u
    return t


def _renamed(t: Tree, suffix: str) -> Tree:
    return t + suffix if isinstance(t, str) else (_renamed(t[0], suffix), _renamed(t[1], suffix))


def _subterms(t: Tree, path: tuple[int, ...] = ()) -> Iterator[tuple[tuple[int, ...], Tree]]:
    """The subterms of t that are not variables, with their positions."""
    if not isinstance(t, str):
        yield path, t
        yield from _subterms(t[0], path + (0,))
        yield from _subterms(t[1], path + (1,))


def _replaced(t: Tree, path: tuple[int, ...], u: Tree) -> Tree:
    if not path:
        return u
    return (_replaced(t[0], path[1:], u), t[1]) if path[0] == 0 else (t[0], _replaced(t[1], path[1:], u))


def critical_pairs(outer: Rule, inner: Rule) -> Iterator[Rule]:
    """The critical pairs of `inner`'s left side overlapping `outer`'s at a
    position that is not a variable, the two rules' variables kept apart."""
    l1, r1 = _renamed(outer[0], "'"), _renamed(outer[1], "'")
    l2, r2 = _renamed(inner[0], '"'), _renamed(inner[1], '"')
    for path, subterm in _subterms(l1):
        if not path and outer == inner:
            continue
        sub = _unify(subterm, l2, {})
        if sub is not None:
            yield _resolve(r1, sub), _resolve(_replaced(l1, path, r2), sub)


def _canonical(pair: Rule) -> Rule:
    names: dict[str, str] = {}

    def rename(t: Tree) -> Tree:
        if isinstance(t, str):
            return names.setdefault(t, f"x{len(names)}")
        return rename(t[0]), rename(t[1])

    return rename(pair[0]), rename(pair[1])


def complete(equations: Iterable[Rule], max_rules: int = 400, time_limit: float = 10.0) -> list[Rule]:
    """A convergent rewrite system equivalent to the equations, by Huet's
    completion with the Knuth-Bendix order.

    Raises CompletionFailed if an equation cannot be oriented, or the limits
    are reached.
    """
    start = time.monotonic()
    pending = [_canonical(e) for e in equations]
    rules: list[Rule] = []
    while pending:
        if time.monotonic() - start > time_limit:
            raise CompletionFailed("time limit")
        pending.sort(key=lambda e: _size(e[0]) + _size(e[1]))
        a, b = pending.pop(0)
        a, b = normal_form(a, rules), normal_form(b, rules)
        if a == b:
            continue
        if kbo_greater(a, b):
            rule = _canonical((a, b))
        elif kbo_greater(b, a):
            rule = _canonical((b, a))
        else:
            raise CompletionFailed(f"cannot orient {show(a)} = {show(b)}")
        kept = []
        for lhs, rhs in rules:
            if _rewrite_once(lhs, [rule]) is not None:
                pending.append((lhs, rhs))
            else:
                kept.append((lhs, normal_form(rhs, rules + [rule])))
        rules = kept + [rule]
        if len(rules) > max_rules:
            raise CompletionFailed("rule limit")
        for other in rules:
            pending.extend(critical_pairs(rule, other))
            if other != rule:
                pending.extend(critical_pairs(other, rule))
    return rules


def certified(rules: Sequence[Rule], premise: Iterable[Rule], laws: Sequence[Rule]) -> list[bool]:
    """For each law, whether `rules` certify that the premise does not imply
    it; raises ValueError if `rules` are not a certificate for the premise at
    all (see the module docstring)."""
    for lhs, rhs in rules:
        if not kbo_greater(lhs, rhs):
            raise ValueError(f"rule {show(lhs)} -> {show(rhs)} does not decrease")
    for outer in rules:
        for inner in rules:
            for a, b in critical_pairs(outer, inner):
                if normal_form(a, rules) != normal_form(b, rules):
                    raise ValueError(f"critical pair {show(a)} = {show(b)} is not joinable")
    for a, b in premise:
        if normal_form(a, rules) != normal_form(b, rules):
            raise ValueError(f"premise law {show(a)} = {show(b)} is not joinable")
    return [normal_form(a, rules) != normal_form(b, rules) for a, b in laws]


def _certify(job: tuple[list[Rule], list[Rule]]) -> tuple[list[Rule] | None, list[bool] | str]:
    premise, laws = job
    try:
        rules = complete(premise)
    except CompletionFailed as failure:
        return None, str(failure)
    return rules, certified(rules, premise, laws)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Certify the negative entries of the free magmas of an exploration by Knuth-Bendix completion."
    )
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR", help="the results of an exploration")
    parser.add_argument("--equations", type=Path, required=True, metavar="FILE", help="the laws it explored")
    parser.add_argument("-o", "--output", type=Path, metavar="CERTIFICATES",
                        help="write each premise's rewrite system and the laws it certifies here")
    args = parser.parse_args(argv)
    equations = ETP.load_equations(args.equations)
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    by_ident = {ident(eq): eq for eq in equations}
    dual = ETP.get_duality_mapping(equations)
    free = json.loads((args.results / "free_magmas.json").read_text(encoding="utf-8"))
    groups: dict[tuple, set] = {}
    for magma in free:
        premise = {by_ident[n] for n in magma["premise"]}
        if magma["dual_of"] and not {ident(eq) for eq in premise} <= set(magma["positive"]):
            # Files written before the fix record a dual's premise as its original's.
            premise = {dual(eq) for eq in premise}
        key = tuple(sorted(ident(eq) for eq in premise))
        groups.setdefault(key, set()).update(magma["negative"])
    keys = list(groups)
    jobs = [([law(by_ident[n]) for n in key], [law(by_ident[n]) for n in sorted(groups[key])]) for key in keys]
    certificates, total, certified_count, failed = [], 0, 0, 0
    with ProcessPoolExecutor() as pool:
        for key, (rules, verdicts) in zip(keys, pool.map(_certify, jobs, chunksize=4)):
            negative = sorted(groups[key])
            total += len(negative)
            if rules is None:
                failed += 1
                certificates.append({"premise": list(key), "failed": verdicts, "uncertified": negative})
                continue
            good = [n for n, v in zip(negative, verdicts) if v]
            certified_count += len(good)
            certificates.append({
                "premise": list(key),
                "rules": [f"{show(lhs)} -> {show(rhs)}" for lhs, rhs in rules],
                "certified": good,
                "uncertified": [n for n in negative if n not in good],
            })
    if args.output is not None:
        args.output.write_text(
            "[\n" + ",\n".join("  " + json.dumps(c) for c in certificates) + "\n]\n", encoding="utf-8"
        )
    print(f"{len(keys)} premises, {failed} not completed; "
          f"{certified_count} of {total} negative entries certified")


if __name__ == "__main__":
    main()
