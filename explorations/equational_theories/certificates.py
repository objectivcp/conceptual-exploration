"""Proof certificates of equational implications, and their checker.

A certificate proves a law from premise laws by chains of terms, each step
replacing one subterm by another with an instance of a premise or of an
earlier lemma, in either direction:

    {"premise": [law, ...], "conclusion": law,
     "lemmas": [{"terms": [t0, t1, ...], "by": ["h0", "l2", ...]}, ...],
     "terms": [...], "by": [...]}

Laws and terms are strings, as in equations.json: "x = (x * (y * z))". A
chain's terms run from the
left side of what it proves to the right side; "hK" cites premise K and "lK"
lemma K, which proves the equation of its first and last terms. The variables
of a chain are constants: a lemma holds for all values of its variables
because its chain holds for any. Equational logic is complete for this, so
every implication that holds in all magmas has a certificate.

The checker relies on nothing else in this repository, so that the results
it checks do not rest on the code that found them.
"""

from __future__ import annotations

import re
from collections.abc import Sequence

# A term is a variable, a string, or a product, a pair of terms.

_TOKEN = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*|[()*=])")


def parse_term(text: str):
    """A term in infix notation, products associating to the left."""
    tokens = _TOKEN.findall(text)
    if "".join(tokens) != re.sub(r"\s", "", text):
        raise ValueError(f"Cannot parse {text!r}")
    position = 0

    def primary():
        nonlocal position
        if position == len(tokens):
            raise ValueError(f"Cannot parse {text!r}")
        token = tokens[position]
        position += 1
        if token == "(":
            term = product()
            if position == len(tokens) or tokens[position] != ")":
                raise ValueError(f"Cannot parse {text!r}")
            position += 1
            return term
        if not re.match(r"[A-Za-z_]", token):
            raise ValueError(f"Cannot parse {text!r}")
        return token

    def product():
        nonlocal position
        term = primary()
        while position < len(tokens) and tokens[position] == "*":
            position += 1
            term = (term, primary())
        return term

    term = product()
    if position != len(tokens):
        raise ValueError(f"Cannot parse {text!r}")
    return term


def word_term(word: str):
    """The right-associated product of the letters of a word."""
    term = word[-1]
    for letter in reversed(word[:-1]):
        term = (letter, term)
    return term


def word_law(text: str) -> tuple:
    """A semigroup law written as two words of one-letter variables,
    "xxy = yyx", its sides right-associated."""
    sides = [side.strip() for side in text.split("=")]
    if len(sides) != 2 or not all(side.isalpha() for side in sides):
        raise ValueError(f"Cannot parse {text!r}")
    return word_term(sides[0]), word_term(sides[1])


def parse_law(text: str) -> tuple:
    sides = text.split("=")
    if len(sides) != 2:
        raise ValueError(f"Cannot parse {text!r}")
    return parse_term(sides[0]), parse_term(sides[1])


def show(term) -> str:
    return term if isinstance(term, str) else f"({show(term[0])} * {show(term[1])})"


def _match(pattern, term, substitution: dict) -> bool:
    """Extends `substitution` so that it maps `pattern` to `term`, if it can."""
    if isinstance(pattern, str):
        if pattern in substitution:
            return substitution[pattern] == term
        substitution[pattern] = term
        return True
    return (isinstance(term, tuple) and _match(pattern[0], term[0], substitution)
            and _match(pattern[1], term[1], substitution))


def _subterm(term, path: Sequence[int]):
    for i in path:
        term = term[i]
    return term


def _difference(s, t) -> list[int]:
    """The path to the smallest subterm outside of which s and t agree."""
    path = []
    while isinstance(s, tuple) and isinstance(t, tuple):
        left, right = s[0] != t[0], s[1] != t[1]
        if left == right:
            break
        i = 0 if left else 1
        path.append(i)
        s, t = s[i], t[i]
    return path


def is_step(s, t, law: tuple) -> bool:
    """Whether t is s with one subterm replaced by another by an instance of
    the law, in either direction."""
    if s == t:
        return True
    path = _difference(s, t)
    for depth in range(len(path), -1, -1):
        u, v = _subterm(s, path[:depth]), _subterm(t, path[:depth])
        for lhs, rhs in (law, law[::-1]):
            substitution: dict = {}
            if _match(lhs, u, substitution) and _match(rhs, v, substitution):
                return True
    return False


class CertificateError(ValueError):
    pass


def _check_chain(terms: Sequence, by: Sequence[str], premise: Sequence[tuple], lemmas: Sequence[tuple],
                 what: str) -> tuple:
    if len(by) != len(terms) - 1 or not terms:
        raise CertificateError(f"{what}: {len(terms)} terms but {len(by)} citations")
    parsed = [parse_term(t) for t in terms]
    for k, (cite, s, t) in enumerate(zip(by, parsed, parsed[1:])):
        kind, number = cite[0], int(cite[1:]) if cite[1:].isdigit() else -1
        laws = premise if kind == "h" else lemmas if kind == "l" else ()
        if not 0 <= number < len(laws):
            raise CertificateError(f"{what}, step {k + 1}: no {cite}")
        if not is_step(s, t, laws[number]):
            raise CertificateError(f"{what}, step {k + 1}: {terms[k + 1]} does not follow from {terms[k]} by {cite}")
    return parsed[0], parsed[-1]


def check_certificate(certificate: dict) -> tuple[list[tuple], tuple]:
    """The premise and the conclusion of a certificate, as pairs of terms, if
    every step of it is right; otherwise CertificateError."""
    premise = [parse_law(law) for law in certificate["premise"]]
    conclusion = parse_law(certificate["conclusion"])
    lemmas: list[tuple] = []
    for k, lemma in enumerate(certificate.get("lemmas", [])):
        lemmas.append(_check_chain(lemma["terms"], lemma["by"], premise, lemmas, f"lemma {k}"))
    proved = _check_chain(certificate["terms"], certificate["by"], premise, lemmas, "conclusion")
    if proved != conclusion:
        raise CertificateError(f"the chain proves {show(proved[0])} = {show(proved[1])}, "
                               f"not {certificate['conclusion']}")
    return premise, conclusion
