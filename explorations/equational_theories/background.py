"""Background implications between one-variable equations, derived by
equational reasoning bounded by the order of the equations it may use.

The order of an equation is the number of operations in it, counting both
sides. Starting from some equations, `BoundedDerivation` derives new ones by

1. multiplying both sides by the same term from the same side: from s = t,
   derive u * s = u * t and s * u = t * u;
2. replacing every occurrence of the variable by the same term: from s = t,
   derive s[u/x] = t[u/x];
3. replacing a subterm by an equal one: from s = t and an equation with s
   at some position of one side, derive the equation with t at that
   position instead. With s as a whole side this is transitivity.

Every equation it derives, and every one it derives from, has order at most
`max_order`, so the derivation is a closure on a finite set of equations.
Equations are unordered pairs of terms, so symmetry needs no rule, and
equations with the same term on both sides hold from the start.

Each rule is sound in every magma, so what the derivation proves from some
attribute equations holds in every magma satisfying them. Restricted to the
attributes it is a closure operator, and `background_implications` returns
its canonical basis.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from conceptual_exploration.algorithms.next_closure import NextClosure
from conceptual_exploration.core.bitset import AttributeIndex
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.core.theory import ImplicationTheory
from explorations.equational_theories.magma import ETP, Equation, Op, Term, Var


@dataclass(frozen=True, slots=True)
class Derived:
    """Equations closed under a `BoundedDerivation`, as pairs of term numbers
    (smaller first), together with the terms each term is equal to."""

    pairs: frozenset[tuple[int, int]]
    partners: dict[int, frozenset[int]]


class BoundedDerivation:
    """Derivation of one-variable equations of order at most `max_order`.

    Terms are numbered once, and equations are held as pairs of term numbers
    (smaller first). `closure` derives semi-naively: each new pair is put
    through the rules once, against the pairs derived before it.
    """

    EMPTY = Derived(frozenset(), {})

    def __init__(self, max_order: int, variable: str = "x") -> None:
        if max_order < 0:
            raise ValueError(f"max_order must be non-negative, got {max_order}")
        self.max_order = max_order
        self.variable = variable

        # All terms of at most max_order operations, by number of operations:
        # a single side can have that many when the other is the variable.
        self.terms: list[Term] = ETP.generate_terms([variable], max_order)
        self.numbers: dict[Term, int] = {t: i for i, t in enumerate(self.terms)}
        self.ops = [t.op_count() for t in self.terms]
        self._var = self.numbers[Var(variable)]
        self._left = [self.numbers[t.left] if isinstance(t, Op) else -1 for t in self.terms]
        self._right = [self.numbers[t.right] if isinstance(t, Op) else -1 for t in self.terms]
        self._products = {
            (left, right): i
            for i, (left, right) in enumerate(zip(self._left, self._right))
            if left >= 0
        }
        # The terms with at most k operations are the first _prefix[k + 1].
        self._prefix = [0] * (max_order + 2)
        for i, ops in enumerate(self.ops):
            self._prefix[ops + 1] = i + 1

        # For each term, its subterms with the path to them (0 = left, 1 =
        # right), and for each term, the places it occurs as a subterm, in
        # the smallest enclosing terms first.
        self._positions: list[list[tuple[tuple[int, ...], int]]] = []
        self._occurrences: list[list[tuple[int, tuple[int, ...]]]] = [[] for _ in self.terms]
        for i in range(len(self.terms)):
            positions = list(self._subterms(i, ()))
            self._positions.append(positions)
            for path, sub in positions:
                self._occurrences[sub].append((i, path))

        self._substituted: dict[tuple[int, int], int] = {}
        self._replaced: dict[tuple[int, tuple[int, ...], int], int] = {}

    def _subterms(self, i: int, path: tuple[int, ...]):
        yield path, i
        if self._left[i] >= 0:
            yield from self._subterms(self._left[i], path + (0,))
            yield from self._subterms(self._right[i], path + (1,))

    def _substitute(self, t: int, u: int) -> int:
        """t[u/x], which the caller has checked to be within the bound."""
        key = (t, u)
        result = self._substituted.get(key)
        if result is None:
            if t == self._var:
                result = u
            else:
                result = self._products[
                    self._substitute(self._left[t], u),
                    self._substitute(self._right[t], u),
                ]
            self._substituted[key] = result
        return result

    def _replace(self, t: int, path: tuple[int, ...], d: int) -> int:
        """t with d at `path`, which the caller has checked to be within the bound."""
        if not path:
            return d
        key = (t, path, d)
        result = self._replaced.get(key)
        if result is None:
            left, right = self._left[t], self._right[t]
            if path[0] == 0:
                result = self._products[self._replace(left, path[1:], d), right]
            else:
                result = self._products[left, self._replace(right, path[1:], d)]
            self._replaced[key] = result
        return result

    def pair(self, equation: Equation) -> tuple[int, int]:
        """The pair of term numbers standing for `equation`."""
        if not set(equation.variables) <= {self.variable}:
            raise ValueError(f"{equation} is not an equation in the variable {self.variable}")
        order = equation.lhs.op_count() + equation.rhs.op_count()
        if order > self.max_order:
            raise ValueError(f"{equation} has order {order}, above max_order {self.max_order}")
        a, b = self.numbers[equation.lhs], self.numbers[equation.rhs]
        return (a, b) if a <= b else (b, a)

    def closure(
        self,
        equations: Iterable[tuple[int, int]],
        base: Derived = EMPTY,
    ) -> Derived:
        """All non-trivial equations derivable from `equations` together with
        `base`, which is closed already, so the rules are only applied to what
        `equations` add to it."""
        n = self.max_order
        ops = self.ops
        products = self._products
        replace = self._replace
        old_pairs, old_partners = base.pairs, base.partners
        added: set[tuple[int, int]] = set()
        new_partners: dict[int, set[int]] = {}
        pending: list[tuple[int, int]] = []

        def add(a: int, b: int) -> None:
            if a == b:
                return
            if a > b:
                a, b = b, a
            if (a, b) in old_pairs or (a, b) in added:
                return
            added.add((a, b))
            new_partners.setdefault(a, set()).add(b)
            new_partners.setdefault(b, set()).add(a)
            pending.append((a, b))

        def partners(t: int) -> tuple[int, ...]:
            return (*old_partners.get(t, ()), *new_partners.get(t, ()))

        for a, b in equations:
            add(a, b)

        while pending:
            a, b = pending.pop()
            order = ops[a] + ops[b]

            # 1. u * a = u * b and a * u = b * u.
            if order + 2 <= n:
                for u in range(self._prefix[(n - order - 2) // 2 + 1]):
                    add(products[u, a], products[u, b])
                    add(products[a, u], products[b, u])

            # 2. a[u/x] = b[u/x]; the order grows by ops(u) per occurrence
            # of x, and there are order + 2 of them.
            for u in range(self._prefix[(n - order) // (order + 2) + 1]):
                if u != self._var:
                    add(self._substitute(a, u), self._substitute(b, u))

            # 3. With a = b, rewrite the equations with an occurrence of a
            # or b on one side ...
            for c, d in ((a, b), (b, a)):
                growth = ops[d] - ops[c]
                for t, path in self._occurrences[c]:
                    room = n - ops[t] - growth
                    if room < 0:
                        break
                    for r in partners(t):
                        if ops[r] <= room:
                            add(replace(t, path, d), r)

            # ... and rewrite a = b with the equations derived so far.
            for t, r in ((a, b), (b, a)):
                room = n - ops[t] - ops[r]
                for path, c in self._positions[t]:
                    for d in partners(c):
                        if ops[d] - ops[c] <= room:
                            add(replace(t, path, d), r)

        if not added:
            return base
        merged = dict(old_partners)
        for t, others in new_partners.items():
            merged[t] = old_partners.get(t, frozenset()) | others
        return Derived(old_pairs | added, merged)


def _variable(attributes: Sequence[Equation]) -> str:
    variables = set().union(*(eq.variables for eq in attributes))
    if len(variables) > 1:
        raise ValueError(
            f"Background derivation needs equations in one variable, got {sorted(variables)}"
        )
    return variables.pop() if variables else "x"


def background_implications(
    attributes: Sequence[Equation],
    max_order: int,
) -> list[Implication[Equation]]:
    """The canonical basis of what bounded derivation proves among `attributes`.

    An implication between the attributes follows from the result exactly
    when its conclusion is derivable from its premise using the rules of
    `BoundedDerivation` with equations of order at most `max_order`, which
    must be at least the order of every attribute. The attributes must share
    a single variable.
    """
    attributes = tuple(attributes)
    derivation = BoundedDerivation(max_order, _variable(attributes))
    pairs = [derivation.pair(eq) for eq in attributes]
    trivial = sum(1 << i for i, (a, b) in enumerate(pairs) if a == b)
    positions: dict[tuple[int, int], int] = {}
    for i, p in enumerate(pairs):
        positions[p] = positions.get(p, 0) | 1 << i

    # NextClosure asks for the closure of the part of a closed set below some
    # attribute together with that attribute, so each mask's derivation
    # extends that of the mask without its highest attribute, and the
    # derivations of recent masks are kept for reuse.
    derivations: dict[int, Derived] = {0: BoundedDerivation.EMPTY}

    def derive(mask: int) -> Derived:
        derived = derivations.get(mask)
        if derived is None:
            highest = mask.bit_length() - 1
            derived = derivation.closure([pairs[highest]], derive(mask ^ (1 << highest)))
            if len(derivations) >= 1 << 14:
                derivations.clear()
                derivations[0] = BoundedDerivation.EMPTY
            derivations[mask] = derived
        return derived

    def closure_mask(mask: int) -> int:
        derived = derive(mask).pairs
        result = mask | trivial
        for p, position_mask in positions.items():
            if p in derived:
                result |= position_mask
        return result

    index = AttributeIndex[Equation](attributes)
    theory = ImplicationTheory[Equation](index=index)
    premises = NextClosure(
        attributes, mask_closure_operator=theory.closure_mask
    ).generate_masks()
    try:
        premise = next(premises)
        while True:
            closed = closure_mask(premise)
            if closed != premise:
                theory.add(Implication(index.decode(premise), index.decode(closed & ~premise)))
                premise = premises.send(True)
            else:
                premise = next(premises)
    except StopIteration:
        pass
    return theory.implications
