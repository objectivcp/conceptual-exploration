"""Magma and Equational Theory domain for Formal Concept Analysis and Attribute Exploration.

Implements algebraic structures, term ASTs, equations, duality symmetries,
and expert counterexample search for exploring equational theories of magmas,
as studied in the Equational Theories Project (ETP).
"""

from __future__ import annotations

import re
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from itertools import product
from typing import ClassVar

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.experts.base import Expert


class Term:
    """Abstract base class for terms in a magma signature (single binary operation `*`)."""

    def eval(self, env: dict[str, int], table: Sequence[Sequence[int]]) -> int:
        """Evaluate the term under a variable assignment and magma operation table."""
        raise NotImplementedError

    def vars(self) -> frozenset[str]:
        """Return the set of free variables occurring in the term."""
        raise NotImplementedError

    def dual(self) -> Term:
        """Return the dual (opposite) term where (s * t)^op = (t^op * s^op)."""
        raise NotImplementedError

    def substitute(self, mapping: dict[str, Term]) -> Term:
        """Substitute variables with other terms."""
        raise NotImplementedError

    def size(self) -> int:
        """Return the number of variable and operation nodes in the AST."""
        raise NotImplementedError

    def op_count(self) -> int:
        """Return the number of binary operation nodes in the AST."""
        raise NotImplementedError

    def __lt__(self, other: Term) -> bool:
        return str(self) < str(other)

    @staticmethod
    def parse(s: str) -> Term:
        """Parse a magma term from a string (e.g. 'x * (y * z)' or '(x * y) * (z * w)')."""
        s = s.strip()
        tokens = [t for t in re.split(r"(\s+|\*|\(|\))", s) if t and not t.isspace()]
        if not tokens:
            raise ValueError("Empty term string")

        pos = 0

        def parse_primary() -> Term:
            nonlocal pos
            if pos >= len(tokens):
                raise ValueError("Unexpected end of term expression")
            tok = tokens[pos]
            if tok == "(":
                pos += 1
                expr = parse_expr()
                if pos >= len(tokens) or tokens[pos] != ")":
                    raise ValueError(f"Expected ')' matching '(' at token {pos}")
                pos += 1
                return expr
            elif tok.isidentifier():
                pos += 1
                return Var(tok)
            else:
                raise ValueError(f"Unexpected token: '{tok}'")

        def parse_expr() -> Term:
            nonlocal pos
            left = parse_primary()
            while pos < len(tokens) and tokens[pos] == "*":
                pos += 1
                right = parse_primary()
                left = Op(left, right)
            return left

        result = parse_expr()
        if pos != len(tokens):
            raise ValueError(f"Extra trailing tokens in term: {tokens[pos:]}")
        return result


@dataclass(frozen=True, slots=True)
class Var(Term):
    """Variable term, e.g. `x`, `y`, `z`."""

    name: str

    def eval(self, env: dict[str, int], table: Sequence[Sequence[int]]) -> int:
        return env[self.name]

    def vars(self) -> frozenset[str]:
        return frozenset([self.name])

    def dual(self) -> Term:
        return self

    def substitute(self, mapping: dict[str, Term]) -> Term:
        return mapping.get(self.name, self)

    def size(self) -> int:
        return 1

    def op_count(self) -> int:
        return 0

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True)
class Op(Term):
    """Binary magma operation node `(left * right)`."""

    left: Term
    right: Term

    def eval(self, env: dict[str, int], table: Sequence[Sequence[int]]) -> int:
        l_val = self.left.eval(env, table)
        r_val = self.right.eval(env, table)
        return table[l_val][r_val]

    def vars(self) -> frozenset[str]:
        return self.left.vars() | self.right.vars()

    def dual(self) -> Term:
        return Op(self.right.dual(), self.left.dual())

    def substitute(self, mapping: dict[str, Term]) -> Term:
        return Op(self.left.substitute(mapping), self.right.substitute(mapping))

    def size(self) -> int:
        return 1 + self.left.size() + self.right.size()

    def op_count(self) -> int:
        return 1 + self.left.op_count() + self.right.op_count()

    def __str__(self) -> str:
        return f"({self.left} * {self.right})"

    def __repr__(self) -> str:
        return f"({self.left} * {self.right})"


@dataclass(frozen=True, slots=True)
class Equation:
    """An equational law `LHS = RHS` on magmas, universally quantified over all occurring variables."""

    lhs: Term
    rhs: Term
    name: str | None = None
    id: int | None = None

    @property
    def variables(self) -> tuple[str, ...]:
        return tuple(sorted(self.lhs.vars() | self.rhs.vars()))

    def dual(self) -> Equation:
        """Return the dual equation under the anti-automorphism of the binary operation."""
        dual_name = f"Dual({self.name})" if self.name else None
        return Equation(self.lhs.dual(), self.rhs.dual(), name=dual_name)

    def holds_in_table(self, size: int, table: Sequence[Sequence[int]]) -> bool:
        """Check if the equation holds universally in a magma defined by its Cayley table."""
        vars_list = self.variables
        if not vars_list:
            return self.lhs.eval({}, table) == self.rhs.eval({}, table)

        for vals in product(range(size), repeat=len(vars_list)):
            env = dict(zip(vars_list, vals))
            if self.lhs.eval(env, table) != self.rhs.eval(env, table):
                return False
        return True

    def holds_in_magma(self, magma: Magma) -> bool:
        """Check if the equation holds in the given Magma."""
        return self.holds_in_table(magma.size, magma.table)

    def substitute(self, mapping: dict[str, Term]) -> Equation:
        return Equation(self.lhs.substitute(mapping), self.rhs.substitute(mapping))

    def is_equivalent_to(self, other: Equation) -> bool:
        """Check if two equations are equivalent under variable renaming and LHS/RHS swap."""
        from itertools import permutations

        vars1 = self.variables
        vars2 = other.variables
        if len(vars1) != len(vars2):
            return False

        for p in permutations(vars2):
            env = {v1: Var(v2) for v1, v2 in zip(vars1, p)}
            s_lhs = self.lhs.substitute(env)
            s_rhs = self.rhs.substitute(env)
            if (s_lhs == other.lhs and s_rhs == other.rhs) or (s_lhs == other.rhs and s_rhs == other.lhs):
                return True
        return False

    @staticmethod
    def parse(s: str, name: str | None = None, id: int | None = None) -> Equation:
        """Parse an equation string like 'x * y = y * x' or '(x * y) * z = x * (y * z)'."""
        if "=" not in s:
            raise ValueError(f"Equation string must contain '=': {s}")
        parts = s.split("=", 1)
        lhs = Term.parse(parts[0])
        rhs = Term.parse(parts[1])
        return Equation(lhs, rhs, name=name, id=id)

    def __str__(self) -> str:
        if self.name and self.id is not None:
            return f"Eq{self.id} ({self.name}): {self.lhs} = {self.rhs}"
        if self.name:
            return f"{self.name}: {self.lhs} = {self.rhs}"
        if self.id is not None:
            return f"Eq{self.id}: {self.lhs} = {self.rhs}"
        return f"{self.lhs} = {self.rhs}"

    def __repr__(self) -> str:
        return self.__str__()

    def __lt__(self, other: Equation) -> bool:
        if not isinstance(other, Equation):
            return NotImplemented
        s_id = self.id if self.id is not None else -1
        o_id = other.id if other.id is not None else -1
        if s_id != o_id:
            return s_id < o_id
        return str(self) < str(other)


@dataclass(frozen=True, slots=True)
class Magma:
    """A finite Magma (set {0, 1, ..., size-1} with a binary operation table)."""

    size: int
    table: tuple[tuple[int, ...], ...]
    name: str = ""

    def __post_init__(self) -> None:
        if len(self.table) != self.size:
            raise ValueError(f"Table row count {len(self.table)} != size {self.size}")
        for row in self.table:
            if len(row) != self.size:
                raise ValueError(f"Table column count {len(row)} != size {self.size}")
            for v in row:
                if not (0 <= v < self.size):
                    raise ValueError(f"Table element {v} out of range [0, {self.size-1}]")

    def op(self, a: int, b: int) -> int:
        return self.table[a][b]

    def dual(self) -> Magma:
        """Return the opposite magma (transpose of the Cayley table)."""
        transposed = tuple(
            tuple(self.table[c][r] for c in range(self.size))
            for r in range(self.size)
        )
        name = f"Dual({self.name})" if self.name else ""
        return Magma(self.size, transposed, name)

    def holds(self, equation: Equation) -> bool:
        """Return True if the magma satisfies the given equation universally."""
        return equation.holds_in_table(self.size, self.table)

    def evaluate_all(self, equations: Iterable[Equation]) -> tuple[set[Equation], set[Equation]]:
        """Evaluate a collection of equations, returning (positive_set, negative_set)."""
        positive: set[Equation] = set()
        negative: set[Equation] = set()
        for eq in equations:
            if self.holds(eq):
                positive.add(eq)
            else:
                negative.add(eq)
        return positive, negative

    @classmethod
    def trivial(cls) -> Magma:
        """The 1-element trivial magma."""
        return cls(1, ((0,),), name="Trivial (1-element)")

    @classmethod
    def left_projection(cls, n: int) -> Magma:
        """Left projection magma on n elements: x * y = x."""
        table = tuple(tuple(r for _ in range(n)) for r in range(n))
        return cls(n, table, name=f"Left-Projection({n})")

    @classmethod
    def right_projection(cls, n: int) -> Magma:
        """Right projection magma on n elements: x * y = y."""
        table = tuple(tuple(c for c in range(n)) for _ in range(n))
        return cls(n, table, name=f"Right-Projection({n})")

    @classmethod
    def constant(cls, n: int, c: int = 0) -> Magma:
        """Constant magma on n elements: x * y = c."""
        table = tuple(tuple(c for _ in range(n)) for _ in range(n))
        return cls(n, table, name=f"Constant({n}, c={c})")

    @classmethod
    def cyclic_addition(cls, n: int) -> Magma:
        """Cyclic group addition magma (Z_n, +): x * y = (x + y) mod n."""
        table = tuple(tuple((r + c) % n for c in range(n)) for r in range(n))
        return cls(n, table, name=f"Z_{n}(+)")

    @classmethod
    def cyclic_subtraction(cls, n: int) -> Magma:
        """Cyclic subtraction magma (Z_n, -): x * y = (x - y) mod n."""
        table = tuple(tuple((r - c) % n for c in range(n)) for r in range(n))
        return cls(n, table, name=f"Z_{n}(-)")

    @classmethod
    def cyclic_multiplication(cls, n: int) -> Magma:
        """Cyclic multiplication magma (Z_n, *): x * y = (x * y) mod n."""
        table = tuple(tuple((r * c) % n for c in range(n)) for r in range(n))
        return cls(n, table, name=f"Z_{n}(*)")

    @classmethod
    def nand(cls) -> Magma:
        """2-element NAND magma: x * y = not (x and y)."""
        table = ((1, 1), (1, 0))
        return cls(2, table, name="NAND")

    @classmethod
    def nor(cls) -> Magma:
        """2-element NOR magma: x * y = not (x or y)."""
        table = ((1, 0), (0, 0))
        return cls(2, table, name="NOR")

    @classmethod
    def implication(cls) -> Magma:
        """2-element Implication magma: x * y = (x -> y)."""
        table = ((1, 1), (0, 1))
        return cls(2, table, name="Implication (x -> y)")

    @classmethod
    def rock_paper_scissors(cls) -> Magma:
        """3-element Rock-Paper-Scissors tournament magma."""
        # 0: Rock, 1: Paper, 2: Scissors
        table = (
            (0, 1, 0),  # R*R=R, R*P=P, R*S=R
            (1, 1, 2),  # P*R=P, P*P=P, P*S=S
            (0, 2, 2),  # S*R=R, S*P=S, S*S=S
        )
        return cls(3, table, name="Rock-Paper-Scissors (tournament)")

    def __str__(self) -> str:
        lines = [f"Magma '{self.name or 'Unnamed'}' (size {self.size}):"]
        header = "  * | " + " ".join(str(i) for i in range(self.size))
        lines.append(header)
        lines.append("  --" + "+-" + "-" * (2 * self.size))
        for r in range(self.size):
            row_str = " ".join(str(self.table[r][c]) for c in range(self.size))
            lines.append(f"  {r} | {row_str}")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"Magma(size={self.size}, name='{self.name}')"


class MagmaExpert(Expert[Magma, Equation]):
    """Expert oracle for Equational Theories Project explorations on magmas.

    Validates hypothetical implications between equational laws.
    If an implication does not hold, searches for a counterexample finite magma
    satisfying all premise equations while violating at least one conclusion equation.
    """

    def __init__(
        self,
        attributes: Sequence[Equation] | None = None,
        max_search_size: int = 3,
        initial_magmas: Sequence[Magma] | None = None,
    ) -> None:
        self.attributes = tuple(attributes) if attributes is not None else None
        self.max_search_size = max_search_size
        self.cached_magmas: list[Magma] = []

        # Seed pool with standard magmas
        if initial_magmas:
            self.cached_magmas.extend(initial_magmas)
        else:
            self._seed_default_magmas()

    def _seed_default_magmas(self) -> None:
        """Initialize the pool with fundamental algebraic counterexample magmas."""
        seeds = [
            Magma.trivial(),
            Magma.left_projection(2),
            Magma.right_projection(2),
            Magma.constant(2, 0),
            Magma.constant(2, 1),
            Magma.cyclic_addition(2),
            Magma.cyclic_subtraction(2),
            Magma.cyclic_multiplication(2),
            Magma.nand(),
            Magma.nor(),
            Magma.implication(),
            Magma.left_projection(3),
            Magma.right_projection(3),
            Magma.constant(3, 0),
            Magma.cyclic_addition(3),
            Magma.cyclic_subtraction(3),
            Magma.cyclic_multiplication(3),
            Magma.rock_paper_scissors(),
        ]
        # Generate all 16 magmas of size 2
        for entries in product(range(2), repeat=4):
            t = ((entries[0], entries[1]), (entries[2], entries[3]))
            seeds.append(Magma(2, t, name=f"Order2-{entries}"))

        seen_tables = set()
        for m in seeds:
            key = (m.size, m.table)
            if key not in seen_tables:
                seen_tables.add(key)
                self.cached_magmas.append(m)

    def validate(
        self,
        implication: Implication[Equation],
        attributes: Iterable[Equation] | None = None,
    ) -> PartialObject[Magma, Equation] | None:
        """Validate if premise equations entail conclusion equations on all magmas.

        Returns a PartialObject counterexample if refuted, or None if valid.
        """
        eval_attrs = attributes or self.attributes

        # 1. Fast check against cached pool of magmas
        for magma in self.cached_magmas:
            if all(magma.holds(eq) for eq in implication.premise):
                if any(not magma.holds(eq) for eq in implication.conclusion):
                    return self._build_counterexample(magma, eval_attrs, implication)

        # 2. Dynamic search for a counterexample magma of size 1..max_search_size
        found = self._search_counterexample(
            implication.premise,
            implication.conclusion,
            self.max_search_size,
        )
        if found is not None:
            self.cached_magmas.append(found)
            return self._build_counterexample(found, eval_attrs, implication)

        return None

    def _build_counterexample(
        self,
        magma: Magma,
        attributes: Iterable[Equation] | None,
        implication: Implication[Equation],
    ) -> PartialObject[Magma, Equation]:
        """Construct a PartialObject with positive and negative equations."""
        if attributes is not None:
            pos, neg = magma.evaluate_all(attributes)
        else:
            pos = {eq for eq in implication.premise if magma.holds(eq)}
            neg = {eq for eq in implication.conclusion if not magma.holds(eq)}
        return PartialObject(magma, pos, neg)

    def _search_counterexample(
        self,
        premises: Iterable[Equation],
        conclusions: Iterable[Equation],
        max_size: int,
    ) -> Magma | None:
        """Search for a Cayley table of size <= max_size satisfying premises and violating conclusions."""
        premises_list = list(premises)
        conclusions_list = list(conclusions)

        for size in range(1, max_size + 1):
            if size == 1:
                m = Magma.trivial()
                if all(m.holds(eq) for eq in premises_list) and any(not m.holds(eq) for eq in conclusions_list):
                    return m
            elif size == 2:
                for entries in product(range(2), repeat=4):
                    table = ((entries[0], entries[1]), (entries[2], entries[3]))
                    m = Magma(2, table, name=f"Counterexample-Size2-{entries}")
                    if all(m.holds(eq) for eq in premises_list) and any(not m.holds(eq) for eq in conclusions_list):
                        return m
            elif size == 3:
                # Fast search over size 3
                for entries in product(range(3), repeat=9):
                    table = (
                        (entries[0], entries[1], entries[2]),
                        (entries[3], entries[4], entries[5]),
                        (entries[6], entries[7], entries[8]),
                    )
                    # Quick check premises
                    if all(eq.holds_in_table(3, table) for eq in premises_list):
                        if any(not eq.holds_in_table(3, table) for eq in conclusions_list):
                            return Magma(3, table, name=f"Counterexample-Size3")
        return None


class ETP:
    """Catalog and utilities for the Equational Theories Project (ETP)."""

    # Curated dictionary of prominent equational laws from ETP with canonical names and IDs
    FAMOUS_EQUATIONS: ClassVar[list[tuple[int, str, str]]] = [
        (1, "Trivial / Reflexivity", "x = x"),
        (2, "Singleton / Degenerate", "x = y"),
        (3, "Idempotence", "x = (x * x)"),
        (4, "Left-Absorption / Left-Zero", "x = (x * y)"),
        (5, "Right-Absorption / Right-Zero", "x = (y * x)"),
        (6, "Central-Identity", "x = ((x * y) * x)"),
        (7, "Left-Alternative", "((x * x) * y) = (x * (x * y))"),
        (8, "Right-Alternative", "((y * x) * x) = (y * (x * x))"),
        (9, "Flexible", "((x * y) * x) = (x * (y * x))"),
        (10, "Left-Distributive", "(x * (y * z)) = ((x * y) * (x * z))"),
        (11, "Right-Distributive", "((x * y) * z) = ((x * z) * (y * z))"),
        (12, "Self-Distributive", "((x * y) * (x * z)) = ((x * (y * z)))"),
        (14, "Central-Groupoid", "((x * y) * (y * z)) = y"),
        (23, "Left-Projection-Composition", "x = (x * (y * x))"),
        (39, "Right-Projection-Composition", "x = ((x * y) * x)"),
        (43, "Commutativity", "(x * y) = (y * x)"),
        (46, "Left-Idempotent-Composition", "(x * y) = (x * (x * y))"),
        (47, "Right-Idempotent-Composition", "((y * x) * x) = (y * x)"),
        (381, "Associativity", "((x * y) * z) = (x * (y * z))"),
        (4512, "Medial / Entropic", "((x * y) * (z * w)) = ((x * z) * (y * w))"),
        (4687, "Steiner Law 1", "(x * (x * y)) = y"),
        (4688, "Steiner Law 2", "((y * x) * x) = y"),
    ]

    @classmethod
    def get_famous_equations(cls) -> list[Equation]:
        """Return the list of famous equational laws from ETP."""
        return [
            Equation.parse(eq_str, name=name, id=eq_id)
            for eq_id, name, eq_str in cls.FAMOUS_EQUATIONS
        ]

    @classmethod
    def get_equation(cls, eq_id: int) -> Equation:
        """Lookup an equation by its ETP ID."""
        for eid, name, eq_str in cls.FAMOUS_EQUATIONS:
            if eid == eq_id:
                return Equation.parse(eq_str, name=name, id=eid)
        raise KeyError(f"Equation with ETP ID {eq_id} not found in catalog")

    @classmethod
    def generate_terms(cls, variables: Sequence[str], max_ops: int) -> list[Term]:
        """Generate all distinct magma terms over given variables up to max_ops binary operations."""
        vars_terms = [Var(v) for v in variables]
        by_ops: dict[int, list[Term]] = {0: vars_terms}

        for op_n in range(1, max_ops + 1):
            by_ops[op_n] = []
            for left_ops in range(op_n):
                right_ops = op_n - 1 - left_ops
                for left in by_ops[left_ops]:
                    for right in by_ops[right_ops]:
                        by_ops[op_n].append(Op(left, right))

        all_terms = []
        for op_n in range(max_ops + 1):
            all_terms.extend(by_ops[op_n])
        return all_terms

    @classmethod
    def generate_equations(
        cls,
        variables: Sequence[str] = ("x", "y", "z"),
        max_ops: int = 2,
    ) -> list[Equation]:
        """Generate all non-trivial equations between terms of at most max_ops operations."""
        terms = cls.generate_terms(variables, max_ops)
        equations: list[Equation] = []
        seen = set()

        for i, t1 in enumerate(terms):
            for t2 in terms[i:]:
                if t1 == t2:
                    continue  # Skip trivial x = x
                eq = Equation(t1, t2)
                # Keep unique up to commutative equality
                key = (t1, t2)
                if key not in seen:
                    seen.add(key)
                    equations.append(eq)
        return equations

    @staticmethod
    def get_duality_mapping(
        attributes: Sequence[Equation],
    ) -> Callable[[Equation], Equation]:
        """Return a duality symmetry mapping for ExplorationBase.

        Maps each equation E to its dual E^op (if present in the attribute set).
        Raises ValueError if attributes are not closed under duality.
        """
        eq_map: dict[Equation, Equation] = {}
        for eq in attributes:
            dual_eq = eq.dual()
            # Find matching dual in attributes using equivalence
            matched = None
            for candidate in attributes:
                if dual_eq.is_equivalent_to(candidate):
                    matched = candidate
                    break
            if matched is None:
                raise ValueError(
                    f"Attribute set is not closed under duality: no dual counterpart found for {eq}. "
                    f"Use ETP.close_under_duality(attributes) to complete the set."
                )
            eq_map[eq] = matched

        def mapping(eq: Equation) -> Equation:
            return eq_map[eq]

        return mapping

    @classmethod
    def close_under_duality(cls, equations: Iterable[Equation]) -> list[Equation]:
        """Ensure a collection of equations is closed under duality."""
        res = list(equations)
        for eq in list(equations):
            dual_eq = eq.dual()
            if not any(dual_eq.is_equivalent_to(existing) for existing in res):
                res.append(dual_eq)
        return res
