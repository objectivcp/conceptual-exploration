from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum

from .variable import Sort


class Notation(Enum):
    FUNCTIONAL = 1
    INFIX = 2
    POSTFIX = 3


@dataclass(frozen=True, slots=True)
class Predicate:
    name: str
    arity: int
    sorts : tuple[Sort, ...] | None = field(default=None, kw_only=True)
    notation: Notation = field(
        default=Notation.FUNCTIONAL,
        kw_only=True
    )
    # Properties of a binary predicate that the exploration can rely on
    # without asking: it keeps one atom of each symmetric pair, and fixes the
    # truth of P(v, v) for reflexive and irreflexive predicates. `complement`
    # names a predicate that holds exactly where this one does not.
    symmetric: bool = field(default=False, kw_only=True)
    reflexive: bool = field(default=False, kw_only=True)
    irreflexive: bool = field(default=False, kw_only=True)
    complement: str | None = field(default=None, kw_only=True)

    def __post_init__(self):
        if (self.symmetric or self.reflexive or self.irreflexive) and self.arity != 2:
            raise ValueError(
                f"Predicate {self.name} has arity {self.arity}; only binary "
                f"predicates can be symmetric, reflexive or irreflexive"
            )
        if self.reflexive and self.irreflexive:
            raise ValueError(f"Predicate {self.name} cannot be both reflexive and irreflexive")
        if self.symmetric and self.sorts and self.sorts[0] != self.sorts[1]:
            raise ValueError(
                f"Predicate {self.name} relates different sorts, so it cannot be symmetric"
            )

    def format(self, arguments):
        if self.notation is Notation.INFIX:
            return f" {self.name} ".join(map(str, arguments))

        args = ", ".join(map(str, arguments))
        if self.notation is Notation.POSTFIX:
            return f"{args} {self.name}"

        return f"{self.name}({args})"

    def valid_arguments(self, arguments):
        if len(arguments) != self.arity:
            return False
        if self.sorts:
            for i, s in enumerate(self.sorts):
                if s is not None and arguments[i].sort != s:
                    return False
        return True

    def __str__(self) -> str:
        return self.name

    def __lt__(self, other: "Predicate") -> bool:
        if not isinstance(other, Predicate):
            return NotImplemented
        return (self.name, self.arity) < (other.name, other.arity)


@dataclass(frozen=True, slots=True)
class EvaluatablePredicate(Predicate):
    function: Callable[..., bool] = field(kw_only=True)

    def __call__(self, *args) -> bool:
        if len(args) != self.arity:
            raise ValueError(f"Expected {self.arity} arguments, got {len(args)}")
        return self.function(*args)