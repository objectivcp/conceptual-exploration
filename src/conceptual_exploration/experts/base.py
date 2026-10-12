from abc import ABC
from abc import abstractmethod
from dataclasses import dataclass

from typing import Generic
from typing import TypeVar

from ..core.context import PartialObject
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True, slots=True)
class Undecided(Generic[O, A]):
    """An expert's answer when it can neither confirm nor refute a question.

    `proved` is the part of the conclusion the expert did confirm, which the
    exploration accepts. The rest becomes an open question or, if
    `unconfirmed`, is accepted as unconfirmed: an expert sets it when it knows
    nothing against the rest, and leaves it unset when it knows the rest to be
    false without knowing which attribute fails. `object` is what the expert
    knows of an object that may refute the implication: a partial row, added
    to the context in the hope that completion later decides it. It must not
    refute the question.
    """

    proved: frozenset[A] = frozenset()
    object: PartialObject[O, A] | None = None
    unconfirmed: bool = False


class Expert(
    ABC,
    Generic[O, A],
):

    @abstractmethod
    def validate(
            self,
            implication: Implication[A],
            attributes: frozenset[A] | None = None,
    ) -> PartialObject[O, A] | Undecided[O, A] | None:
        """A counterexample, None to accept the implication, or Undecided."""
        ...

    def is_conclusive(self) -> bool:
        """Whether the most recent `validate` call actually decided the question.

        An expert whose search can be cut short (e.g. by a solver timeout) returns
        False to signal that finding no counterexample means "undecided" rather
        than "none exists", so the implication is accepted as unconfirmed.
        """
        return True
