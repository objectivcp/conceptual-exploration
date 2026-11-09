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
    exploration accepts. The rest is accepted as unconfirmed, the expert
    knowing nothing against it, or, if `rejected`, known false as a whole
    without the expert knowing which attribute fails. An expert that knows
    a single attribute to fail returns a counterexample instead, a partial
    object with the premise and without that attribute if need be. `object`
    is what the expert knows of an object that may refute the implication: a
    partial row, added to the context in the hope that completion later
    decides it. It must not refute the question.
    """

    proved: frozenset[A] = frozenset()
    object: PartialObject[O, A] | None = None
    rejected: bool = False


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

    def new_objects(self) -> list[PartialObject[O, A]]:
        """Objects the expert has come to know besides its answers and has
        not given before, such as the other candidates of a search; the
        exploration adds them to the context after each answer. An object
        given again under the same name merges into the one given before.
        """
        return []
