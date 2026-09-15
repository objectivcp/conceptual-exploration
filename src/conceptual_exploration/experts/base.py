from abc import ABC
from abc import abstractmethod

from typing import Generic
from typing import TypeVar

from ..core.context import PartialObject
from ..core.implication import Implication

A = TypeVar("A")
O = TypeVar("O")


class Expert(
    ABC,
    Generic[O, A],
):

    @abstractmethod
    def validate(
            self,
            implication: Implication[A],
            attributes: frozenset[A] | None = None,
    ) -> PartialObject[O, A] | None:
        ...

    def is_conclusive(self) -> bool:
        """Whether the most recent `validate` call actually decided the question.

        An expert whose search can be cut short (e.g. by a solver timeout) returns
        False to signal that finding no counterexample means "undecided" rather
        than "none exists", so the implication is accepted as unconfirmed.
        """
        return True
