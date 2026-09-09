from abc import ABC
from abc import abstractmethod

from typing import Generic
from typing import TypeVar

from core.partial_object import PartialObject
from core.implication import Implication

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