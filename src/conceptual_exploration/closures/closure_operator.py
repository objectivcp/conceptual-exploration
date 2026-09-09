from abc import abstractmethod
from collections.abc import MutableSet, Set
from typing import Protocol, TypeVar

A = TypeVar("A")


class ClosureOperator(Protocol[A]):

    @abstractmethod
    def closure(self, attributes: Set[A]) -> MutableSet[A]:
        ...
