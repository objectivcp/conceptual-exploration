from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import TypeVar, Generic, Iterable

from ..core.context import PartialContext, PartialObject
from ..core.implication import Implication
from ..core.theory import ImplicationTheory

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True, slots=True)
class VersionedObject(Generic[O]):
    original: O
    version: int

    def __str__(self) -> str:
        return f"{self.original}#{self.version}"


class ImplicationSource(Enum):
    BACKGROUND = "background"
    CONFIRMED = "confirmed"
    MAPPED = "mapped"


class ExplorationBase(Generic[O, A]):

    def __init__(
            self,
            attributes: Iterable[A],
            background_implications: Iterable[Implication[A]] = (),
            mappings: Iterable[Callable[[A], A]] = ()
    ) -> None:
        self.attributes = tuple(attributes)
        self.context = PartialContext[VersionedObject[O], A](attributes)
        self.mappings = tuple(mappings)
        self.implications = ImplicationTheory[A](background_implications)
        self.implication_sources: dict[Implication[A], ImplicationSource] = {
            implication: ImplicationSource.BACKGROUND
            for implication in background_implications
        }

    def add_background(self, implication: Implication[A]) -> None:
        self._add_implication(implication, ImplicationSource.BACKGROUND)

    @property
    def accepted_implications(self) -> tuple[Implication[A], ...]:
        return tuple(
            implication
            for implication in self.implications
            if self.implication_sources[implication] == ImplicationSource.CONFIRMED
        )

    def accept(self, implication: Implication[A]) -> None:
        self._add_implication(implication, ImplicationSource.CONFIRMED)
        for mapping in self.mappings:
            mapped_implication = Implication(
                frozenset(mapping(a) for a in implication.premise),
                frozenset(mapping(a) for a in implication.conclusion)
            )
            if not self.implications.entails(mapped_implication):
                self._add_implication(
                    mapped_implication,
                    ImplicationSource.MAPPED
                )

    def add_counterexample(self, example: PartialObject[O, A]) -> None:
        obj = self._add_object(
            PartialObject(
                VersionedObject(example.object, 0),
                example.positive,
                example.negative
            )
        )
        for version, mapping in enumerate(self.mappings, start=1):
            self._add_object(
                self._make_version(
                    obj,
                    mapping,
                    version
                )
            )

    def _add_object(self, example: PartialObject[VersionedObject[O], A]):
        obj = PartialObject(
            example.object,
            example.positive,
            example.negative
        )
        self._update_object(obj)
        if self.implications.closure(obj.positive) & obj.negative:
            raise ValueError(f"Implications conflict with object: {obj}")
        self.context.add(obj)
        return obj

    def _make_version(
            self,
            example: PartialObject[VersionedObject[O], A],
            mapping: Callable[[A], A],
            version: int
    ) -> PartialObject[O, A]:

        return PartialObject(
            VersionedObject(example.object.original, version),
            set(a for a in self.attributes if mapping(a) in example.positive),
            set(a for a in self.attributes if mapping(a) in example.negative)
        )

    def _update(self):
        for obj in self.context.objects.values():
            self._update_object(obj)

    def _update_object(self, obj: PartialObject[O, A]):
        obj.positive = self.implications.closure(obj.positive)
        changed = True
        new_negative = set(obj.negative)
        while changed:
            changed = False
            for a in set(self.attributes) - obj.positive - new_negative:
                if self.implications.closure(obj.positive | {a}) & new_negative:
                    changed = True
                    new_negative.add(a)
        obj.negative = new_negative
        assert len(obj.positive & obj.negative) == 0

    def _add_implication(
            self,
            implication: Implication[A],
            source: ImplicationSource,
    ) -> None:
        self.implications.add(implication)
        self.implication_sources[implication] = source
        self._update()

