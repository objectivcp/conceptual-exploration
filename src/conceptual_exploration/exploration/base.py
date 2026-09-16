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
    # Accepted because the expert found no counterexample, but the expert
    # could not decide the question (e.g. its solver hit a timeout).
    UNCONFIRMED = "unconfirmed"


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
        self.implications = ImplicationTheory[A]()
        self.implication_sources: dict[Implication[A], ImplicationSource] = {}

        for implication in background_implications:
            self.add_background(implication)

    def add_background(self, implication: Implication[A]) -> None:
        self._add_implication(implication, ImplicationSource.BACKGROUND)
        self._add_mapped(implication)

    @property
    def accepted_implications(self) -> tuple[Implication[A], ...]:
        return tuple(
            implication
            for implication in self.implications
            if self.implication_sources[implication] in (
                ImplicationSource.CONFIRMED,
                ImplicationSource.UNCONFIRMED,
            )
        )

    @property
    def unconfirmed_implications(self) -> tuple[Implication[A], ...]:
        """Accepted implications the expert could not actually decide."""
        return tuple(
            implication
            for implication in self.implications
            if self.implication_sources[implication] == ImplicationSource.UNCONFIRMED
        )

    def accept(
            self,
            implication: Implication[A],
            source: ImplicationSource = ImplicationSource.CONFIRMED,
    ) -> None:
        self._add_implication(implication, source)
        self._add_mapped(implication)

    def _add_mapped(self, implication: Implication[A]) -> None:
        """Add the images of an implication under the symmetry mappings.

        Keeping the theory closed under the mappings is what lets a mapped copy
        of a completed object be completed itself, so background implications
        are mapped for the same reason confirmed ones are.
        """
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
        """Merge an observation into what is already known, complete it under
        the implications, and store it; return the object the context holds.

        Takes ownership of `example`, whose attribute sets are replaced with the
        merged and completed ones. Merging comes first because an attribute
        derivable from the union need not be derivable from either observation
        alone, and nothing is stored until completion succeeds, so a conflicting
        observation leaves the context as it was rather than half-absorbed.
        """
        stored = self.context.objects.get(example.object)
        if stored is not None:
            example.positive = example.positive | stored.positive
            example.negative = example.negative | stored.negative

        self._update_object(example)
        return self.context.add(example)

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
        """Complete an object's attribute sets under the current implications.

        Raises ValueError if the implications force an attribute the object is
        known not to have. Completing the positive side is what can produce that
        clash, so the check lives here, where the closure is computed anyway.
        """
        positive = self.implications.closure(obj.positive)
        if positive & obj.negative:
            raise ValueError(f"Implications conflict with object: {obj}")

        obj.positive = positive
        changed = True
        new_negative = set(obj.negative)
        while changed:
            changed = False
            for a in set(self.attributes) - obj.positive - new_negative:
                if self.implications.closure(obj.positive | {a}) & new_negative:
                    changed = True
                    new_negative.add(a)
        obj.negative = new_negative

    def _add_implication(
            self,
            implication: Implication[A],
            source: ImplicationSource,
    ) -> None:
        self.implications.add(implication)
        self.implication_sources[implication] = source
        self._update()

