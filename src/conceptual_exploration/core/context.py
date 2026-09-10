from collections.abc import MutableSet, Set, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Generic, TypeVar, TextIO, AbstractSet

from .implication import Implication

A = TypeVar("A")
O = TypeVar("O")


@dataclass(slots=True)
class PartialObject(Generic[O, A]):

    object: O

    positive: Set[A]
    negative: Set[A]

    def __post_init__(self):
        overlap: AbstractSet[A] = self.positive & self.negative
        if overlap:
            raise ValueError(
                f'Positive and negative attributes overlap: {overlap}'
            )

    def refutes(
            self,
            implication: Implication[A],
    ) -> bool:
        return (
                implication.premise <= self.positive
                and
                bool(implication.conclusion & self.negative)
        )

    def __str__(self) -> str:
        positive = "{" + ", ".join(map(str, self.positive)) + "}"
        negative = "{" + ", ".join(map(str, self.negative)) + "}"
        return f"{self.object}[{positive}, {negative}]"


class PartialContext(Generic[O, A]):

    def __init__(
            self,
            attributes: Iterable[A],
            objects: Iterable[PartialObject[O, A]] | None = None,
    ) -> None:
        self.attributes = attributes
        self.objects = {o.object: o for o in objects or []}

    def __str__(self) -> str:
        s = "Attributes:\n"
        for a in self.attributes:
            s += f"  {a}\n"
        s += f"Objects:\n"
        for o in self.objects.values():
            s += f"  {o.object}\n"
            s += f"    Positive: {'; '.join(map(str, sorted(o.positive)))}\n"
            s += f"    Negative: {'; '.join(map(str, sorted(o.negative)))}\n"
        return s

    @classmethod
    def from_cxt(
            cls,
            source: str | Path | TextIO,
    ) -> "PartialContext[str, str]":
        close_after_reading = False

        if isinstance(source, str | Path):
            source = open(source, encoding="utf-8")
            close_after_reading = True

        try:
            lines = [line.rstrip("\n") for line in source]
        finally:
            if close_after_reading:
                source.close()

        if not lines or lines[0] != "B":
            raise ValueError("Invalid CXT file: expected first line to be 'B'.")

        try:
            object_count = int(lines[2])
            attribute_count = int(lines[3])
        except (IndexError, ValueError) as error:
            raise ValueError("Invalid CXT file: missing object or attribute count.") from error

        object_start = 5
        attribute_start = object_start + object_count
        incidence_start = attribute_start + attribute_count

        objects = lines[object_start:attribute_start]
        attributes = lines[attribute_start:incidence_start]
        incidence = lines[incidence_start:incidence_start + object_count]

        if len(objects) != object_count:
            raise ValueError("Invalid CXT file: object count does not match object names.")

        if len(attributes) != attribute_count:
            raise ValueError("Invalid CXT file: attribute count does not match attribute names.")

        if len(incidence) != object_count:
            raise ValueError("Invalid CXT file: object count does not match incidence rows.")

        partial_objects: list[PartialObject[str, str]] = []

        for object_name, row in zip(objects, incidence):
            if len(row) != attribute_count:
                raise ValueError(
                    f"Invalid CXT file: incidence row for {object_name!r} "
                    f"has length {len(row)}, expected {attribute_count}."
                )

            positive = set()
            negative = set()

            for attribute, value in zip(attributes, row):
                if value in {"X", "x", "1"}:
                    positive.add(attribute)
                elif value in {".", "0"}:
                    negative.add(attribute)
                elif value == "?":
                    continue
                else:
                    raise ValueError(
                        f"Invalid CXT file: unsupported incidence value {value!r} "
                        f"for object {object_name!r} and attribute {attribute!r}."
                    )

            partial_objects.append(
                PartialObject(object_name, positive, negative)
            )

        return cls(attributes, partial_objects)

    def add(
            self,
            obj: PartialObject[O, A],
    ) -> None:
        if obj.object in self.objects:
            old_obj = self.objects[obj.object]
            new_positive = old_obj.positive | obj.positive
            new_negative = old_obj.negative | obj.negative
            if new_positive & new_negative:
                raise ValueError(
                    f"Object {obj} exists and has conflicting attributes."
                )
            old_obj.positive = new_positive
            old_obj.negative = new_negative
        else:
            self.objects[obj.object] = obj

    def closure(
            self,
            attributes: Set[A],
    ) -> MutableSet[A]:
        result = set(self.attributes)
        for o in self.objects.values():
            if attributes <= o.positive:
                result -= o.negative
        return result