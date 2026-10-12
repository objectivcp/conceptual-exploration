from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import TypeVar, Generic, Iterable

from ..core.bitset import AttributeIndex, bits
from ..core.context import PartialContext, PartialObject
from ..core.implication import Implication
from ..core.theory import ImplicationTheory
from ..core.truth import Truth

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
    """The implications and objects an exploration has gathered so far.

    `implications` and `context` are the public, set-based record. Alongside
    them the base keeps every object as a pair of bitmasks over `index`, and
    the exploration loop works on those: completing objects, closing premises
    in the context, and applying the mappings all become integer operations.
    The masks are the base's own copy of the context it manages, so objects
    have to be added through `add_counterexample`, not `context.add`.

    Each implication and each object is mapped by each mapping once, never by
    a composition of them, so the mappings should be closed under
    composition: a group of symmetries, or all substitutions of variables.

    Objects are completed only with the trusted implications: background,
    confirmed and their images. An unconfirmed implication may be false, and
    completing with it could put a false value into a row; it still takes part
    in `implications` and so in choosing the questions. An object that turns
    out to violate one is recorded in `refuted` rather than rejected.
    `open_questions` collects the questions the expert left undecided.
    """

    def __init__(
            self,
            attributes: Iterable[A],
            background_implications: Iterable[Implication[A]] = (),
            mappings: Iterable[Callable[[A], A]] = ()
    ) -> None:
        self.attributes = tuple(attributes)
        self.index = AttributeIndex[A](self.attributes)
        self.full_mask = (1 << len(self.attributes)) - 1
        self.context = PartialContext[VersionedObject[O], A](self.attributes)
        self.mappings = tuple(mappings)
        # For each mapping, the image bit of attribute i at position i (0 if
        # the image is a truth value), and the attributes it sends to true
        # and to false; a mapping is called once per attribute rather than on
        # every use.
        self._mapping_tables: list[list[int]] = [[] for _ in self.mappings]
        self._true_masks: list[int] = [0] * len(self.mappings)
        self._false_masks: list[int] = [0] * len(self.mappings)
        for k in range(len(self.mappings)):
            self._extend_table(k, len(self.attributes))
        self.implications = ImplicationTheory[A](index=self.index)
        self.implication_sources: dict[Implication[A], ImplicationSource] = {}
        # The implications objects are completed with, and the masks of the
        # others, checked against every stored row.
        self._trusted = ImplicationTheory[A](index=self.index)
        self._untrusted: dict[Implication[A], tuple[int, int]] = {}
        self.refuted: dict[Implication[A], VersionedObject[O]] = {}
        # The implication each mapped image was mapped from.
        self._origins: dict[Implication[A], Implication[A]] = {}
        self.open_questions: list[Implication[A]] = []
        self._rows: dict[VersionedObject[O], tuple[int, int]] = {}
        # The objects sharing each distinct row. Many versions of an object
        # repeat a row under another name, and the context closure and the
        # updates only need each row once.
        self._names_by_row: dict[tuple[int, int], dict[VersionedObject[O], None]] = {}
        # The distinct rows transposed for the context closure: each row has
        # a bit, and each attribute (by position) a mask of the rows that
        # have it and of the rows that deny it.
        self._row_bits: dict[tuple[int, int], int] = {}
        self._next_row_bit = 1
        self._live_rows = 0
        self._rows_with: dict[int, int] = {}
        self._rows_without: dict[int, int] = {}

        for implication in background_implications:
            self.add_background(implication)

    def add_background(self, implication: Implication[A]) -> None:
        self.accept(implication, ImplicationSource.BACKGROUND)

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
        """Add an implication and its images under the mappings, then bring
        the objects up to date with all of them at once.

        Raises ValueError if the new implications conflict with an object.

        An implication the theory already holds, such as a background
        implication added before as the image of another, only takes on the
        new source. It is not mapped again either: it is the original or an
        image of one that was mapped, and with the mappings closed under
        composition its images are images of that original, which the theory
        already holds or entails. A background made of whole orbits is thus
        mapped once per orbit rather than once per implication.
        """
        trusted = source is not ImplicationSource.UNCONFIRMED
        if implication in self.implication_sources:
            self.implication_sources[implication] = source
            if trusted and implication in self._untrusted:
                masks = self._untrusted.pop(implication)
                self._trusted.add(implication)
                self._update([masks, *self._add_mapped(*masks, trusted)])
                for other, other_masks in list(self._untrusted.items()):
                    if self._trusted.entails_mask(*other_masks):
                        del self._untrusted[other]
            return
        masks = self._add_implication(implication, source, trusted)
        added = self._add_mapped(*masks, trusted, implication)
        if trusted:
            self._update([masks, *added])

    def origin(self, implication: Implication[A]) -> Implication[A]:
        """The implication accepted or given as background that `implication`
        is, or is an image of."""
        return self._origins.get(implication, implication)

    def _add_mapped(
            self,
            premise: int,
            conclusion: int,
            trusted: bool = True,
            origin: Implication[A] | None = None,
    ) -> list[tuple[int, int]]:
        """Add the images of an implication under the symmetry mappings and
        return the masks of those the trusted implications did not entail
        already, if the implication is trusted itself.

        Keeping the theory closed under the mappings is what lets a mapped copy
        of a completed object be completed itself, so background implications
        are mapped for the same reason confirmed ones are. The image of an
        unconfirmed implication is no more trustworthy than the implication.
        """
        added = []
        for mapped_premise, mapped_conclusion in self.mapped_images(premise, conclusion):
            mapped_implication = Implication(
                self.index.decode(mapped_premise),
                self.index.decode(mapped_conclusion),
            )
            if not self.implications.entails_mask(mapped_premise, mapped_conclusion):
                masks = self._add_implication(mapped_implication, ImplicationSource.MAPPED, trusted)
                if origin is not None:
                    self._origins[mapped_implication] = origin
                if trusted:
                    added.append(masks)
            elif trusted and not self._trusted.entails_mask(mapped_premise, mapped_conclusion):
                added.append(self._trusted.add(mapped_implication))
        return added

    def mapped_images(self, premise: int, conclusion: int) -> list[tuple[int, int]]:
        """The masks of an implication's images under the mappings.

        An attribute sent to true drops out of either side. One sent to false
        makes a premise unsatisfiable, so that image says nothing and is left
        out; in the conclusion it means the premise image cannot hold, so the
        image concludes every attribute.
        """
        images = []
        for k in range(len(self.mappings)):
            mapped_premise = self._image(k, premise)
            mapped_conclusion = self._image(k, conclusion)
            if premise & self._false_masks[k]:
                continue
            if conclusion & self._false_masks[k]:
                mapped_conclusion = self.full_mask
            images.append((mapped_premise, mapped_conclusion))
        return images

    def _extend_table(self, k: int, length: int) -> None:
        """Tabulate mapping k on the first `length` indexed attributes.

        A mapping may send an attribute outside `attributes`, which gives the
        image a new bit; implications mentioning it are mapped in turn, so the
        tables grow with the index rather than being fixed at construction.
        """
        table = self._mapping_tables[k]
        while len(table) < length:
            i = len(table)
            image = self.mappings[k](self.index.attributes[i])
            if image is Truth.TRUE:
                self._true_masks[k] |= 1 << i
                table.append(0)
            elif image is Truth.FALSE:
                self._false_masks[k] |= 1 << i
                table.append(0)
            else:
                table.append(self.index.bit(image))

    def _image(self, k: int, mask: int) -> int:
        self._extend_table(k, mask.bit_length())
        table = self._mapping_tables[k]
        image = 0
        for i in bits(mask):
            image |= table[i]
        return image

    def _preimage(self, k: int, mask: int) -> int:
        """The attributes whose images under mapping k are attributes in
        `mask`."""
        preimage = 0
        for i, image in enumerate(self._mapping_tables[k][:len(self.attributes)]):
            if image & mask:
                preimage |= 1 << i
        return preimage

    def add_counterexample(self, example: PartialObject[O, A]) -> None:
        """Add a counterexample along with its images under the mappings.

        An image that repeats one already added is skipped. A non-injective
        mapping can send an object onto an earlier version of itself — with
        x = y = z every substitution grounds to the same object, so all its
        images coincide — and such a copy constrains nothing its twin does not
        while costing time in every later closure. A version the context
        already holds is re-added even so, to keep it in step with the object
        it is derived from. Versions are numbered by mapping rather than
        consecutively, so that a second sighting of the same object merges into
        the images of the first. An attribute the mapping sends to a truth
        value has that value in every version.
        """
        original = example.object
        row = self._add_row(
            VersionedObject(original, 0),
            self.index.encode(example.positive),
            self.index.encode(example.negative),
        )
        seen = {row}
        for k in range(len(self.mappings)):
            name = VersionedObject(original, k + 1)
            copy = (
                self._preimage(k, row[0]) | self._true_masks[k] & self.full_mask,
                self._preimage(k, row[1]) | self._false_masks[k] & self.full_mask,
            )
            if copy in seen and name not in self._rows:
                continue
            seen.add(copy)
            self._add_row(name, *copy)

    def _add_row(
            self,
            name: VersionedObject[O],
            positive: int,
            negative: int,
    ) -> tuple[int, int]:
        """Merge an observation into what is already known, complete it under
        the implications, and store it; return the stored masks.

        Merging comes first because an attribute derivable from the union need
        not be derivable from either observation alone, and nothing is stored
        until completion succeeds, so a conflicting observation leaves the
        context as it was rather than half-absorbed. The stored object gets
        sets of its own, never the ones the expert handed over.
        """
        stored = self._rows.get(name)
        if stored is not None:
            positive |= stored[0]
            negative |= stored[1]

        row = self._complete(positive, negative, name)
        self._store(name, row)
        return row

    def _set_row(self, name: VersionedObject[O], row: tuple[int, int]) -> None:
        old = self._rows.get(name)
        if old is not None:
            names = self._names_by_row[old]
            del names[name]
            if not names:
                del self._names_by_row[old]
                self._forget_row(old)
        self._rows[name] = row
        if row not in self._names_by_row:
            self._names_by_row[row] = {}
            self._register_row(row)
        self._names_by_row[row][name] = None

    def _register_row(self, row: tuple[int, int]) -> None:
        bit = self._next_row_bit
        self._next_row_bit <<= 1
        self._row_bits[row] = bit
        self._live_rows |= bit
        positive, negative = row
        for position in bits(positive):
            self._rows_with[position] = self._rows_with.get(position, 0) | bit
        for position in bits(negative):
            self._rows_without[position] = self._rows_without.get(position, 0) | bit

    def _forget_row(self, row: tuple[int, int]) -> None:
        bit = self._row_bits.pop(row)
        self._live_rows &= ~bit
        positive, negative = row
        for position in bits(positive):
            self._rows_with[position] &= ~bit
        for position in bits(negative):
            self._rows_without[position] &= ~bit

    def _store(self, name: VersionedObject[O], row: tuple[int, int]) -> None:
        self._set_row(name, row)
        for implication, masks in self._untrusted.items():
            self._check_untrusted(implication, masks, name, *row)
        obj = self.context.objects.get(name)
        if obj is None:
            self.context.add(
                PartialObject(name, self.index.decode(row[0]), self.index.decode(row[1]))
            )
        else:
            obj.positive = self.index.decode(row[0])
            obj.negative = self.index.decode(row[1])

    def context_closure_mask(self, attributes: int) -> int:
        """The attributes every object having `attributes` might have: the
        mask form of `context.closure`."""
        rows = self._live_rows
        for position in bits(attributes):
            rows &= self._rows_with.get(position, 0)
            if not rows:
                return self.full_mask
        result = self.full_mask
        for position, denying in self._rows_without.items():
            if denying & rows:
                result &= ~(1 << position)
        return result

    def _update(self, added: list[tuple[int, int]]) -> None:
        """Bring the objects up to date after `added` joined the theory.

        Every stored object is closed under the theory it was completed by, so
        its positive side can only grow where one of the new implications
        fires, and a complete object has no unknown attribute for the negative
        side to claim; such objects are left alone. A firing implication on a
        complete object can only be a conflict, which `_complete` reports.
        Objects sharing a row are completed once, together.
        """
        if not added:
            return
        for (positive, negative), names in list(self._names_by_row.items()):
            fires = any(
                premise & positive == premise and conclusion & ~positive
                for premise, conclusion in added
            )
            if not fires and (positive | negative) & self.full_mask == self.full_mask:
                continue
            row = self._complete(positive, negative, next(iter(names)))
            if row != (positive, negative):
                for name in list(names):
                    self._store(name, row)

    def _update_object(self, obj: PartialObject[O, A]):
        """Complete an object's attribute sets under the current implications.

        Raises ValueError if the implications force an attribute the object is
        known not to have.
        """
        positive, negative = self._complete(
            self.index.encode(obj.positive),
            self.index.encode(obj.negative),
            obj.object,
        )
        obj.positive = self.index.decode(positive)
        obj.negative = self.index.decode(negative)
        if self.context.objects.get(obj.object) is obj:
            self._set_row(obj.object, (positive, negative))

    def _complete(self, positive: int, negative: int, name) -> tuple[int, int]:
        """Close the positive side, then deny every attribute that would force
        a denied one.

        Completing the positive side is what can clash with the negative one,
        so the check lives here, where the closure is computed anyway.
        """
        closure = self._trusted.closure_mask
        positive = closure(positive)
        if positive & negative:
            raise ValueError(
                f"Implications conflict with object {name}: "
                f"{self.index.decode(positive & negative)}"
            )
        changed = True
        while changed:
            changed = False
            for i in bits(self.full_mask & ~positive & ~negative):
                bit = 1 << i
                if closure(positive | bit) & negative:
                    negative |= bit
                    changed = True
        return positive, negative

    def _add_implication(
            self,
            implication: Implication[A],
            source: ImplicationSource,
            trusted: bool = True,
    ) -> tuple[int, int]:
        """Record an implication in the theory without touching the objects;
        return its masks."""
        self.implication_sources[implication] = source
        masks = self.implications.add(implication)
        if not trusted:
            self._untrusted[implication] = masks
            for name, (positive, negative) in self._rows.items():
                self._check_untrusted(implication, masks, name, positive, negative)
        else:
            self._trusted.add(implication)
        return masks

    def _check_untrusted(self, implication, masks, name, positive: int, negative: int) -> None:
        premise, conclusion = masks
        if premise & positive == premise and conclusion & negative and implication not in self.refuted:
            self.refuted[implication] = name
