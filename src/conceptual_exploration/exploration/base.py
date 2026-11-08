from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import TypeVar, Generic, Iterable

from ..core.bitset import AttributeIndex, bits
from ..core.context import PartialContext, PartialObject
from ..core.implication import Implication
from ..core.theory import ImplicationTheory, close_mask
from ..core.truth import Truth

A = TypeVar("A")
O = TypeVar("O")


@dataclass(frozen=True, slots=True)
class VersionedObject(Generic[O]):
    original: O
    version: int

    def __str__(self) -> str:
        return f"{self.original}#{self.version}"


@dataclass(frozen=True, slots=True)
class JointConflict(Generic[O, A]):
    """Unconfirmed implications that, with the trusted ones, contradict the
    objects or rejected implications in `contradicted` only together: none
    of them does on its own, and without any one of them the others do not
    either. One of them is false, but which is not known."""

    implications: tuple[Implication[A], ...]
    contradicted: tuple[VersionedObject[O] | Implication[A], ...]


class ImplicationSource(Enum):
    BACKGROUND = "background"
    CONFIRMED = "confirmed"
    MAPPED = "mapped"
    # Accepted because the expert found no counterexample, but the expert
    # could not decide the question (e.g. its solver hit a timeout).
    UNCONFIRMED = "unconfirmed"
    # An image of an unconfirmed implication, no more certain than it; it
    # becomes MAPPED when that implication is confirmed.
    MAPPED_UNCONFIRMED = "mapped unconfirmed"


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
    in `implications` and so in choosing the questions. With
    `map_unconfirmed` false, unconfirmed implications are not mapped until
    they are confirmed, so that their images are asked about in turn; an
    unconfirmed implication that the trusted ones come to entail, such as the
    image of a confirmed one, is then recorded as confirmed.
    `rejected_implications` collects the implications the expert showed false
    as a whole without knowing which attribute of the conclusion fails. They
    are facts, as the objects are.

    Each unconfirmed implication, with its images if they are mapped, must
    hold together with the trusted implications: it must not contradict an
    object or entail a rejected implication. One that does is recorded in
    `refuted`, with the object or the rejected implication, whenever an
    object, a trusted implication or a rejected one comes in. Unconfirmed
    implications that contradict an object or a rejected implication only
    together are allowed: which of them is false is not known.
    """

    def __init__(
            self,
            attributes: Iterable[A],
            background_implications: Iterable[Implication[A]] = (),
            mappings: Iterable[Callable[[A], A]] = (),
            map_unconfirmed: bool = True,
    ) -> None:
        self.attributes = tuple(attributes)
        self.map_unconfirmed = map_unconfirmed
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
        # Each refuted unconfirmed implication (the one accepted, not an
        # image), with the object or the rejected implication refuting it.
        self.refuted: dict[Implication[A], VersionedObject[O] | Implication[A]] = {}
        # The implication each mapped image was mapped from.
        self._origins: dict[Implication[A], Implication[A]] = {}
        self.rejected_implications: list[Implication[A]] = []
        self._rows: dict[VersionedObject[O], tuple[int, int]] = {}
        # The objects sharing each distinct row. Many versions of an object
        # repeat a row under another name, and the context closure and the
        # updates only need each row once.
        self._names_by_row: dict[tuple[int, int], dict[VersionedObject[O], None]] = {}
        # The distinct rows transposed for the context closure: each row has
        # a bit, and each attribute (by position) a mask of the rows that
        # have it and of the rows that deny it.
        self._row_bits: dict[tuple[int, int], int] = {}
        self._rows_by_bit: dict[int, tuple[int, int]] = {}
        self._next_row_bit = 1
        self._live_rows = 0
        # The rows with an unknown attribute.
        self._partial_rows = 0
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

    @property
    def trusted_implications(self) -> ImplicationTheory[A]:
        """The trusted implications: the background, the confirmed
        implications and their images, those the objects are completed
        with. Not to be modified."""
        return self._trusted

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
                for image, origin in self._origins.items():
                    if origin == implication and self.implication_sources[image] is ImplicationSource.MAPPED_UNCONFIRMED:
                        self.implication_sources[image] = ImplicationSource.MAPPED
                self._settle_untrusted()
                self._check_untrusted_after_trusted()
            return
        masks = self._add_implication(implication, source, trusted)
        added = self._add_mapped(*masks, trusted, implication) if trusted or self.map_unconfirmed else []
        if trusted:
            self._update([masks, *added])
            if not self.map_unconfirmed:
                self._settle_untrusted()
            self._check_untrusted_after_trusted()
        else:
            self._check_untrusted_implication(implication)

    def _settle_untrusted(self) -> None:
        """Trust the untrusted implications that the trusted ones entail.

        Without mapping unconfirmed implications, one of them is entailed
        this way when its image is confirmed, and since the mappings are
        symmetries it is then true itself, so it is recorded as confirmed.
        """
        for other, other_masks in list(self._untrusted.items()):
            if self._trusted.entails_mask(*other_masks):
                del self._untrusted[other]
                if not self.map_unconfirmed and self.implication_sources[other] is ImplicationSource.UNCONFIRMED:
                    self.implication_sources[other] = ImplicationSource.CONFIRMED

    @property
    def open_questions(self) -> list[Implication[A]]:
        """The former name of `rejected_implications`."""
        return self.rejected_implications

    def reject(self, implication: Implication[A]) -> None:
        """Record an implication shown false as a whole without a
        counterexample."""
        if implication in self.rejected_implications:
            return
        self.rejected_implications.append(implication)
        masks = self._masks(implication)
        for origin, group in self._untrusted_groups().items():
            self._check_against_rejected(origin, group, implication, masks)

    def known_false(self, implication: Implication[A]) -> bool:
        """Whether the trusted knowledge shows `implication` false; see
        `known_false_mask`."""
        return self.known_false_mask(*self._masks(implication))

    def known_false_mask(self, premise: int, conclusion: int) -> bool:
        """Whether the implication, with its images and the trusted
        implications, contradicts an object or entails a rejected
        implication.

        The images count whether or not unconfirmed implications are mapped:
        an implication whose image is false is false itself. So does a
        preimage of a rejected implication, which needs no check of its own:
        if the implication entails one, applying the mapping shows that it
        entails the rejected implication itself, the trusted implications and
        the images being closed under the mappings.

        Only the objects certainly having the premise of the implication or
        of an image can be contradicted. A complete one is closed under the
        trusted implications, so it is contradicted only if one of these
        refutes it directly; a partial one needs the closure.
        """
        extra = [(premise, conclusion), *self.mapped_images(premise, conclusion)]
        for p, c in extra:
            rows = self._rows_having(p)
            complete = rows & ~self._partial_rows
            if complete and any(complete & self._rows_without.get(i, 0) for i in bits(c)):
                return True
            for position in bits(rows & self._partial_rows):
                positive, negative = self._rows_by_bit[1 << position]
                if self._closure_with(positive, extra) & negative:
                    return True
        for rejected in self.rejected_implications:
            p, c = self._masks(rejected)
            if self._closure_with(p, extra) & c == c:
                return True
        return False

    def joint_conflicts(self) -> list[JointConflict[O, A]]:
        """The sets of unconfirmed implications that contradict an object or
        a rejected implication only together, each with what it contradicts.

        For each partial object and rejected implication that all
        implications together contradict, the unconfirmed implications
        (each with its images, if they are mapped) are dropped one at a
        time, in the order they were accepted, as long as the rest still
        contradict it; what is left is a minimal set. A complete object
        contradicted by the implications together is refuted by one of
        them, which `refuted` records instead. Objects or rejected
        implications contradicted by the same set are reported together.
        """
        groups = self._untrusted_groups()
        if not groups:
            return []
        order = {implication: n for n, implication in enumerate(self.implications.implications)}
        origins = sorted(groups, key=lambda i: order.get(i, len(order)))

        def minimal(contradicts) -> tuple[Implication[A], ...]:
            kept = list(origins)
            for origin in origins:
                rest = [o for o in kept if o != origin]
                if contradicts([masks for o in rest for masks in groups[o]]):
                    kept = rest
            return tuple(kept)

        found: dict[tuple[Implication[A], ...], list] = {}
        for position in bits(self._partial_rows):
            row = self._rows_by_bit[1 << position]
            positive, negative = row
            if self.implications.closure_mask(positive) & negative:
                key = minimal(lambda extra: self._closure_with(positive, extra) & negative)
                names = list(self._names_by_row[row])
                found.setdefault(key, []).append(next((n for n in names if n.version == 0), names[0]))
        for rejected in self.rejected_implications:
            premise, conclusion = self._masks(rejected)
            if self.implications.closure_mask(premise) & conclusion == conclusion:
                key = minimal(lambda extra: self._closure_with(premise, extra) & conclusion == conclusion)
                found.setdefault(key, []).append(rejected)
        return [JointConflict(key, tuple(contradicted)) for key, contradicted in found.items()]

    def earliest_refuted(self) -> tuple[Implication[A], VersionedObject[O] | Implication[A]] | None:
        """The refuted unconfirmed implication accepted first, with what
        refutes it, or None. Dropping it and those accepted after it leaves
        none refuted."""
        if not self.refuted:
            return None
        order = {implication: n for n, implication in enumerate(self.implications.implications)}
        implication = min(self.refuted, key=lambda i: order.get(i, len(order)))
        return implication, self.refuted[implication]

    def _masks(self, implication: Implication[A]) -> tuple[int, int]:
        return self.index.encode(implication.premise), self.index.encode(implication.conclusion)

    def _closure_with(self, mask: int, extra: list[tuple[int, int]]) -> int:
        """The closure of `mask` under the trusted implications and `extra`."""
        while True:
            mask = self._trusted.closure_mask(mask)
            grown = close_mask(mask, extra)
            if grown == mask:
                return mask
            mask = grown

    def _rows_having(self, attributes: int) -> int:
        """The bits of the rows certainly having `attributes`."""
        rows = self._live_rows
        for position in bits(attributes):
            rows &= self._rows_with.get(position, 0)
            if not rows:
                break
        return rows

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
        unconfirmed implication is no more trustworthy than the implication,
        and is recorded as MAPPED_UNCONFIRMED. The image of a trusted one that
        the theory entails only with the help of unconfirmed implications is
        recorded as well, so that the trusted implications recorded stay
        closed under the mappings.
        """
        source = ImplicationSource.MAPPED if trusted else ImplicationSource.MAPPED_UNCONFIRMED
        added = []
        for mapped_premise, mapped_conclusion in self.mapped_images(premise, conclusion):
            mapped_implication = Implication(
                self.index.decode(mapped_premise),
                self.index.decode(mapped_conclusion),
            )
            if not self.implications.entails_mask(mapped_premise, mapped_conclusion):
                masks = self._add_implication(mapped_implication, source, trusted)
                if origin is not None:
                    self._origins[mapped_implication] = origin
                if trusted:
                    added.append(masks)
            elif trusted and not self._trusted.entails_mask(mapped_premise, mapped_conclusion):
                if mapped_implication in self.implication_sources:
                    added.append(self._trusted.add(mapped_implication))
                else:
                    added.append(self._add_implication(mapped_implication, source, trusted))
                    if origin is not None:
                        self._origins[mapped_implication] = origin
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
        self._rows_by_bit[bit] = row
        self._live_rows |= bit
        positive, negative = row
        if self._partial(positive, negative):
            self._partial_rows |= bit
        for position in bits(positive):
            self._rows_with[position] = self._rows_with.get(position, 0) | bit
        for position in bits(negative):
            self._rows_without[position] = self._rows_without.get(position, 0) | bit

    def _forget_row(self, row: tuple[int, int]) -> None:
        bit = self._row_bits.pop(row)
        del self._rows_by_bit[bit]
        self._live_rows &= ~bit
        self._partial_rows &= ~bit
        positive, negative = row
        for position in bits(positive):
            self._rows_with[position] &= ~bit
        for position in bits(negative):
            self._rows_without[position] &= ~bit

    def _store(self, name: VersionedObject[O], row: tuple[int, int]) -> None:
        self._set_row(name, row)
        for origin, group in self._untrusted_groups().items():
            self._check_against_row(origin, group, name, *row)
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
        rows = self._rows_having(attributes)
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
        else:
            self._trusted.add(implication)
        return masks

    def _partial(self, positive: int, negative: int) -> bool:
        return (positive | negative) & self.full_mask != self.full_mask

    def _untrusted_groups(self) -> dict[Implication[A], list[tuple[int, int]]]:
        """The masks of the untrusted implications, by the implication each
        is or is an image of."""
        groups: dict[Implication[A], list[tuple[int, int]]] = {}
        for implication, masks in self._untrusted.items():
            groups.setdefault(self.origin(implication), []).append(masks)
        return groups

    def _check_untrusted_implication(self, implication: Implication[A]) -> None:
        """Check a newly accepted unconfirmed implication, with its images,
        against every object and rejected implication."""
        group = self._untrusted_groups().get(implication)
        if group is None:
            return
        for row, names in self._names_by_row.items():
            self._check_against_row(implication, group, next(iter(names)), *row)
        for rejected in self.rejected_implications:
            self._check_against_rejected(implication, group, rejected, self._masks(rejected))

    def _check_untrusted_after_trusted(self) -> None:
        """Check the unconfirmed implications again after the trusted ones
        grew.

        A complete object is contradicted by an unconfirmed implication only
        directly, whatever the trusted implications, so only the partial ones
        are checked again, and only those that the whole theory contradicts,
        since an unconfirmed implication contradicts no more with the
        trusted ones than all implications do together.
        """
        if not self._untrusted:
            return
        groups = self._untrusted_groups()
        for position in bits(self._partial_rows):
            row = self._rows_by_bit[1 << position]
            if self.implications.closure_mask(row[0]) & row[1]:
                name = next(iter(self._names_by_row[row]))
                for origin, group in groups.items():
                    self._check_against_row(origin, group, name, *row)
        for rejected in self.rejected_implications:
            masks = self._masks(rejected)
            if self.implications.closure_mask(masks[0]) & masks[1] == masks[1]:
                for origin, group in groups.items():
                    self._check_against_rejected(origin, group, rejected, masks)

    def _check_against_row(self, origin, group, name, positive: int, negative: int) -> None:
        """Record `origin` as refuted by the object `name` if the unconfirmed
        implications `group`, with the trusted ones, contradict its row. A
        complete row, closed under the trusted implications, is contradicted
        only if one of `group` refutes it directly."""
        if origin in self.refuted or not any(p & positive == p for p, _ in group):
            return
        if self._partial(positive, negative):
            contradicted = self._closure_with(positive, group) & negative
        else:
            contradicted = any(p & positive == p and c & negative for p, c in group)
        if contradicted:
            self.refuted[origin] = name

    def _check_against_rejected(self, origin, group, rejected, masks) -> None:
        """Record `origin` as refuted by `rejected` if the unconfirmed
        implications `group`, with the trusted ones, entail it."""
        premise, conclusion = masks
        if origin not in self.refuted and self._closure_with(premise, group) & conclusion == conclusion:
            self.refuted[origin] = rejected
