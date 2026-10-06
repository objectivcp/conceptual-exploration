"""Unit tests for ExplorationBase object bookkeeping."""

import pytest

from conceptual_exploration import Implication
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.truth import Truth
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource


def test_object_is_merged_before_being_completed():
    """Completion must run on everything known about an object, not on one part.

    An attribute derivable from the union of two observations need not be
    derivable from either on its own, so merging has to happen first: completing
    each observation separately and then unioning the results loses `c` below.
    """
    base = ExplorationBase(
        attributes=["a", "b", "c"],
        background_implications=[
            Implication(frozenset(["a", "b"]), frozenset(["c"])),
        ],
    )

    # Two sightings of the same object, neither of which implies c by itself.
    base.add_counterexample(PartialObject("g", {"a"}, set()))
    base.add_counterexample(PartialObject("g", {"b"}, set()))

    stored = next(iter(base.context.objects.values()))
    assert stored.positive == {"a", "b", "c"}


def test_the_expert_s_attribute_sets_are_left_alone():
    """The expert's own sets are handed over without being copied.

    That is only safe while merging and completion rebind the attributes rather
    than updating the sets in place — an `|=` here would reach back into the
    object the expert still holds.
    """
    base = ExplorationBase(
        attributes=["a", "b", "c", "d"],
        background_implications=[
            Implication(frozenset(["a"]), frozenset(["c"])),
        ],
    )
    base.add_counterexample(PartialObject("g", {"a"}, {"d"}))

    # The second sighting is the dangerous one: this is the call whose sets the
    # merge reads, and an in-place union would write straight back into them.
    positive, negative = {"b"}, set()
    base.add_counterexample(PartialObject("g", positive, negative))

    assert positive == {"b"}
    assert negative == set()

    stored = next(iter(base.context.objects.values()))
    assert stored.positive == {"a", "b", "c"}
    assert stored.negative == {"d"}


def test_conflicting_observation_leaves_the_context_unchanged():
    """A rejected observation must not be half-absorbed.

    The merged object is completed while still detached, so a client that
    catches the error and asks the expert for another counterexample resumes
    from the context it had before.
    """
    base = ExplorationBase(
        attributes=["a", "b", "c"],
        background_implications=[
            Implication(frozenset(["a"]), frozenset(["c"])),
        ],
    )
    base.add_counterexample(PartialObject("g", {"a"}, set()))
    stored = next(iter(base.context.objects.values()))
    before = (set(stored.positive), set(stored.negative))

    # `a` forces `c`, so denying `c` contradicts what is already known.
    with pytest.raises(ValueError):
        base.add_counterexample(PartialObject("g", set(), {"c"}))

    assert (set(stored.positive), set(stored.negative)) == before


def test_implication_conflict_raises_rather_than_asserts():
    """The check must survive `python -O`, which strips assertions."""
    base = ExplorationBase(
        attributes=["a", "b", "c"],
        background_implications=[
            Implication(frozenset(["a"]), frozenset(["c"])),
        ],
    )
    with pytest.raises(ValueError):
        base.add_counterexample(PartialObject("g", {"a"}, {"c"}))

    assert not base.context.objects


def test_background_implications_are_mapped():
    swap = {"a": "b", "b": "a", "c": "d", "d": "c"}
    base = ExplorationBase(
        attributes=["a", "b", "c", "d"],
        background_implications=[Implication(frozenset(["a"]), frozenset(["c"]))],
        mappings=[lambda x: swap[x]],
    )

    mapped = Implication(frozenset(["b"]), frozenset(["d"]))
    assert base.implications.entails(mapped)
    assert base.implication_sources[mapped] is ImplicationSource.MAPPED


def test_mapped_versions_are_already_complete():
    """Mapping a completed object yields a completed one.

    This holds only while the theory is closed under the mappings, which is why
    background implications are mapped as confirmed ones are.
    """
    swap = {"a": "b", "b": "a", "c": "d", "d": "c", "e": "e"}
    base = ExplorationBase(
        attributes=["a", "b", "c", "d", "e"],
        background_implications=[
            Implication(frozenset(["a"]), frozenset(["c"])),
            Implication(frozenset(["d"]), frozenset(["e"])),
        ],
        mappings=[lambda x: swap[x]],
    )
    base.add_counterexample(PartialObject("g", {"a"}, set()))

    versions = {str(o.object): o for o in base.context.objects.values()}
    original, mapped = versions["g#0"], versions["g#1"]

    assert original.positive == {"a", "c", "e"}
    # The image of the completed original, with nothing further to derive.
    assert mapped.positive == {swap[a] for a in original.positive}
    before = set(mapped.positive)
    base._update_object(mapped)
    assert mapped.positive == before


def test_duplicate_mapped_versions_are_not_stored():
    """A mapping that leaves an object where it was adds no new version.

    Substitutions are not injective, so several of them can ground to the same
    object; the copies they produce would only repeat work in every later
    closure.
    """
    identify = {"a": "a", "b": "a", "c": "c"}
    swap = {"a": "b", "b": "a", "c": "c"}
    base = ExplorationBase(
        attributes=["a", "b", "c"],
        mappings=[lambda x: identify[x], lambda x: swap[x]],
    )
    base.add_counterexample(PartialObject("g", {"a", "b"}, {"c"}))

    # The substitution fixes the object, the swap fixes it too; one copy is
    # enough for the pair.
    assert [str(o.object) for o in base.context.objects.values()] == ["g#0"]

    # A version stays in the context once it is there, even when a later
    # sighting makes it a duplicate.
    base = ExplorationBase(
        attributes=["a", "b", "c"],
        mappings=[lambda x: swap[x]],
    )
    base.add_counterexample(PartialObject("g", {"a"}, set()))
    base.add_counterexample(PartialObject("g", {"b"}, set()))

    versions = {str(o.object): o for o in base.context.objects.values()}
    assert set(versions) == {"g#0", "g#1"}
    assert versions["g#1"].positive == {"a", "b"}


def test_add_returns_the_stored_object():
    base = ExplorationBase(attributes=["a", "b"])

    first = base.context.add(PartialObject("g", {"a"}, set()))
    second = base.context.add(PartialObject("g", {"b"}, set()))

    # The second call merges into the first object rather than replacing it.
    assert first is second
    assert second.positive == {"a", "b"}
    assert len(base.context.objects) == 1


def test_mappings_to_truth_values():
    """A mapping may send an attribute to a fixed truth value, as identifying
    the arguments of a reflexive or irreflexive relation does."""
    # Sends a to true and b to false, and swaps c and d.
    image = {"a": Truth.TRUE, "b": Truth.FALSE, "c": "d", "d": "c"}
    base = ExplorationBase(
        attributes=["a", "b", "c", "d"],
        mappings=[lambda x: image[x]],
    )

    # A false premise attribute: the image says nothing.
    base.accept(Implication(frozenset(["b"]), frozenset(["c"])))
    assert len(base.implications.implications) == 1

    # A true premise attribute drops out of the image.
    base.accept(Implication(frozenset(["a", "c"]), frozenset(["d"])))
    assert base.implications.entails(Implication(frozenset(["d"]), frozenset(["c"])))

    # A false conclusion attribute makes the premise image impossible.
    base.accept(Implication(frozenset(["c"]), frozenset(["b"])))
    assert base.implications.entails(
        Implication(frozenset(["d"]), frozenset(["a", "b", "c"]))
    )

    # In an object's image the attributes take their fixed values, whatever
    # the object itself says about them.
    base = ExplorationBase(
        attributes=["a", "b", "c", "d"],
        mappings=[lambda x: image[x]],
    )
    base.add_counterexample(PartialObject("g", {"c"}, {"a"}))
    versions = {str(o.object): o for o in base.context.objects.values()}
    assert versions["g#1"].positive == {"a", "d"}
    assert versions["g#1"].negative == {"b"}


if __name__ == "__main__":
    test_object_is_merged_before_being_completed()
    test_the_expert_s_attribute_sets_are_left_alone()
    test_conflicting_observation_leaves_the_context_unchanged()
    test_implication_conflict_raises_rather_than_asserts()
    test_background_implications_are_mapped()
    test_mapped_versions_are_already_complete()
    test_duplicate_mapped_versions_are_not_stored()
    test_add_returns_the_stored_object()
    test_mappings_to_truth_values()
    print("All exploration base tests passed successfully!")
