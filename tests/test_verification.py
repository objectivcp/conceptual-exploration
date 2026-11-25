"""Unit tests for checking an exploration's result from its evidence."""

import json

import pytest

from conceptual_exploration.verification import (
    VerificationError, check_closure_systems, check_open_closure_systems)
from explorations.equational_theories.certificates import parse_law
from explorations.equational_theories.verify import (
    holds, is_associative, law_key, nilpotency, read_open, semigroup_laws)

# Attributes a, b, c as bits 0, 1, 2; the objects have the intents {a, b},
# {b} and {b, c}, so that b always holds and a and c exclude each other.
INTENTS = [0b011, 0b010, 0b110]


def test_a_basis_gives_the_intents():
    # 0 -> b and a c -> a b c: the closed sets are {b}, {a, b}, {b, c}, {a, b, c}.
    assert check_closure_systems(3, INTENTS, [(0, 0b010), (0b101, 0b111)]) == 4


def test_an_implication_the_objects_violate_is_rejected():
    with pytest.raises(VerificationError, match="violates"):
        check_closure_systems(3, INTENTS, [(0, 0b010), (0b001, 0b100)])


def test_missing_implications_are_rejected():
    # Without 0 -> b, the empty set is closed but no intent.
    with pytest.raises(VerificationError, match="not intents"):
        check_closure_systems(3, INTENTS, [(0b101, 0b111)])
    # In a context where b and c hold together, 0 -> a leaves {a, b} closed.
    with pytest.raises(VerificationError, match="not intents"):
        check_closure_systems(3, [0b111, 0b001], [(0, 0b001)])


def test_the_closures_may_be_computed_in_processes():
    assert check_closure_systems(3, INTENTS, [(0, 0b010)], processes=2) == 4


def test_implications_entailed_by_others_are_not_needed():
    # a c -> a b c follows from 0 -> b, the full set being an intent.
    assert check_closure_systems(3, INTENTS, [(0, 0b010)]) == 4


# Rows as (has, lacks): {a, b} and {b} completely known, and an object known
# only to have b and c. Under 0 -> b, the closed sets are {b}, {a, b}, {b, c}
# and {a, b, c}; no object settles {b, c}, where a is open.
FULL = 0b111
ROWS = [(0b011, FULL & ~0b011), (0b010, FULL & ~0b010), (0b110, 0)]


def test_the_open_sets_of_an_unfinished_exploration_are_checked():
    assert check_open_closure_systems(3, ROWS, [(0, 0b010)], {0b110: 0b001}) == (4, 3)


def test_a_finished_exploration_has_no_open_sets():
    rows = [(intent, FULL & ~intent) for intent in INTENTS]
    assert check_open_closure_systems(3, rows, [(0, 0b010)], {}) == (4, 4)


def test_open_sets_must_be_listed_with_their_open_attributes():
    with pytest.raises(VerificationError, match="not listed"):
        check_open_closure_systems(3, ROWS, [(0, 0b010)], {})
    with pytest.raises(VerificationError, match="listed with"):
        check_open_closure_systems(3, ROWS, [(0, 0b010)], {0b110: 0b101})
    with pytest.raises(VerificationError, match="settled"):
        check_open_closure_systems(3, ROWS, [(0, 0b010)], {0b110: 0b001, 0b011: 0b100})
    with pytest.raises(VerificationError, match="not closed"):
        check_open_closure_systems(3, ROWS, [(0, 0b010)], {0b110: 0b001, 0b100: 0b001})


def test_a_row_must_respect_the_implications():
    # The partial object has b and c, so it may not lack a under b c -> a.
    rows = ROWS[:2] + [(0b110, 0b001)]
    with pytest.raises(VerificationError, match="violates"):
        check_open_closure_systems(3, rows, [(0, 0b010), (0b110, 0b001)], {})



def test_the_open_sets_are_read_by_law(tmp_path):
    path = tmp_path / "open.json"
    index = {"Eq1": 0, "Eq3": 1, "Eq5": 2}
    path.write_text(json.dumps([{"closure": [1, 3], "open": ["Eq5"]}]))
    assert read_open(path, index) == {0b011: 0b100}
    path.write_text(json.dumps([{"closure": [1], "open": [7]}]))
    with pytest.raises(VerificationError, match="not a law"):
        read_open(path, index)
    path.write_text(json.dumps([{"closure": [1], "open": [3]}, {"closure": [1], "open": [5]}]))
    with pytest.raises(VerificationError, match="twice"):
        read_open(path, index)


LEFT_ZERO = [[0, 0], [1, 1]]  # x * y = x
ZERO_TWO = [[0, 0, 0], [0, 0, 0], [0, 0, 1]]  # 2 * 2 = 1, every other product 0


def test_laws_are_evaluated_on_tables():
    assert holds(LEFT_ZERO, parse_law("x = x * y"))
    assert holds(LEFT_ZERO, parse_law("x * (y * z) = (x * y) * z"))
    assert not holds(LEFT_ZERO, parse_law("x * y = y * x"))
    assert is_associative(LEFT_ZERO)
    assert holds(ZERO_TWO, parse_law("x * y = y * x"))


def test_long_products_are_zero_in_a_nilpotent_semigroup():
    assert nilpotency(ZERO_TWO) == (3, 0)
    assert nilpotency(LEFT_ZERO) is None
    for law in ["x * (y * z) = (z * y) * x", "x * (x * x) = y * y", "x * y = (x * y) * z"]:
        assert holds(ZERO_TWO, parse_law(law), nilpotency(ZERO_TWO)) == holds(ZERO_TWO, parse_law(law))


def test_laws_are_compared_up_to_renaming_swapping_and_bracketing():
    assert law_key(parse_law("x * y = y"), False) == law_key(parse_law("z = w * z"), False)
    assert law_key(parse_law("(x * y) * z = x"), False) != law_key(parse_law("x * (y * z) = x"), False)
    assert law_key(parse_law("(x * y) * z = x"), True) == law_key(parse_law("x * (y * z) = x"), True)


def test_the_semigroup_laws_are_counted():
    # x = x and x = y; then x = xx, x = xy, x = yx, x = yy and x = yz.
    assert len(semigroup_laws(0)) == 2
    assert len(semigroup_laws(1)) == 7
