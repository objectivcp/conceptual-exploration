from enum import Enum


class Truth(Enum):
    """A fixed truth value, which a mapping may send an attribute to.

    A substitution that identifies the arguments of a reflexive relation turns
    the atom into one that holds in every object, and so into no attribute at
    all; `ExplorationBase` reads such an image as true or false accordingly.
    """

    TRUE = True
    FALSE = False
