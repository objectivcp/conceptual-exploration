"""Equational Theories Project (ETP) exploration domain.

Provides algebraic representations of magmas, term ASTs, equational laws,
automated counterexample search, and duality symmetries for conceptual exploration.
"""

from .background import BoundedDerivation, background_implications
from .magma import ETP, Equation, Magma, MagmaExpert, Op, Term, Var

__all__ = [
    "BoundedDerivation",
    "background_implications",
    "ETP",
    "Equation",
    "Magma",
    "MagmaExpert",
    "Op",
    "Term",
    "Var",
]
