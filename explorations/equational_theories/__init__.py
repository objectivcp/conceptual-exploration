"""Equational Theories Project (ETP) exploration domain.

Provides algebraic representations of magmas, term ASTs, equational laws,
automated counterexample search, and duality symmetries for conceptual exploration.
"""

from .magma import ETP, Equation, Magma, MagmaExpert, Op, Term, Var

__all__ = [
    "ETP",
    "Equation",
    "Magma",
    "MagmaExpert",
    "Op",
    "Term",
    "Var",
]
