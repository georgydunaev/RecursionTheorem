"""RecursionTheorem: Mathematical Foundations of Recursion and Computability.

This package formalizes both the Set-Theoretic Recursion Theorem
(Dedekind/Peano recursion on natural numbers in Zermelo-Fraenkel set theory)
and Computability-Theoretic Recursion Theorems (Kleene First and Second Recursion
Theorems, Fixed-Point Combinators, S-m-n Parameter Theorem, and Rice's Theorem).
"""

from recursion_theory.kleene import (
    KleeneFirstRecursion,
    KleeneSecondRecursion,
    ParametricRecursionTheorem,
    RicesTheoremVerification,
    QuineConstructor,
)
from recursion_theory.combinators import (
    Term,
    Var,
    Abs,
    App,
    Y_combinator,
    Theta_combinator,
    Z_combinator,
    church_numeral,
    church_to_int,
    reduce_normal_order,
    reduce_step,
)
from recursion_theory.primitive_recursion import (
    PRF,
    Zero,
    Succ,
    Proj,
    Comp,
    Rec,
    Mu,
    prf_add,
    prf_mult,
    prf_exp,
    prf_fact,
    prf_pred,
    prf_sub,
)
from recursion_theory.theory_checker import IsabelleTheoryChecker

__all__ = [
    "KleeneFirstRecursion",
    "KleeneSecondRecursion",
    "ParametricRecursionTheorem",
    "RicesTheoremVerification",
    "QuineConstructor",
    "Term",
    "Var",
    "Abs",
    "App",
    "Y_combinator",
    "Theta_combinator",
    "Z_combinator",
    "church_numeral",
    "church_to_int",
    "reduce_normal_order",
    "reduce_step",
    "PRF",
    "Zero",
    "Succ",
    "Proj",
    "Comp",
    "Rec",
    "Mu",
    "prf_add",
    "prf_mult",
    "prf_exp",
    "prf_fact",
    "prf_pred",
    "prf_sub",
    "IsabelleTheoryChecker",
]
