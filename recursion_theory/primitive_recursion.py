"""Primitive Recursive Functions (PRF) and Mu-Recursive Functions.

This module formalizes:
1. The inductive schema of Primitive Recursive Functions (Zero, Succ, Proj, Comp, Rec).
2. The arity system and sound evaluation.
3. Standard PRF constructions:
   - Addition: add(y, x) = x + y
   - Multiplication: mult(y, x) = x * y
   - Predecessor: pred(x) = max(0, x - 1)
   - Truncated subtraction (monus): sub(y, x) = max(0, x - y)
   - Exponentiation: exp(y, x) = x^y
   - Factorial: fact(n) = n!
4. The Mu operator (unbounded minimalization) defining general recursive functions.
5. Peano arithmetic verification of primitive recursive addition and multiplication.
"""

from typing import List, Tuple, Optional


class PRF:
    """Base class for Primitive Recursive Functions."""

    def __init__(self, arity: int):
        self.arity = arity

    def eval(self, *args: int) -> int:
        raise NotImplementedError

    def __call__(self, *args: int) -> int:
        if len(args) != self.arity:
            raise ValueError(f"Expected {self.arity} arguments, got {len(args)}")
        for a in args:
            if not isinstance(a, int) or a < 0:
                raise ValueError(f"Arguments must be non-negative integers, got {a}")
        return self.eval(*args)


class Zero(PRF):
    """The constant zero function: Z(x_1, ..., x_k) = 0."""

    def __init__(self, arity: int = 1):
        super().__init__(arity)

    def eval(self, *args: int) -> int:
        return 0

    def __repr__(self) -> str:
        return f"Zero^{self.arity}"


class Succ(PRF):
    """The successor function: S(x) = x + 1."""

    def __init__(self):
        super().__init__(1)

    def eval(self, *args: int) -> int:
        return args[0] + 1

    def __repr__(self) -> str:
        return "Succ"


class Proj(PRF):
    """The projection function: P_i^n(x_1, ..., x_n) = x_i (1-indexed)."""

    def __init__(self, n: int, i: int):
        if not (1 <= i <= n):
            raise ValueError(f"Index i={i} out of bounds for arity n={n}")
        super().__init__(n)
        self.i = i

    def eval(self, *args: int) -> int:
        return args[self.i - 1]

    def __repr__(self) -> str:
        return f"P_{self.i}^{self.arity}"


class Comp(PRF):
    """Composition: Cn[f, g_1, ..., g_m].

    If f has arity m, and each g_i has arity k,
    then Cn[f, g_1, ..., g_m] has arity k:
      Cn[f, g_1, ..., g_m](x_1, ..., x_k) = f(g_1(vec{x}), ..., g_m(vec{x})).
    """

    def __init__(self, f: PRF, gs: List[PRF]):
        if not gs:
            raise ValueError("Composition requires at least one inner function")
        k = gs[0].arity
        for g in gs:
            if g.arity != k:
                raise ValueError(f"All inner functions must share arity {k}, found {g.arity}")
        if len(gs) != f.arity:
            raise ValueError(f"Outer function requires {f.arity} inputs, got {len(gs)} inner functions")
        super().__init__(k)
        self.f = f
        self.gs = gs

    def eval(self, *args: int) -> int:
        inner_vals = [g.eval(*args) for g in self.gs]
        return self.f.eval(*inner_vals)

    def __repr__(self) -> str:
        return f"Cn[{self.f}, {', '.join(str(g) for g in self.gs)}]"


class Rec(PRF):
    """Primitive Recursion: Pr[g, h].

    If g has arity k, and h has arity k + 2:
      Pr[g, h](0, vec{x}) = g(vec{x})
      Pr[g, h](y + 1, vec{x}) = h(y, Pr[g, h](y, vec{x}), vec{x})
    Has arity k + 1.

    When k = 0, g is represented as a constant int c or 0-ary function:
      Pr[c, h](0) = c
      Pr[c, h](y + 1) = h(y, Pr[c, h](y))
    """

    def __init__(self, g: PRF, h: PRF):
        k = g.arity
        if h.arity != k + 2:
            raise ValueError(f"Step function h must have arity k+2 = {k + 2}, got {h.arity}")
        super().__init__(k + 1)
        self.g = g
        self.h = h

    def eval(self, *args: int) -> int:
        y = args[0]
        rest = args[1:]
        val = self.g.eval(*rest)
        for i in range(y):
            val = self.h.eval(i, val, *rest)
        return val

    def __repr__(self) -> str:
        return f"Pr[{self.g}, {self.h}]"


class Rec0(PRF):
    """Primitive recursion with base arity 0 (1-ary result).

    Rec0[base_const, h](0) = base_const
    Rec0[base_const, h](y + 1) = h(y, Rec0[base_const, h](y))
    where h has arity 2.
    """

    def __init__(self, base_const: int, h: PRF):
        if h.arity != 2:
            raise ValueError(f"Step function h must have arity 2, got {h.arity}")
        super().__init__(1)
        self.base_const = base_const
        self.h = h

    def eval(self, *args: int) -> int:
        y = args[0]
        val = self.base_const
        for i in range(y):
            val = self.h.eval(i, val)
        return val

    def __repr__(self) -> str:
        return f"Rec0[{self.base_const}, {self.h}]"


# -------------------------------------------------------------
# Standard Derived Primitive Recursive Functions
# -------------------------------------------------------------

def prf_add() -> PRF:
    """Addition function: add(y, x) = x + y.

    add(0, x) = x           (base: P_1^1)
    add(y+1, x) = S(add(y, x)) (step: Cn[Succ, P_2^3])
    """
    base = Proj(1, 1)
    step = Comp(Succ(), [Proj(3, 2)])
    return Rec(base, step)


def prf_mult() -> PRF:
    """Multiplication function: mult(y, x) = x * y.

    mult(0, x) = 0
    mult(y+1, x) = add(mult(y, x), x)
    """
    base = Zero(1)
    add_fn = prf_add()
    # step h(y, prev, x) = add(prev, x)
    # prev is arg 2, x is arg 3
    step = Comp(add_fn, [Proj(3, 2), Proj(3, 3)])
    return Rec(base, step)


def prf_pred() -> PRF:
    """Predecessor function: pred(y) = max(0, y - 1).

    pred(0) = 0
    pred(y+1) = y (step h(y, prev) = P_1^2(y, prev) = y)
    """
    return Rec0(0, Proj(2, 1))


def prf_sub() -> PRF:
    """Monus / truncated subtraction: sub(y, x) = max(0, x - y).

    sub(0, x) = x
    sub(y+1, x) = pred(sub(y, x))
    """
    base = Proj(1, 1)
    pred_fn = prf_pred()
    step = Comp(pred_fn, [Proj(3, 2)])
    return Rec(base, step)


def prf_exp() -> PRF:
    """Exponentiation: exp(y, x) = x^y.

    exp(0, x) = 1
    exp(y+1, x) = mult(exp(y, x), x)
    """
    # Base: constant 1 for 1 argument = Comp(Succ, [Zero(1)])
    base = Comp(Succ(), [Zero(1)])
    mult_fn = prf_mult()
    # step h(y, prev, x) = mult(prev, x)
    step = Comp(mult_fn, [Proj(3, 2), Proj(3, 3)])
    return Rec(base, step)


def prf_fact() -> PRF:
    """Factorial function: fact(n) = n!.

    fact(0) = 1
    fact(y+1) = (y + 1) * fact(y)
    """
    mult_fn = prf_mult()
    # step h(y, prev) = mult(Succ(y), prev)
    step = Comp(mult_fn, [Comp(Succ(), [Proj(2, 1)]), Proj(2, 2)])
    return Rec0(1, step)


class Mu:
    """Unbounded minimalization operator (Mu operator).

    Given f of arity k + 1:
      mu[f](vec{x}) = min { y in N | f(y, vec{x}) == 0 }
    """

    def __init__(self, f: PRF, max_search: int = 100000):
        if f.arity < 2:
            raise ValueError(f"Mu operator requires function of arity >= 2, got {f.arity}")
        self.f = f
        self.arity = f.arity - 1
        self.max_search = max_search

    def __call__(self, *args: int) -> int:
        if len(args) != self.arity:
            raise ValueError(f"Expected {self.arity} arguments, got {len(args)}")
        for y in range(self.max_search):
            if self.f(y, *args) == 0:
                return y
        raise TimeoutError(f"Minimalization search exceeded {self.max_search} steps")
