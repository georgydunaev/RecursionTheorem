"""Primitive Recursive Functions (PRF) and Mu-Recursive Functions.

This module formalizes:
1. The modular inductive schema of Primitive Recursive Functions
   (Zero, Succ, Proj, Compose, Recurse).
2. Well-formedness checks, AST metrics (size, depth, subterms), structural
   equality, serialization (to_dict / from_dict), and Gödel numbering.
3. Verified inductive evaluation semantics via PRFVerifier.
4. Standard PRF constructions:
   - Addition: add(y, x) = x + y
   - Multiplication: mult(y, x) = x * y
   - Predecessor: pred(x) = max(0, x - 1)
   - Truncated subtraction (monus): sub(y, x) = max(0, x - y)
   - Exponentiation: exp(y, x) = x^y
   - Factorial: fact(n) = n!
   - Constants, Identity, Signum, IsZero, Max, Min, Equal
5. The Mu operator (unbounded minimalization) defining general recursive functions.
6. Cantor pairing and Gödel numbering of PRF inductive datatypes.
"""

import math
from typing import List, Tuple, Optional, Dict, Any


# -------------------------------------------------------------
# Cantor Pairing and Natural Number List Encoding
# -------------------------------------------------------------

def cantor_pair(x: int, y: int) -> int:
    """Bijective Cantor pairing function for N x N to N."""
    if x < 0 or y < 0:
        raise ValueError("Inputs to cantor_pair must be non-negative integers")
    return ((x + y) * (x + y + 1)) // 2 + y


def cantor_unpair(z: int) -> Tuple[int, int]:
    """Invert the Cantor pairing function."""
    if z < 0:
        raise ValueError("Input to cantor_unpair must be non-negative integer")
    w = int((math.isqrt(8 * z + 1) - 1) // 2)
    t = (w * (w + 1)) // 2
    y = z - t
    x = w - y
    return x, y


def encode_nat_list(lst: List[int]) -> int:
    """Encode a finite list of natural numbers as a single natural number."""
    code = 0
    for x in reversed(lst):
        code = cantor_pair(x + 1, code)
    return code


def decode_nat_list(code: int) -> List[int]:
    """Decode a natural number into a finite list of natural numbers."""
    lst: List[int] = []
    while code != 0:
        x_plus_1, code = cantor_unpair(code)
        lst.append(x_plus_1 - 1)
    return lst


# -------------------------------------------------------------
# Base Inductive Datatype for Primitive Recursive Functions
# -------------------------------------------------------------

class PRF:
    """Base class and inductive term algebra for Primitive Recursive Functions."""

    def __init__(self, arity: int):
        if not isinstance(arity, int) or arity < 0:
            raise ValueError(f"Arity must be a non-negative integer, got {arity}")
        self.arity = arity

    def eval(self, *args: int) -> int:
        """Evaluate the PRF term on arguments."""
        raise NotImplementedError

    def __call__(self, *args: int) -> int:
        if len(args) != self.arity:
            raise ValueError(f"Expected {self.arity} arguments, got {len(args)}")
        for a in args:
            if not isinstance(a, int) or a < 0:
                raise ValueError(f"Arguments must be non-negative integers, got {a}")
        return self.eval(*args)

    @property
    def size(self) -> int:
        """Total number of constructor nodes in the inductive AST."""
        return 1 + sum(child.size for child in self.subterms())

    @property
    def depth(self) -> int:
        """Height of the inductive AST tree."""
        children = self.subterms()
        if not children:
            return 1
        return 1 + max(child.depth for child in children)

    def subterms(self) -> List['PRF']:
        """Immediate inductive subterms or child PRF expressions."""
        return []

    def is_well_formed(self) -> bool:
        """Verify structural well-formedness of the term and its subterms."""
        return all(child.is_well_formed() for child in self.subterms())

    def to_dict(self) -> Dict[str, Any]:
        """Serialize the inductive PRF term to dictionary representation."""
        raise NotImplementedError

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> 'PRF':
        """Deserialize an inductive PRF term from dictionary representation."""
        t = d.get("type")
        if t == "Zero":
            return Zero(d.get("arity", 1))
        elif t == "Succ":
            return Succ()
        elif t == "Proj":
            return Proj(d["n"], d["i"])
        elif t in ("Compose", "Comp"):
            f = PRF.from_dict(d["f"])
            gs = [PRF.from_dict(g) for g in d["gs"]]
            return Compose(f, gs)
        elif t in ("Recurse", "Rec"):
            g = PRF.from_dict(d["g"])
            h = PRF.from_dict(d["h"])
            return Recurse(g, h)
        elif t == "Rec0":
            h = PRF.from_dict(d["h"])
            return Rec0(d["base_const"], h)
        raise ValueError(f"Unknown inductive PRF type: {t}")

    def to_expr(self) -> str:
        """Return symbolic mathematical representation."""
        raise NotImplementedError

    def eval_trace(self, *args: int) -> Tuple[int, List[str]]:
        """Evaluate with execution trace recording intermediate inductive steps."""
        trace = [f"Eval {self.to_expr()} with args {args}"]
        res = self(*args)
        trace.append(f"Result = {res}")
        return res, trace


# -------------------------------------------------------------
# Modular Inductive PRF Constructors
# -------------------------------------------------------------

class Zero(PRF):
    """The constant zero function: Z^k(x_1, ..., x_k) = 0."""

    def __init__(self, arity: int = 1):
        super().__init__(arity)

    def eval(self, *args: int) -> int:
        return 0

    def to_dict(self) -> Dict[str, Any]:
        return {"type": "Zero", "arity": self.arity}

    def to_expr(self) -> str:
        return f"Zero^{self.arity}"

    def __repr__(self) -> str:
        return f"Zero^{self.arity}"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Zero) and self.arity == other.arity

    def __hash__(self) -> int:
        return hash(("Zero", self.arity))


class Succ(PRF):
    """The successor function: S(x) = x + 1."""

    def __init__(self):
        super().__init__(1)

    def eval(self, *args: int) -> int:
        return args[0] + 1

    def to_dict(self) -> Dict[str, Any]:
        return {"type": "Succ", "arity": 1}

    def to_expr(self) -> str:
        return "Succ"

    def __repr__(self) -> str:
        return "Succ"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Succ)

    def __hash__(self) -> int:
        return hash("Succ")


class Proj(PRF):
    """The projection function: P_i^n(x_1, ..., x_n) = x_i (1-indexed)."""

    def __init__(self, n: int, i: int):
        if not (1 <= i <= n):
            raise ValueError(f"Index i={i} out of bounds for arity n={n}")
        super().__init__(n)
        self.i = i

    def eval(self, *args: int) -> int:
        return args[self.i - 1]

    def to_dict(self) -> Dict[str, Any]:
        return {"type": "Proj", "n": self.arity, "i": self.i}

    def to_expr(self) -> str:
        return f"P_{self.i}^{self.arity}"

    def __repr__(self) -> str:
        return f"P_{self.i}^{self.arity}"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Proj) and self.arity == other.arity and self.i == other.i

    def __hash__(self) -> int:
        return hash(("Proj", self.arity, self.i))


class Compose(PRF):
    """Composition: Cn[f, g_1, ..., g_m].

    If f has arity m, and each g_i has arity k,
    then Cn[f, g_1, ..., g_m] has arity k:
      Cn[f, g_1, ..., g_m](x_1, ..., x_k) = f(g_1(vec{x}), ..., g_m(vec{x})).
    """

    def __init__(self, f: PRF, gs: List[PRF]):
        if not isinstance(f, PRF):
            raise TypeError("Outer function f must be an instance of PRF")
        if not gs:
            raise ValueError("Composition requires at least one inner function")
        for g in gs:
            if not isinstance(g, PRF):
                raise TypeError("Inner functions gs must be instances of PRF")
        k = gs[0].arity
        for g in gs:
            if g.arity != k:
                raise ValueError(f"All inner functions must share arity {k}, found {g.arity}")
        if len(gs) != f.arity:
            raise ValueError(f"Outer function requires {f.arity} inputs, got {len(gs)} inner functions")
        super().__init__(k)
        self.f = f
        self.gs = gs

    def subterms(self) -> List[PRF]:
        return [self.f] + list(self.gs)

    def eval(self, *args: int) -> int:
        inner_vals = [g.eval(*args) for g in self.gs]
        return self.f.eval(*inner_vals)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "type": "Compose",
            "f": self.f.to_dict(),
            "gs": [g.to_dict() for g in self.gs]
        }

    def to_expr(self) -> str:
        return f"Cn[{self.f.to_expr()}, {', '.join(g.to_expr() for g in self.gs)}]"

    def __repr__(self) -> str:
        return f"Cn[{self.f}, {', '.join(str(g) for g in self.gs)}]"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, (Compose, Comp)):
            return False
        return self.f == other.f and self.gs == other.gs

    def __hash__(self) -> int:
        return hash(("Compose", self.f, tuple(self.gs)))


# Backward-compatibility alias
Comp = Compose


class Recurse(PRF):
    """Primitive Recursion: Pr[g, h].

    If g has arity k, and h has arity k + 2:
      Pr[g, h](0, vec{x}) = g(vec{x})
      Pr[g, h](y + 1, vec{x}) = h(y, Pr[g, h](y, vec{x}), vec{x})
    Has arity k + 1.
    """

    def __init__(self, g: PRF, h: PRF):
        if not isinstance(g, PRF) or not isinstance(h, PRF):
            raise TypeError("Both base g and step h must be instances of PRF")
        k = g.arity
        if h.arity != k + 2:
            raise ValueError(f"Step function h must have arity k+2 = {k + 2}, got {h.arity}")
        super().__init__(k + 1)
        self.g = g
        self.h = h

    def subterms(self) -> List[PRF]:
        return [self.g, self.h]

    def eval(self, *args: int) -> int:
        y = args[0]
        rest = args[1:]
        val = self.g.eval(*rest)
        for i in range(y):
            val = self.h.eval(i, val, *rest)
        return val

    def to_dict(self) -> Dict[str, Any]:
        return {
            "type": "Recurse",
            "g": self.g.to_dict(),
            "h": self.h.to_dict()
        }

    def to_expr(self) -> str:
        return f"Pr[{self.g.to_expr()}, {self.h.to_expr()}]"

    def __repr__(self) -> str:
        return f"Pr[{self.g}, {self.h}]"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, (Recurse, Rec)):
            return False
        return self.g == other.g and self.h == other.h

    def __hash__(self) -> int:
        return hash(("Recurse", self.g, self.h))


# Backward-compatibility alias
Rec = Recurse


class Rec0(PRF):
    """Primitive recursion with base arity 0 (1-ary result).

    Rec0[base_const, h](0) = base_const
    Rec0[base_const, h](y + 1) = h(y, Rec0[base_const, h](y))
    where h has arity 2.
    """

    def __init__(self, base_const: int, h: PRF):
        if not isinstance(h, PRF):
            raise TypeError("Step function h must be an instance of PRF")
        if h.arity != 2:
            raise ValueError(f"Step function h must have arity 2, got {h.arity}")
        super().__init__(1)
        self.base_const = base_const
        self.h = h

    def subterms(self) -> List[PRF]:
        return [self.h]

    def eval(self, *args: int) -> int:
        y = args[0]
        val = self.base_const
        for i in range(y):
            val = self.h.eval(i, val)
        return val

    def to_dict(self) -> Dict[str, Any]:
        return {
            "type": "Rec0",
            "base_const": self.base_const,
            "h": self.h.to_dict()
        }

    def to_expr(self) -> str:
        return f"Rec0[{self.base_const}, {self.h.to_expr()}]"

    def __repr__(self) -> str:
        return f"Rec0[{self.base_const}, {self.h}]"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Rec0):
            return False
        return self.base_const == other.base_const and self.h == other.h

    def __hash__(self) -> int:
        return hash(("Rec0", self.base_const, self.h))


# -------------------------------------------------------------
# Gödel Numbering of Primitive Recursive Inductive Terms
# -------------------------------------------------------------

def encode_prf(prf: PRF) -> int:
    """Compute the unique Gödel number encoding for an inductive PRF AST."""
    if isinstance(prf, Zero):
        return encode_nat_list([0, prf.arity])
    elif isinstance(prf, Succ):
        return encode_nat_list([1])
    elif isinstance(prf, Proj):
        return encode_nat_list([2, prf.arity, prf.i])
    elif isinstance(prf, (Compose, Comp)):
        g_codes = [encode_prf(g) for g in prf.gs]
        return encode_nat_list([3, encode_prf(prf.f), len(g_codes)] + g_codes)
    elif isinstance(prf, (Recurse, Rec)):
        return encode_nat_list([4, encode_prf(prf.g), encode_prf(prf.h)])
    elif isinstance(prf, Rec0):
        return encode_nat_list([5, prf.base_const, encode_prf(prf.h)])
    raise ValueError(f"Cannot encode unknown PRF: {prf}")


def decode_prf(code: int) -> PRF:
    """Decode a Gödel number into the corresponding inductive PRF AST."""
    lst = decode_nat_list(code)
    if not lst:
        raise ValueError("Invalid empty Gödel code for PRF")
    tag = lst[0]
    if tag == 0:
        return Zero(lst[1])
    elif tag == 1:
        return Succ()
    elif tag == 2:
        return Proj(lst[1], lst[2])
    elif tag == 3:
        f_code = lst[1]
        num_gs = lst[2]
        g_codes = lst[3:3 + num_gs]
        f = decode_prf(f_code)
        gs = [decode_prf(gc) for gc in g_codes]
        return Compose(f, gs)
    elif tag == 4:
        g = decode_prf(lst[1])
        h = decode_prf(lst[2])
        return Recurse(g, h)
    elif tag == 5:
        base_const = lst[1]
        h = decode_prf(lst[2])
        return Rec0(base_const, h)
    raise ValueError(f"Unknown PRF Gödel tag: {tag}")


# -------------------------------------------------------------
# Formal Evaluation Semantics Verifier
# -------------------------------------------------------------

class PRFVerifier:
    """Verification suite for primitive recursive schemas and evaluation semantics."""

    @staticmethod
    def verify_zero_semantics(zero: Zero, test_args: List[Tuple[int, ...]]) -> bool:
        for args in test_args:
            if len(args) != zero.arity or zero(*args) != 0:
                return False
        return True

    @staticmethod
    def verify_succ_semantics(succ: Succ, test_inputs: List[int]) -> bool:
        for x in test_inputs:
            if succ(x) != x + 1:
                return False
        return True

    @staticmethod
    def verify_proj_semantics(proj: Proj, test_args: List[Tuple[int, ...]]) -> bool:
        for args in test_args:
            if len(args) != proj.arity or proj(*args) != args[proj.i - 1]:
                return False
        return True

    @staticmethod
    def verify_compose_semantics(comp: Compose, test_args: List[Tuple[int, ...]]) -> bool:
        for args in test_args:
            inner_vals = [g(*args) for g in comp.gs]
            expected = comp.f(*inner_vals)
            if comp(*args) != expected:
                return False
        return True

    @staticmethod
    def verify_recurse_semantics(rec: Recurse, test_args: List[Tuple[int, ...]]) -> bool:
        for args in test_args:
            y = args[0]
            rest = args[1:]
            base_val = rec(0, *rest)
            if base_val != rec.g(*rest):
                return False
            curr = base_val
            for step_y in range(y):
                next_val = rec.h(step_y, curr, *rest)
                curr_actual = rec(step_y + 1, *rest)
                if curr_actual != next_val:
                    return False
                curr = next_val
        return True

    @staticmethod
    def verify_inductive_semantics(prf: PRF, test_args: List[Tuple[int, ...]]) -> bool:
        """Verify inductive evaluation semantics for any well-formed PRF."""
        if not prf.is_well_formed():
            return False
        if isinstance(prf, Zero):
            return PRFVerifier.verify_zero_semantics(prf, test_args)
        elif isinstance(prf, Succ):
            return PRFVerifier.verify_succ_semantics(prf, [a[0] for a in test_args if len(a) == 1])
        elif isinstance(prf, Proj):
            return PRFVerifier.verify_proj_semantics(prf, test_args)
        elif isinstance(prf, (Compose, Comp)):
            return PRFVerifier.verify_compose_semantics(prf, test_args)
        elif isinstance(prf, (Recurse, Rec)):
            return PRFVerifier.verify_recurse_semantics(prf, test_args)
        return True


# -------------------------------------------------------------
# Standard Derived Primitive Recursive Functions
# -------------------------------------------------------------

def prf_add() -> PRF:
    """Addition function: add(y, x) = x + y.

    add(0, x) = x               (base: P_1^1)
    add(y+1, x) = S(add(y, x))  (step: Cn[Succ, P_2^3])
    """
    base = Proj(1, 1)
    step = Compose(Succ(), [Proj(3, 2)])
    return Recurse(base, step)


def prf_mult() -> PRF:
    """Multiplication function: mult(y, x) = x * y.

    mult(0, x) = 0
    mult(y+1, x) = add(mult(y, x), x)
    """
    base = Zero(1)
    add_fn = prf_add()
    step = Compose(add_fn, [Proj(3, 2), Proj(3, 3)])
    return Recurse(base, step)


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
    step = Compose(pred_fn, [Proj(3, 2)])
    return Recurse(base, step)


def prf_exp() -> PRF:
    """Exponentiation: exp(y, x) = x^y.

    exp(0, x) = 1
    exp(y+1, x) = mult(exp(y, x), x)
    """
    base = Compose(Succ(), [Zero(1)])
    mult_fn = prf_mult()
    step = Compose(mult_fn, [Proj(3, 2), Proj(3, 3)])
    return Recurse(base, step)


def prf_fact() -> PRF:
    """Factorial function: fact(n) = n!.

    fact(0) = 1
    fact(y+1) = (y + 1) * fact(y)
    """
    mult_fn = prf_mult()
    step = Compose(mult_fn, [Compose(Succ(), [Proj(2, 1)]), Proj(2, 2)])
    return Rec0(1, step)


def prf_const(c: int, arity: int = 1) -> PRF:
    """Constant function: C_c^k(x_1, ..., x_k) = c."""
    if c < 0:
        raise ValueError("Constant value must be non-negative")
    res: PRF = Zero(arity)
    succ_fn = Succ()
    for _ in range(c):
        res = Compose(succ_fn, [res])
    return res


def prf_id(arity: int = 1) -> PRF:
    """Identity function on the first argument: P_1^k."""
    return Proj(arity, 1)


def prf_is_zero() -> PRF:
    """Boolean test for zero: is_zero(x) = 1 if x == 0 else 0."""
    # is_zero(0) = 1
    # is_zero(y + 1) = 0
    step = Compose(Zero(1), [Proj(2, 1)])
    return Rec0(1, step)


def prf_signum() -> PRF:
    """Signum function: sgn(0) = 0, sgn(y + 1) = 1."""
    step = Compose(Succ(), [Compose(Zero(1), [Proj(2, 1)])])
    return Rec0(0, step)


def prf_max() -> PRF:
    """Maximum function: max(y, x) = y + (x - y)."""
    # max(y, x) = add(sub(x, y), y)
    add_fn = prf_add()
    sub_fn = prf_sub()
    # P_1^2 is y, P_2^2 is x
    sub_x_y = Compose(sub_fn, [Proj(2, 1), Proj(2, 2)])
    return Compose(add_fn, [sub_x_y, Proj(2, 1)])


def prf_min() -> PRF:
    """Minimum function: min(y, x) = x - (x - y)."""
    sub_fn = prf_sub()
    # sub(sub(y, x), x)
    sub_y_x = Compose(sub_fn, [Proj(2, 1), Proj(2, 2)])
    return Compose(sub_fn, [sub_y_x, Proj(2, 2)])


def prf_equal() -> PRF:
    """Equality indicator: equal(y, x) = 1 if x == y else 0."""
    sub_fn = prf_sub()
    add_fn = prf_add()
    is_zero_fn = prf_is_zero()
    diff1 = Compose(sub_fn, [Proj(2, 1), Proj(2, 2)])
    diff2 = Compose(sub_fn, [Proj(2, 2), Proj(2, 1)])
    total_diff = Compose(add_fn, [diff1, diff2])
    return Compose(is_zero_fn, [total_diff])


# -------------------------------------------------------------
# Unbounded Minimalization Operator
# -------------------------------------------------------------

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
