"""Untyped Lambda Calculus and Fixed-Point Combinators.

This module formalizes:
1. Pure Lambda Calculus Term AST (Var, Abs, App) with capture-avoiding substitution.
2. Normal-order and Applicative-order beta-reduction.
3. Fixed-point combinators:
   - Curry's Y combinator: Y = \\f. (\\x. f (x x)) (\\x. f (x x))
   - Turing's Theta combinator: Theta = (\\x.\\y. y (x x y)) (\\x.\\y. y (x x y))
   - Call-by-value Z combinator: Z = \\f. (\\x. f (\\v. x x v)) (\\x. f (\\v. x x v))
4. Church encodings (booleans, pairs, numerals, arithmetic).
5. Recursive function computation via fixed-point combinators without native recursion.
"""

from typing import Set, Optional, Tuple, List


class Term:
    """Base class for untyped lambda calculus terms."""

    def free_vars(self) -> Set[str]:
        raise NotImplementedError

    def substitute(self, var: str, replacement: "Term") -> "Term":
        raise NotImplementedError

    def to_string(self) -> str:
        raise NotImplementedError

    def __str__(self) -> str:
        return self.to_string()

    def __repr__(self) -> str:
        return self.to_string()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Term):
            return False
        return self.to_string() == other.to_string()


class Var(Term):
    """Variable term."""

    def __init__(self, name: str):
        self.name = name

    def free_vars(self) -> Set[str]:
        return {self.name}

    def substitute(self, var: str, replacement: Term) -> Term:
        if self.name == var:
            return replacement
        return self

    def to_string(self) -> str:
        return self.name


class Abs(Term):
    """Abstraction (lambda) term: \\param. body."""

    def __init__(self, param: str, body: Term):
        self.param = param
        self.body = body

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.param}

    def substitute(self, var: str, replacement: Term) -> Term:
        if self.param == var:
            # Shadowed
            return self

        # If parameter occurs in free vars of replacement, rename to avoid capture
        repl_free = replacement.free_vars()
        if self.param in repl_free:
            fresh_param = self._fresh_var(self.param, self.body.free_vars() | repl_free | {var})
            renamed_body = self.body.substitute(self.param, Var(fresh_param))
            return Abs(fresh_param, renamed_body.substitute(var, replacement))

        return Abs(self.param, self.body.substitute(var, replacement))

    def _fresh_var(self, base: str, avoid: Set[str]) -> str:
        i = 1
        candidate = f"{base}_{i}"
        while candidate in avoid:
            i += 1
            candidate = f"{base}_{i}"
        return candidate

    def to_string(self) -> str:
        return f"(\\{self.param}. {self.body.to_string()})"


class App(Term):
    """Application term: (rator rand)."""

    def __init__(self, rator: Term, rand: Term):
        self.rator = rator
        self.rand = rand

    def free_vars(self) -> Set[str]:
        return self.rator.free_vars() | self.rand.free_vars()

    def substitute(self, var: str, replacement: Term) -> Term:
        return App(
            self.rator.substitute(var, replacement),
            self.rand.substitute(var, replacement),
        )

    def to_string(self) -> str:
        return f"({self.rator.to_string()} {self.rand.to_string()})"


def reduce_step(term: Term) -> Optional[Term]:
    """Single-step normal-order reduction (leftmost outermost redex).

    Returns the reduced term or None if in normal form.
    """
    if isinstance(term, Var):
        return None

    if isinstance(term, Abs):
        new_body = reduce_step(term.body)
        if new_body is not None:
            return Abs(term.param, new_body)
        return None

    if isinstance(term, App):
        # Beta redex: (\\x. B) A
        if isinstance(term.rator, Abs):
            return term.rator.body.substitute(term.rator.param, term.rand)

        # Left side first (normal order)
        new_rator = reduce_step(term.rator)
        if new_rator is not None:
            return App(new_rator, term.rand)

        # Right side
        new_rand = reduce_step(term.rand)
        if new_rand is not None:
            return App(term.rator, new_rand)

        return None

    return None


def reduce_normal_order(term: Term, max_steps: int = 1000) -> Tuple[Term, int]:
    """Reduce term to normal form using normal order reduction.

    Returns (normal_form_term, steps_taken).
    """
    current = term
    steps = 0
    while steps < max_steps:
        nxt = reduce_step(current)
        if nxt is None:
            return current, steps
        current = nxt
        steps += 1
    return current, steps


# -------------------------------------------------------------
# Fixed-Point Combinators
# -------------------------------------------------------------

def Y_combinator() -> Term:
    """Curry's Y combinator:

    Y = \\f. (\\x. f (x x)) (\\x. f (x x))
    Fixed-point property: Y F =_beta F (Y F)
    """
    inner = Abs("x", App(Var("f"), App(Var("x"), Var("x"))))
    return Abs("f", App(inner, inner))


def Theta_combinator() -> Term:
    """Turing's Theta combinator:

    A = \\x. \\y. y (x x y)
    Theta = A A
    Fixed-point property: Theta F ->+ F (Theta F) (reduces in standard reduction!)
    """
    A = Abs("x", Abs("y", App(Var("y"), App(App(Var("x"), Var("x")), Var("y")))))
    return App(A, A)


def Z_combinator() -> Term:
    """Call-by-value / Applicative-order fixed-point combinator Z:

    Z = \\f. (\\x. f (\\v. x x v)) (\\x. f (\\v. x x v))
    """
    inner = Abs("x", App(Var("f"), Abs("v", App(App(Var("x"), Var("x")), Var("v")))))
    return Abs("f", App(inner, inner))


# -------------------------------------------------------------
# Church Encodings
# -------------------------------------------------------------

def church_bool(b: bool) -> Term:
    """Church booleans: tru = \\t.\\f. t, fls = \\t.\\f. f."""
    if b:
        return Abs("t", Abs("f", Var("t")))
    else:
        return Abs("t", Abs("f", Var("f")))


tru = church_bool(True)
fls = church_bool(False)


def church_pair(first: Term, second: Term) -> Term:
    """Church pair: \\b. b first second."""
    return Abs("b", App(App(Var("b"), first), second))


def fst() -> Term:
    """fst = \\p. p tru."""
    return Abs("p", App(Var("p"), tru))


def snd() -> Term:
    """snd = \\p. p fls."""
    return Abs("p", App(Var("p"), fls))


def church_numeral(n: int) -> Term:
    """Church numeral c_n = \\s. \\z. s^n z."""
    body: Term = Var("z")
    for _ in range(n):
        body = App(Var("s"), body)
    return Abs("s", Abs("z", body))


def church_to_int(term: Term, max_steps: int = 2000) -> Optional[int]:
    """Convert a Church numeral term to a Python int by applying (+1) and 0."""
    # Test application: term (\\n. n + 1) 0 in lambda calculus
    # Represent (+1) and 0 symbolically
    counter = 0
    curr, _ = reduce_normal_order(term, max_steps)
    if not isinstance(curr, Abs):
        return None
    s_param = curr.param
    body1 = curr.body
    if not isinstance(body1, Abs):
        return None
    z_param = body1.param
    body2 = body1.body

    # Count applications of s_param to z_param
    curr_expr = body2
    while isinstance(curr_expr, App) and isinstance(curr_expr.rator, Var) and curr_expr.rator.name == s_param:
        counter += 1
        curr_expr = curr_expr.rand

    if isinstance(curr_expr, Var) and curr_expr.name == z_param:
        return counter
    return None


def succ() -> Term:
    """Successor: \\n. \\s. \\z. s (n s z)."""
    return Abs("n", Abs("s", Abs("z", App(Var("s"), App(App(Var("n"), Var("s")), Var("z"))))))


def plus() -> Term:
    """Addition: \\m. \\n. \\s. \\z. m s (n s z)."""
    return Abs("m", Abs("n", Abs("s", Abs("z", App(App(Var("m"), Var("s")), App(App(Var("n"), Var("s")), Var("z")))))))


def times() -> Term:
    """Multiplication: \\m. \\n. \\s. m (n s)."""
    return Abs("m", Abs("n", Abs("s", App(Var("m"), App(Var("n"), Var("s"))))))


def iszero() -> Term:
    """iszero = \\n. n (\\x. fls) tru."""
    return Abs("n", App(App(Var("n"), Abs("x", fls)), tru))


def pred() -> Term:
    """Predecessor using pairs:

    pred = \\n. fst (n (\\p. pair (snd p) (succ (snd p))) (pair c0 c0))
    """
    c0 = church_numeral(0)
    step = Abs("p", church_pair(App(snd(), Var("p")), App(succ(), App(snd(), Var("p")))))
    base = church_pair(c0, c0)
    return Abs("n", App(fst(), App(App(Var("n"), step), base)))


def factorial_functional() -> Term:
    """Recursive factorial functional F:

    F = \\f. \\n. iszero n (c1) (times n (f (pred n)))
    Factorial = Y F
    """
    c1 = church_numeral(1)
    body = App(
        App(App(iszero(), Var("n")), c1),
        App(App(times(), Var("n")), App(Var("f"), App(pred(), Var("n")))),
    )
    return Abs("f", Abs("n", body))


def make_recursive_factorial() -> Term:
    """Construct factorial function using Turing's Theta combinator."""
    return App(Theta_combinator(), factorial_functional())
