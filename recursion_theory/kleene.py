"""Kleene's First and Second Recursion Theorems and Applications.

This module formalizes:
1. Kleene's First Recursion Theorem:
   The least fixed point of a monotone and continuous operator on partial functions
   exists and is computable (Scott fixed point theorem).
2. Kleene's Second Recursion Theorem (The Fixed-Point Theorem in Computability):
   For any total computable function f, there exists an index e such that
   phi_e is equivalent to phi_{f(e)}.
3. The S-m-n Parameter Theorem:
   Effective specialization/currying of program codes.
4. Rice's Theorem:
   Deduction of the undecidability of all non-trivial semantic properties of
   computable functions as an immediate corollary of the 2nd recursion theorem.
5. Quine Generation:
   Self-reproducing programs based on the diagonal fixed-point construction.
"""

from typing import Callable, Dict, Optional, Tuple, Any, List, Set


# Partial function type: maps int -> Optional[int] (None represents undefined / non-termination)
PartialFunction = Dict[int, int]
Functional = Callable[[PartialFunction], PartialFunction]


class KleeneFirstRecursion:
    """Formalization of Kleene's First Recursion Theorem.

    Let D be the partial order of partial functions on N ordered by graph inclusion (subset).
    An operator Phi : D -> D is:
    1. Monotone: f subset g implies Phi(f) subset g.
    2. Continuous: for any chain f_0 subset f_1 subset ..., Phi(Union f_i) = Union Phi(f_i).

    Theorem: Phi has a least fixed point fix(Phi) = Union_{k >= 0} Phi^k(empty).
    """

    @staticmethod
    def iterate(phi: Functional, steps: int) -> List[PartialFunction]:
        """Compute the sequence of approximations f_0, f_1, ..., f_{steps}.

        f_0 = {}
        f_{k+1} = phi(f_k)
        """
        approx = {}
        history = [dict(approx)]
        for _ in range(steps):
            next_approx = phi(dict(approx))
            approx.update(next_approx)
            history.append(dict(approx))
        return history

    @staticmethod
    def least_fixed_point(phi: Functional, max_iterations: int = 100) -> PartialFunction:
        """Find the least fixed point of Phi by iterating from the empty function."""
        current: PartialFunction = {}
        for _ in range(max_iterations):
            nxt = phi(dict(current))
            # If current is closed under nxt
            if all(k in current and current[k] == v for k, v in nxt.items()) and len(nxt) == len(current):
                return current
            current.update(nxt)
        return current

    @staticmethod
    def verify_monotonicity(phi: Functional, f: PartialFunction, g: PartialFunction) -> bool:
        """Verify that f subset g implies phi(f) subset phi(g)."""
        # Ensure f subset g
        for k, v in f.items():
            if k not in g or g[k] != v:
                raise ValueError("f is not a subset of g")
        phi_f = phi(f)
        phi_g = phi(g)
        for k, v in phi_f.items():
            if k not in phi_g or phi_g[k] != v:
                return False
        return True

    @staticmethod
    def verify_fixed_point(phi: Functional, f: PartialFunction) -> bool:
        """Verify that phi(f) == f on the domain where phi produces values."""
        phi_f = phi(f)
        return phi_f == f


class ProgramSystem:
    """An acceptable programming system / Godel numbering model for Kleene's theorems.

    Each program is represented by an integer index e.
    phi_e(x) computes the result of program e on input x.
    phi2_e(x, y) computes the result of 2-argument program e on (x, y).
    """

    def __init__(self):
        # Registry of 1-argument programs: index -> Callable[[int], Optional[int]]
        self._programs_1: Dict[int, Callable[[int], Optional[int]]] = {}
        # Registry of 2-argument programs: index -> Callable[[int, int], Optional[int]]
        self._programs_2: Dict[int, Callable[[int, int], Optional[int]]] = {}
        # S-1-1 table: (e, x) -> specialized index
        self._s11_table: Dict[Tuple[int, int], int] = {}
        self._next_index = 1000

    def register_program_1(self, index: int, fn: Callable[[int], Optional[int]]) -> int:
        self._programs_1[index] = fn
        return index

    def register_program_2(self, index: int, fn: Callable[[int, int], Optional[int]]) -> int:
        self._programs_2[index] = fn
        return index

    def phi(self, e: int, x: int) -> Optional[int]:
        """Evaluate program e on argument x."""
        if e not in self._programs_1:
            return None
        return self._programs_1[e](x)

    def phi2(self, e: int, x: int, y: int) -> Optional[int]:
        """Evaluate 2-argument program e on arguments (x, y)."""
        if e not in self._programs_2:
            return None
        return self._programs_2[e](x, y)

    def s11(self, e: int, x: int) -> int:
        """The S-1-1 parameter function.

        Returns an index e_x such that for all y:
          phi(e_x, y) == phi2(e, x, y)
        """
        key = (e, x)
        if key in self._s11_table:
            return self._s11_table[key]

        new_idx = self._next_index
        self._next_index += 1

        # Curried program: captures e and x
        def specialized(y: int) -> Optional[int]:
            return self.phi2(e, x, y)

        self._programs_1[new_idx] = specialized
        self._s11_table[key] = new_idx
        return new_idx

    def diagonal(self, x: int) -> int:
        """The diagonal function d(x) = s11(x, x)."""
        return self.s11(x, x)


class KleeneSecondRecursion:
    """Formalization and constructive implementation of Kleene's Second Recursion Theorem.

    Theorem (Kleene's 2nd Recursion Theorem):
    In any acceptable programming system with an S-1-1 parameter function,
    for every total computable function f : N -> N, there exists an index e
    such that phi_e and phi_{f(e)} are extensionally equivalent (phi_e ~= phi_{f(e)}).

    Proof Construction:
    1. Define the 2-argument function:
       g(x, y) = phi(f(d(x)), y)
       where d(x) = s11(x, x).
    2. Since g is computable, it has an index v in the programming system, so:
       phi2(v, x, y) = g(x, y) = phi(f(d(x)), y).
    3. Take e = d(v) = s11(v, v).
    4. Then for all y:
       phi(e, y) = phi(s11(v, v), y)
                 = phi2(v, v, y)
                 = g(v, y)
                 = phi(f(d(v)), y)
                 = phi(f(e), y).
       Hence phi_e == phi_{f(e)}. Q.E.D.
    """

    def __init__(self, system: ProgramSystem):
        self.system = system

    def find_fixed_point_index(self, f: Callable[[int], int]) -> int:
        """Construct the fixed-point index e such that phi_e ~= phi_{f(e)}."""
        # Step 1: Define g(x, y) = phi(f(d(x)), y)
        def g(x: int, y: int) -> Optional[int]:
            d_x = self.system.diagonal(x)
            f_d_x = f(d_x)
            return self.system.phi(f_d_x, y)

        # Step 2: Register g as a 2-argument program with index v
        v = self.system._next_index
        self.system._next_index += 1
        self.system.register_program_2(v, g)

        # Step 3: Compute e = d(v) = s11(v, v)
        e = self.system.diagonal(v)
        return e

    def verify_fixed_point(
        self,
        e: int,
        f: Callable[[int], int],
        test_inputs: List[int]
    ) -> bool:
        """Verify that phi_e and phi_{f(e)} agree on all test inputs."""
        fe = f(e)
        for x in test_inputs:
            res_e = self.system.phi(e, x)
            res_fe = self.system.phi(fe, x)
            if res_e != res_fe:
                return False
        return True


class ParametricRecursionTheorem:
    """Parametric form of Kleene's Second Recursion Theorem.

    For any computable g(e, p, y), there exists a computable function h(p)
    such that for all p and y:
      phi(h(p), y) ~= g(h(p), p, y).
    """

    def __init__(self, system: ProgramSystem):
        self.system = system
        self.kleene = KleeneSecondRecursion(system)

    def solve_parametric(
        self,
        g: Callable[[int, int, int], Optional[int]]
    ) -> Callable[[int], int]:
        """Construct the index transformer h(p)."""
        def h(p: int) -> int:
            # Transform g into a 1-parameter function f_p on program indices
            def f_p(e: int) -> int:
                idx = self.system._next_index
                self.system._next_index += 1
                self.system.register_program_1(idx, lambda y: g(e, p, y))
                return idx

            return self.kleene.find_fixed_point_index(f_p)

        return h


class RicesTheoremVerification:
    """Formalization and constructive verification of Rice's Theorem.

    Theorem (Rice):
    Let P be any property of partial computable functions (i.e. a set of indices
    such that phi_a == phi_b implies (a in P <-> b in P)).
    If P is non-trivial (P is neither empty nor the set of all indices),
    then P is undecidable.

    Proof (as a direct corollary of Kleene's Second Recursion Theorem):
    Assume for contradiction that P is decidable with decider D : N -> {0, 1}.
    Since P is non-trivial, pick a in P and b not in P.
    Define f(e) = b if D(e) == 1 else a.
    f is total computable.
    By Kleene's 2nd recursion theorem, there is an index e* such that:
      phi_{e*} ~= phi_{f(e*)}.
    Since P is a semantic property, e* in P <-> f(e*) in P.
    Case 1: D(e*) == 1 -> e* in P -> f(e*) = b -> f(e*) not in P. Contradiction!
    Case 2: D(e*) == 0 -> e* not in P -> f(e*) = a -> f(e*) in P. Contradiction!
    Therefore, no decider D can exist.
    """

    @staticmethod
    def derive_contradiction(
        kleene: KleeneSecondRecursion,
        decider: Callable[[int], int],
        idx_in_P: int,
        idx_not_in_P: int,
    ) -> Tuple[int, int, bool]:
        """Constructively find the contradictory index e* for any hypothesized decider.

        Returns (e_star, f(e_star), contradiction_verified).
        """
        def f(e: int) -> int:
            if decider(e) == 1:
                return idx_not_in_P
            else:
                return idx_in_P

        e_star = kleene.find_fixed_point_index(f)
        fe_star = f(e_star)

        # Contradiction check:
        # If decider says e_star in P (1), then fe_star must be idx_not_in_P
        # If decider says e_star not in P (0), then fe_star must be idx_in_P
        dec_e = decider(e_star)
        if dec_e == 1:
            valid_contradiction = (fe_star == idx_not_in_P)
        else:
            valid_contradiction = (fe_star == idx_in_P)

        return e_star, fe_star, valid_contradiction


class QuineConstructor:
    """Self-reproducing programs (Quines) constructed via the diagonal fixpoint.

    Based on the Kleene fixed point construction:
    A quine consists of two parts:
    1. An algorithm A that takes data and prints both the data and the result of applying A to data.
    2. Data D which is the quote of algorithm A.
    """

    @staticmethod
    def construct_python_quine() -> str:
        """Return a purely self-contained, valid Python quine."""
        # Standard 2-part diagonal quine
        template = 's = %r\nprint(s %% s)'
        return template % template

    @staticmethod
    def verify_quine(quine_code: str) -> bool:
        """Verify that executing quine_code produces exact copy of quine_code."""
        import io
        import sys

        old_stdout = sys.stdout
        redirected_output = io.StringIO()
        sys.stdout = redirected_output
        try:
            exec(quine_code, {})
        finally:
            sys.stdout = old_stdout

        output = redirected_output.getvalue()
        # Normalizing trailing newline if print appends newline
        return output == quine_code or output.rstrip('\n') == quine_code.rstrip('\n')
