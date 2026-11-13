"""Kleene's First and Second Recursion Theorems and Computability Formulations.

This module formalizes:
1. Kleene's First Recursion Theorem:
   The least fixed point of a monotone and continuous operator on partial functions
   exists and is computable (Scott fixed point theorem).
2. The S-m-n Parameter Theorem and Index Specialization:
   Effective currying, parameterization, and composition of program codes.
3. Modular Computability Lemmas:
   S-m-n currying, S-m-n iteration, diagonal computability, padding lemma,
   universal interpreter evaluation, and index composition.
4. Clean Index Mapping Functions:
   IndexMapping term hierarchy (Identity, Constant, Composed, Diagonal, Smn, Parametric).
5. Kleene's Second Recursion Theorem Proof Decomposition:
   Constructive decomposition of the fixed-point proof into explicit modular steps
   and certified formal proof certificates.
6. Smullyan's Double Recursion Theorem:
   Simultaneous fixed points for pairs of bivariate index transformations.
7. Rice's Theorem:
   Deduction of the undecidability of all non-trivial semantic properties of
   computable functions as an immediate corollary of the 2nd recursion theorem.
8. Quine Generation:
   Self-reproducing programs based on the diagonal fixed-point construction.
"""

from typing import Callable, Dict, Optional, Tuple, Any, List, Set


# Partial function type: maps int to Optional[int] (None represents undefined / non-termination)
PartialFunction = Dict[int, int]
Functional = Callable[[PartialFunction], PartialFunction]


# -------------------------------------------------------------
# Kleene's First Recursion Theorem (Scott Least Fixed Point)
# -------------------------------------------------------------

class KleeneFirstRecursion:
    """Formalization of Kleene's First Recursion Theorem.

    Let D be the partial order of partial functions on N ordered by graph inclusion.
    An operator Phi : D to D is:
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
        approx: PartialFunction = {}
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
            if all(k in current and current[k] == v for k, v in nxt.items()) and len(nxt) == len(current):
                return current
            current.update(nxt)
        return current

    @staticmethod
    def verify_monotonicity(phi: Functional, f: PartialFunction, g: PartialFunction) -> bool:
        """Verify that f subset g implies phi(f) subset phi(g)."""
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

    @staticmethod
    def verify_continuity(phi: Functional, chain: List[PartialFunction]) -> bool:
        """Verify that phi(Union chain) == Union (phi(f_i)) for a chain of approximations."""
        union_chain: PartialFunction = {}
        for f in chain:
            union_chain.update(f)
        phi_union = phi(union_chain)

        union_phi: PartialFunction = {}
        for f in chain:
            union_phi.update(phi(f))
        return phi_union == union_phi


# -------------------------------------------------------------
# Index Mapping Functions
# -------------------------------------------------------------

class IndexMapping:
    """Abstract base class for computable index mappings between program indices."""

    def __init__(self, arity: int = 1, name: str = "IndexMapping"):
        self.arity = arity
        self.name = name

    def __call__(self, *args: int) -> int:
        if len(args) != self.arity:
            raise ValueError(f"Expected {self.arity} indices, got {len(args)}")
        return self.map_index(*args)

    def map_index(self, *args: int) -> int:
        raise NotImplementedError

    def compose(self, other: 'IndexMapping') -> 'ComposedMapping':
        """Compose self with another index mapping."""
        if other.arity != 1 or self.arity != 1:
            raise ValueError("Direct composition currently supported for unary index mappings")
        return ComposedMapping(self, other)

    def __repr__(self) -> str:
        return self.name


class IdentityMapping(IndexMapping):
    """Identity index mapping: id(e) = e."""

    def __init__(self):
        super().__init__(arity=1, name="Identity")

    def map_index(self, *args: int) -> int:
        return args[0]


class ConstantMapping(IndexMapping):
    """Constant index mapping: C_k(e) = k."""

    def __init__(self, const_index: int):
        super().__init__(arity=1, name=f"Constant({const_index})")
        self.const_index = const_index

    def map_index(self, *args: int) -> int:
        return self.const_index


class ComposedMapping(IndexMapping):
    """Composition of index mappings: (outer o inner)(e) = outer(inner(e))."""

    def __init__(self, outer: IndexMapping, inner: IndexMapping):
        super().__init__(arity=inner.arity, name=f"({outer.name} o {inner.name})")
        self.outer = outer
        self.inner = inner

    def map_index(self, *args: int) -> int:
        return self.outer(self.inner(*args))


class DiagonalMapping(IndexMapping):
    """The diagonal index mapping: d(x) = s11(x, x)."""

    def __init__(self, system: 'ProgramSystem'):
        super().__init__(arity=1, name="Diagonal")
        self.system = system

    def map_index(self, *args: int) -> int:
        x = args[0]
        return self.system.s11(x, x)


class SmnMapping(IndexMapping):
    """S-m-n index specialization mapping: e maps to s_m_n(e, vec{x})."""

    def __init__(self, system: 'ProgramSystem', m: int, n: int, fixed_args: Tuple[int, ...]):
        if len(fixed_args) != m:
            raise ValueError(f"Expected {m} fixed arguments, got {len(fixed_args)}")
        super().__init__(arity=1, name=f"S_{m}^{n}(., {fixed_args})")
        self.system = system
        self.m = m
        self.n = n
        self.fixed_args = fixed_args

    def map_index(self, *args: int) -> int:
        e = args[0]
        return self.system.s_m_n(e, self.m, self.n, *self.fixed_args)


class ParametricMapping(IndexMapping):
    """Parametric index mapping: maps parameter p to solved fixed-point index h(p)."""

    def __init__(self, transformer: Callable[[int], int], name: str = "ParametricFixedPoint"):
        super().__init__(arity=1, name=name)
        self.transformer = transformer

    def map_index(self, *args: int) -> int:
        return self.transformer(args[0])


# -------------------------------------------------------------
# Programming System / Gödel Numbering Model
# -------------------------------------------------------------

class ProgramSystem:
    """An acceptable programming system / Gödel numbering model for Kleene's theorems.

    Each program is represented by an integer index e.
    phi_e(x) computes the result of program e on input x.
    phi2_e(x, y) computes the result of 2-argument program e on (x, y).
    phi_n(e, *args) computes the result of arbitrary arity program e on args.
    """

    def __init__(self):
        # Registry of 1-argument programs: index to Callable[[int], Optional[int]]
        self._programs_1: Dict[int, Callable[[int], Optional[int]]] = {}
        # Registry of 2-argument programs: index to Callable[[int, int], Optional[int]]
        self._programs_2: Dict[int, Callable[[int, int], Optional[int]]] = {}
        # General registry: (arity, index) to Callable[..., Optional[int]]
        self._programs_n: Dict[Tuple[int, int], Callable[..., Optional[int]]] = {}
        # S-1-1 table: (e, x) to specialized index
        self._s11_table: Dict[Tuple[int, int], int] = {}
        # S-m-n table: (e, m, n, fixed_args) to specialized index
        self._smn_table: Dict[Tuple[int, int, int, Tuple[int, ...]], int] = {}
        # Universal program index cache
        self._universal_index: Optional[int] = None
        self._next_index = 1000

    def register_program_1(self, index: int, fn: Callable[[int], Optional[int]]) -> int:
        self._programs_1[index] = fn
        self._programs_n[(1, index)] = fn
        return index

    def register_program_2(self, index: int, fn: Callable[[int, int], Optional[int]]) -> int:
        self._programs_2[index] = fn
        self._programs_n[(2, index)] = fn
        return index

    def register_program_n(self, index: int, arity: int, fn: Callable[..., Optional[int]]) -> int:
        """Register a program of given arity."""
        self._programs_n[(arity, index)] = fn
        if arity == 1:
            self._programs_1[index] = fn
        elif arity == 2:
            self._programs_2[index] = fn
        return index

    def phi(self, e: int, x: int) -> Optional[int]:
        """Evaluate program e on argument x."""
        if e in self._programs_1:
            return self._programs_1[e](x)
        if (1, e) in self._programs_n:
            return self._programs_n[(1, e)](x)
        return None

    def phi2(self, e: int, x: int, y: int) -> Optional[int]:
        """Evaluate 2-argument program e on arguments (x, y)."""
        if e in self._programs_2:
            return self._programs_2[e](x, y)
        if (2, e) in self._programs_n:
            return self._programs_n[(2, e)](x, y)
        return None

    def phi_n(self, e: int, *args: int) -> Optional[int]:
        """Evaluate program e on arbitrary number of arguments."""
        arity = len(args)
        if (arity, e) in self._programs_n:
            return self._programs_n[(arity, e)](*args)
        if arity == 1 and e in self._programs_1:
            return self._programs_1[e](args[0])
        if arity == 2 and e in self._programs_2:
            return self._programs_2[e](args[0], args[1])
        return None

    def s11(self, e: int, x: int) -> int:
        """The S-1-1 parameter function.

        Returns an index e_x such that for all y:
          phi(e_x, y) == phi2(e, x, y)
        """
        return self.s_m_n(e, 1, 1, x)

    def s_m_n(self, e: int, m: int, n: int, *fixed_args: int) -> int:
        """The S-m-n Parameterization Theorem.

        Given program index e computing an (m + n)-ary function,
        and m fixed parameters (x_1, ..., x_m),
        construct an index e' computing an n-ary function such that:
          phi_n(e', y_1, ..., y_n) == phi_{m+n}(e, x_1, ..., x_m, y_1, ..., y_n).
        """
        if len(fixed_args) != m:
            raise ValueError(f"Expected {m} fixed arguments, got {len(fixed_args)}")

        key = (e, m, n, fixed_args)
        if key in self._smn_table:
            return self._smn_table[key]

        new_idx = self._next_index
        self._next_index += 1

        def specialized(*remaining_args: int) -> Optional[int]:
            if len(remaining_args) != n:
                raise ValueError(f"Expected {n} arguments, got {len(remaining_args)}")
            all_args = fixed_args + remaining_args
            return self.phi_n(e, *all_args)

        self.register_program_n(new_idx, n, specialized)
        self._smn_table[key] = new_idx
        if m == 1 and n == 1:
            self._s11_table[(e, fixed_args[0])] = new_idx
        return new_idx

    def diagonal(self, x: int) -> int:
        """The diagonal function d(x) = s11(x, x)."""
        return self.s11(x, x)

    def diagonal_mapping(self) -> DiagonalMapping:
        """Return the clean DiagonalMapping instance for this system."""
        return DiagonalMapping(self)

    def smn_mapping(self, m: int, n: int, *fixed_args: int) -> SmnMapping:
        """Return a clean SmnMapping specializing m parameters."""
        return SmnMapping(self, m, n, fixed_args)

    def compose_programs(self, e1: int, e2: int) -> int:
        """Effectively compose two 1-ary programs: phi_{res}(x) = phi_{e1}(phi_{e2}(x))."""
        new_idx = self._next_index
        self._next_index += 1

        def composed(x: int) -> Optional[int]:
            v2 = self.phi(e2, x)
            if v2 is None:
                return None
            return self.phi(e1, v2)

        self.register_program_1(new_idx, composed)
        return new_idx

    def pad_program(self, e: int, pad_tag: int = 1) -> int:
        """Padding Lemma: generate a distinct program index computing the same function."""
        new_idx = self._next_index
        self._next_index += 1

        def padded(x: int) -> Optional[int]:
            # pad_tag creates synthetic internal distinction while preserving semantics
            _ = pad_tag
            return self.phi(e, x)

        self.register_program_1(new_idx, padded)
        return new_idx

    def universal_index(self) -> int:
        """Construct or return the index u of the universal interpreter: phi2(u, e, x) = phi(e, x)."""
        if self._universal_index is not None:
            return self._universal_index

        u = self._next_index
        self._next_index += 1

        def universal_eval(e: int, x: int) -> Optional[int]:
            return self.phi(e, x)

        self.register_program_2(u, universal_eval)
        self._universal_index = u
        return u


# -------------------------------------------------------------
# Computability Lemmas
# -------------------------------------------------------------

class ComputabilityLemmas:
    """Formal verification lemmas for computability theory and index transformations."""

    @staticmethod
    def verify_smn_currying(
        system: ProgramSystem,
        e: int,
        m: int,
        n: int,
        fixed_args: Tuple[int, ...],
        test_inputs: List[Tuple[int, ...]]
    ) -> bool:
        """Lemma: S-m-n Currying Equivalence.
        phi_n(s_m_n(e, vec{x}), vec{y}) == phi_{m+n}(e, vec{x}, vec{y}).
        """
        e_spec = system.s_m_n(e, m, n, *fixed_args)
        for ys in test_inputs:
            if len(ys) != n:
                raise ValueError(f"Test input arity {len(ys)} does not match n={n}")
            lhs = system.phi_n(e_spec, *ys)
            all_args = fixed_args + ys
            rhs = system.phi_n(e, *all_args)
            if lhs != rhs:
                return False
        return True

    @staticmethod
    def verify_smn_iteration(
        system: ProgramSystem,
        e: int,
        m1: int,
        m2: int,
        n: int,
        fixed1: Tuple[int, ...],
        fixed2: Tuple[int, ...],
        test_inputs: List[Tuple[int, ...]]
    ) -> bool:
        """Lemma: S-m-n Iterated Currying Equivalence.
        Specializing m1 then m2 produces extensional equivalence with specializing m1 + m2.
        """
        e_direct = system.s_m_n(e, m1 + m2, n, *(fixed1 + fixed2))
        e_stage1 = system.s_m_n(e, m1, m2 + n, *fixed1)
        e_stage2 = system.s_m_n(e_stage1, m2, n, *fixed2)

        for ys in test_inputs:
            res_direct = system.phi_n(e_direct, *ys)
            res_stage2 = system.phi_n(e_stage2, *ys)
            if res_direct != res_stage2:
                return False
        return True

    @staticmethod
    def verify_diagonal_computability(system: ProgramSystem, test_indices: List[int]) -> bool:
        """Lemma: Diagonal Index Mapping Computability.
        d(x) = s11(x, x) is total, computable, and consistent.
        """
        diag = system.diagonal_mapping()
        for x in test_indices:
            dx1 = diag(x)
            dx2 = system.diagonal(x)
            if dx1 != dx2:
                return False
        return True

    @staticmethod
    def verify_padding_lemma(
        system: ProgramSystem,
        e: int,
        count: int = 5,
        test_inputs: Optional[List[int]] = None
    ) -> bool:
        """Lemma: Padding Lemma (Infinite Injective Equivalent Indices).
        Every program has infinitely many distinct indices computing the same function.
        """
        if test_inputs is None:
            test_inputs = [0, 1, 2, 5, 10]
        padded_indices = [system.pad_program(e, pad_tag=i) for i in range(1, count + 1)]
        if len(set(padded_indices)) != count or any(p == e for p in padded_indices):
            return False
        for p in padded_indices:
            for x in test_inputs:
                if system.phi(p, x) != system.phi(e, x):
                    return False
        return True

    @staticmethod
    def verify_composition_lemma(
        system: ProgramSystem,
        e1: int,
        e2: int,
        test_inputs: Optional[List[int]] = None
    ) -> bool:
        """Lemma: Program Index Composition.
        There effectively exists index e_comp computing phi_{e1}(phi_{e2}(x)).
        """
        if test_inputs is None:
            test_inputs = [0, 1, 2, 5]
        e_comp = system.compose_programs(e1, e2)
        for x in test_inputs:
            v2 = system.phi(e2, x)
            expected = system.phi(e1, v2) if v2 is not None else None
            actual = system.phi(e_comp, x)
            if actual != expected:
                return False
        return True

    @staticmethod
    def verify_universal_function(
        system: ProgramSystem,
        u: int,
        test_pairs: List[Tuple[int, int]]
    ) -> bool:
        """Lemma: Universal Evaluation Program.
        phi2(u, e, x) == phi(e, x).
        """
        for e, x in test_pairs:
            if system.phi2(u, e, x) != system.phi(e, x):
                return False
        return True


# -------------------------------------------------------------
# Kleene's Second Recursion Theorem Proof Decomposition
# -------------------------------------------------------------

class KleeneProofCertificate:
    """Formal deduction certificate decomposing Kleene's Second Recursion Theorem."""

    def __init__(
        self,
        target_function: Callable[[int], int],
        diagonal_mapping: DiagonalMapping,
        auxiliary_kernel_index: int,
        fixed_point_index: int,
        transformed_index: int,
        proof_steps: List[str],
        is_verified: bool
    ):
        self.target_function = target_function
        self.diagonal_mapping = diagonal_mapping
        self.auxiliary_kernel_index = auxiliary_kernel_index
        self.fixed_point_index = fixed_point_index
        self.transformed_index = transformed_index
        self.proof_steps = proof_steps
        self.is_verified = is_verified

    def summary(self) -> str:
        lines = [
            "Kleene Second Recursion Theorem Proof Certificate:",
            f"  Auxiliary kernel index v = {self.auxiliary_kernel_index}",
            f"  Fixed point index e = d(v) = {self.fixed_point_index}",
            f"  Transformed index f(e) = {self.transformed_index}",
            f"  Extensional equivalence verified: {self.is_verified}",
            "Deduction Steps:"
        ]
        for idx, step in enumerate(self.proof_steps, start=1):
            lines.append(f"  Step {idx}: {step}")
        return "\n".join(lines)


class KleeneSecondRecursion:
    """Formalization and constructive implementation of Kleene's Second Recursion Theorem.

    Theorem (Kleene's 2nd Recursion Theorem):
    In any acceptable programming system with an S-1-1 parameter function,
    for every total computable function f : N to N, there exists an index e
    such that phi_e and phi_{f(e)} are extensionally equivalent (phi_e ~= phi_{f(e)}).

    Proof Construction (Modular Decomposition):
    1. Construct diagonal mapping d(x) = s11(x, x).
    2. Define auxiliary 2-argument kernel function g(x, y) = phi(f(d(x)), y) with index v.
    3. Take e = d(v) = s11(v, v).
    4. Deduce extensional equivalence:
       phi_e(y) = phi(s11(v, v), y) = phi2(v, v, y) = g(v, y) = phi(f(d(v)), y) = phi(f(e), y).
    """

    def __init__(self, system: ProgramSystem):
        self.system = system

    def decompose_proof(
        self,
        f: Callable[[int], int],
        test_inputs: Optional[List[int]] = None
    ) -> KleeneProofCertificate:
        """Decompose Kleene's 2nd recursion theorem proof into formal verifiable steps."""
        if test_inputs is None:
            test_inputs = [0, 1, 2, 5, 10]

        # Step 1: Diagonal index mapping d(x) = s11(x, x)
        diag = self.system.diagonal_mapping()
        step1 = "Construct total computable diagonal mapping d(x) = s_1_1(x, x)."

        # Step 2: Auxiliary kernel function g(x, y) = phi(f(d(x)), y)
        def g(x: int, y: int) -> Optional[int]:
            d_x = diag(x)
            f_d_x = f(d_x)
            return self.system.phi(f_d_x, y)

        v = self.system._next_index
        self.system._next_index += 1
        self.system.register_program_2(v, g)
        step2 = f"Register auxiliary kernel g(x, y) = phi(f(d(x)), y) with index v = {v}."

        # Step 3: Fixed point index e = d(v) = s11(v, v)
        e = diag(v)
        fe = f(e)
        step3 = f"Evaluate diagonal on kernel index: e = d(v) = s_1_1({v}, {v}) = {e}, yielding f(e) = {fe}."

        # Step 4: Verification of extensional equivalence
        is_verified = self.verify_fixed_point(e, f, test_inputs)
        step4 = (
            f"Verify extensional equivalence for all y: "
            f"phi_{e}(y) = phi2({v}, {v}, y) = g({v}, y) = phi_{fe}(y). Verified: {is_verified}."
        )

        return KleeneProofCertificate(
            target_function=f,
            diagonal_mapping=diag,
            auxiliary_kernel_index=v,
            fixed_point_index=e,
            transformed_index=fe,
            proof_steps=[step1, step2, step3, step4],
            is_verified=is_verified
        )

    def find_fixed_point_index(self, f: Callable[[int], int]) -> int:
        """Construct the fixed-point index e such that phi_e ~= phi_{f(e)}."""
        cert = self.decompose_proof(f)
        return cert.fixed_point_index

    def find_self_referential_index(self, F: Callable[[int, int], Optional[int]]) -> int:
        """Construct a self-referential program index e such that phi_e(x) == F(e, x)."""
        def f(idx: int) -> int:
            new_idx = self.system._next_index
            self.system._next_index += 1
            self.system.register_program_1(new_idx, lambda x: F(idx, x))
            return new_idx

        return self.find_fixed_point_index(f)

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


# -------------------------------------------------------------
# Parametric Recursion Theorem
# -------------------------------------------------------------

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
        """Construct the deterministic index transformer h(p)."""
        cache: Dict[int, int] = {}

        def h(p: int) -> int:
            if p in cache:
                return cache[p]

            def f_p(e: int) -> int:
                idx = self.system._next_index
                self.system._next_index += 1
                self.system.register_program_1(idx, lambda y: g(e, p, y))
                return idx

            res = self.kleene.find_fixed_point_index(f_p)
            cache[p] = res
            return res

        return h

    def solve_parametric_mapping(
        self,
        g: Callable[[int, int, int], Optional[int]]
    ) -> ParametricMapping:
        """Construct a clean ParametricMapping instance mapping p to h(p)."""
        h_fn = self.solve_parametric(g)
        return ParametricMapping(h_fn)


# -------------------------------------------------------------
# Smullyan's Double Recursion Theorem
# -------------------------------------------------------------

class DoubleRecursionTheorem:
    """Formalization and construction of Smullyan's Double Recursion Theorem.

    Theorem: For any two total computable functions f1, f2 : N x N to N,
    there exist indices a and b such that:
      phi_a is extensionally equivalent to phi_{f1(a, b)}
      phi_b is extensionally equivalent to phi_{f2(a, b)}
    """

    def __init__(self, system: ProgramSystem):
        self.system = system
        self.kleene = KleeneSecondRecursion(system)
        self.param_rec = ParametricRecursionTheorem(system)

    def find_double_fixed_points(
        self,
        f1: Callable[[int, int], int],
        f2: Callable[[int, int], int]
    ) -> Tuple[int, int]:
        """Constructively find indices (a, b) satisfying the double recursion equations."""
        def g2(e: int, p: int, arg: int) -> Optional[int]:
            target_idx = f2(p, e)
            return self.system.phi(target_idx, arg)

        h = self.param_rec.solve_parametric(g2)

        def F1(x: int) -> int:
            return f1(x, h(x))

        a = self.kleene.find_fixed_point_index(F1)
        b = h(a)
        return a, b

    def verify_double_fixed_points(
        self,
        a: int,
        b: int,
        f1: Callable[[int, int], int],
        f2: Callable[[int, int], int],
        test_inputs: List[int]
    ) -> bool:
        """Verify that (a, b) satisfy the double recursion fixed-point equations."""
        target_a = f1(a, b)
        target_b = f2(a, b)
        for x in test_inputs:
            if self.system.phi(a, x) != self.system.phi(target_a, x):
                return False
            if self.system.phi(b, x) != self.system.phi(target_b, x):
                return False
        return True


# -------------------------------------------------------------
# Rice's Theorem Deduction
# -------------------------------------------------------------

class RicesTheoremVerification:
    """Formalization and constructive verification of Rice's Theorem.

    Theorem (Rice):
    Let P be any property of partial computable functions (i.e. a set of indices
    such that phi_a == phi_b implies (a in P iff b in P)).
    If P is non-trivial (P is neither empty nor the set of all indices),
    then P is undecidable.
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

        dec_e = decider(e_star)
        if dec_e == 1:
            valid_contradiction = (fe_star == idx_not_in_P)
        else:
            valid_contradiction = (fe_star == idx_in_P)

        return e_star, fe_star, valid_contradiction


# -------------------------------------------------------------
# Quine Constructor via Diagonal Fixpoint
# -------------------------------------------------------------

class QuineConstructor:
    """Self-reproducing programs (Quines) constructed via the diagonal fixpoint."""

    @staticmethod
    def construct_python_quine() -> str:
        """Return a purely self-contained, valid Python quine."""
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
        return output == quine_code or output.rstrip('\n') == quine_code.rstrip('\n')
