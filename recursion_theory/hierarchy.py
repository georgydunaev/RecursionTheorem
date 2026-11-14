"""Arithmetical Hierarchy, Post's Theorem, and Shoenfield Limit Lemma.

This module formalizes:
1. Arithmetical Hierarchy (Sigma_n^0, Pi_n^0, Delta_n^0):
   - Quantifier enum (EXISTS, FORALL) and QuantifierPrefix.
   - Classification of relations by quantifier alternations over computable matrices.
   - Contraction of like quantifiers using Cantor pairing.
   - Dual formulas under negation.
   - Bounded evaluation of arithmetical formulas.
2. Shoenfield Limit Lemma:
   - Delta_2^0 sets as limits of computable approximations: chi_A(x) = lim_{s -> infty} g(x, s).
   - Mind changes, modulus of convergence, and stabilization stage.
   - Bidirectional translation between Delta_2^0 formulas and limit approximations.
3. Post's Theorem:
   - Connection between the arithmetical hierarchy and Turing jumps:
     * Sigma_1^0 <==> Computably Enumerable (c.e.)
     * Delta_1^0 <==> Computable (decidable)
     * Sigma_{n+1}^0 <==> Computably enumerable relative to 0^(n)
     * Delta_{n+1}^0 <==> Turing reducible to 0^(n) (<=_T 0^(n))
4. Completeness and Undecidability:
   - Sigma_1^0-completeness of the Halting Problem K = 0'.
   - Pi_1^0-completeness of the Empty Problem Empty.
   - Sigma_2^0-completeness of the Finiteness Problem Fin.
   - Pi_2^0-completeness of the Totality Problem Tot.
"""

from enum import Enum
from typing import Callable, Dict, List, Optional, Set, Tuple, Union, Iterable, Any
from recursion_theory.primitive_recursion import cantor_pair, cantor_unpair
from recursion_theory.myhill import ManyOneReduction


# -------------------------------------------------------------
# Quantifiers and Quantifier Prefix
# -------------------------------------------------------------

class Quantifier(Enum):
    EXISTS = "exists"
    FORALL = "forall"

    def dual(self) -> 'Quantifier':
        """Invert quantifier under negation."""
        return Quantifier.FORALL if self == Quantifier.EXISTS else Quantifier.EXISTS

    def __repr__(self) -> str:
        return self.value


class QuantifierPrefix:
    """A sequence of alternating or repeated quantifiers."""

    def __init__(self, quantifiers: Iterable[Quantifier]):
        self.quantifiers: Tuple[Quantifier, ...] = tuple(quantifiers)

    def __len__(self) -> int:
        return len(self.quantifiers)

    def __iter__(self):
        return iter(self.quantifiers)

    def __getitem__(self, idx: int) -> Quantifier:
        return self.quantifiers[idx]

    def dual(self) -> 'QuantifierPrefix':
        """Negation of prefix: inverts every quantifier."""
        return QuantifierPrefix(q.dual() for q in self.quantifiers)

    def contract_adjacent(self) -> 'QuantifierPrefix':
        """Contract adjacent identical quantifiers into a single quantifier.

        e.g., [exists, exists, forall] contracts to [exists, forall].
        """
        if not self.quantifiers:
            return QuantifierPrefix([])
        contracted = [self.quantifiers[0]]
        for q in self.quantifiers[1:]:
            if q != contracted[-1]:
                contracted.append(q)
        return QuantifierPrefix(contracted)

    def classification(self) -> Tuple[str, int]:
        """Classify prefix into (class_name, n).

        Returns ("Delta", 0) for empty prefix,
        or ("Sigma", n) / ("Pi", n) after contracting adjacent quantifiers.
        """
        contracted = self.contract_adjacent()
        if len(contracted) == 0:
            return ("Delta", 0)
        leading = contracted[0]
        n = len(contracted)
        class_name = "Sigma" if leading == Quantifier.EXISTS else "Pi"
        return (class_name, n)

    def __repr__(self) -> str:
        cls, n = self.classification()
        raw = " ".join(q.value for q in self.quantifiers)
        return f"QuantifierPrefix({cls}_{n}^0: [{raw}])"


# -------------------------------------------------------------
# Arithmetical Formula
# -------------------------------------------------------------

class ArithmeticalFormula:
    """An arithmetical formula: Q_1 y_1 ... Q_k y_k P(x, y_1, ..., y_k).

    P is a computable matrix (relation), and Q_1 ... Q_k is the quantifier prefix.
    """

    def __init__(
        self,
        prefix: QuantifierPrefix,
        matrix: Callable[..., bool],
        name: str = "ArithmeticalFormula",
    ):
        self.prefix = prefix
        self.matrix = matrix
        self.name = name

    def classify(self) -> Tuple[str, int]:
        """Return (class_name, n) in the arithmetical hierarchy."""
        return self.prefix.classification()

    def dual(self) -> 'ArithmeticalFormula':
        """Construct the negated formula by duality."""
        dual_prefix = self.prefix.dual()
        dual_matrix = lambda *args: not self.matrix(*args)
        return ArithmeticalFormula(
            prefix=dual_prefix,
            matrix=dual_matrix,
            name=f"not({self.name})",
        )

    def evaluate_bounded(self, x: int, search_bounds: Union[int, List[int]]) -> bool:
        """Evaluate the formula with search bound(s) on quantified variables.

        For each quantified variable y_i, search is restricted to 0 <= y_i < B_i.
        """
        k = len(self.prefix)
        if isinstance(search_bounds, int):
            bounds = [search_bounds] * k
        else:
            bounds = list(search_bounds)
            if len(bounds) < k:
                bounds.extend([bounds[-1] if bounds else 10] * (k - len(bounds)))

        def _rec(i: int, current_args: List[int]) -> bool:
            if i == k:
                return bool(self.matrix(x, *current_args))
            q = self.prefix[i]
            bound = bounds[i]
            if q == Quantifier.EXISTS:
                for y in range(bound):
                    if _rec(i + 1, current_args + [y]):
                        return True
                return False
            else:  # FORALL
                for y in range(bound):
                    if not _rec(i + 1, current_args + [y]):
                        return False
                return True

        return _rec(0, [])

    def contract(self) -> 'ArithmeticalFormula':
        """Contract adjacent identical quantifiers using Cantor pairing.

        If prefix has adjacent like quantifiers (e.g. exists y1 exists y2),
        they are contracted into a single quantifier exists z where
        y1, y2 = cantor_unpair(z).
        """
        contracted_prefix = self.prefix.contract_adjacent()
        if len(contracted_prefix) == len(self.prefix):
            return self

        # Group indices of identical consecutive quantifiers
        groups: List[List[int]] = []
        for i, q in enumerate(self.prefix.quantifiers):
            if not groups or self.prefix.quantifiers[groups[-1][0]] != q:
                groups.append([i])
            else:
                groups[-1].append(i)

        original_matrix = self.matrix

        def contracted_matrix(x: int, *z_args: int) -> bool:
            # Decode z_args back into original variables
            full_args: List[int] = [0] * len(self.prefix)
            for z, group in zip(z_args, groups):
                if len(group) == 1:
                    full_args[group[0]] = z
                elif len(group) == 2:
                    y1, y2 = cantor_unpair(z)
                    full_args[group[0]] = y1
                    full_args[group[1]] = y2
                else:
                    curr = z
                    for idx in reversed(group[1:]):
                        curr, y = cantor_unpair(curr)
                        full_args[idx] = y
                    full_args[group[0]] = curr
            return original_matrix(x, *full_args)

        return ArithmeticalFormula(
            prefix=contracted_prefix,
            matrix=contracted_matrix,
            name=f"Contracted({self.name})",
        )

    def __repr__(self) -> str:
        cls, n = self.classify()
        return f"{self.name}({cls}_{n}^0)"


# -------------------------------------------------------------
# Shoenfield Limit Lemma
# -------------------------------------------------------------

class LimitApproximation:
    """A computable approximation function g(x, s) with finite mind changes.

    The Shoenfield Limit Lemma states that A is Delta_2^0 if and only if
    there exists a total computable g : N x N -> {0, 1} such that
        chi_A(x) = lim_{s -> infty} g(x, s).
    """

    def __init__(self, g: Callable[[int, int], int], name: str = "LimitApproximation"):
        self.g = g
        self.name = name

    def evaluate(self, x: int, s: int) -> int:
        """Compute approximation value g(x, s) in {0, 1}."""
        val = int(self.g(x, s))
        if val not in (0, 1):
            raise ValueError(f"Limit approximation must produce binary values, got {val}")
        return val

    def mind_changes(self, x: int, max_s: int = 100) -> int:
        """Count the number of changes of mind g(x, s) != g(x, s+1) for s < max_s."""
        changes = 0
        curr = self.evaluate(x, 0)
        for s in range(1, max_s + 1):
            nxt = self.evaluate(x, s)
            if nxt != curr:
                changes += 1
                curr = nxt
        return changes

    def stabilization_stage(self, x: int, max_s: int = 100) -> Optional[int]:
        """Find the earliest stage s_0 <= max_s where g(x, s) remains constant for all s in [s_0, max_s]."""
        vals = [self.evaluate(x, s) for s in range(max_s + 1)]
        final_val = vals[-1]
        s0 = max_s
        while s0 > 0 and vals[s0 - 1] == final_val:
            s0 -= 1
        return s0

    def limit(self, x: int, max_s: int = 100) -> int:
        """Compute the stabilized limit value at max_s."""
        return self.evaluate(x, max_s)


class LimitLemma:
    """Formalization of the Shoenfield Limit Lemma for Delta_2^0 relations.

    Theorem (Shoenfield, 1959):
    Let A subseteq N. The following are equivalent:
    1. A in Delta_2^0 (A is both Sigma_2^0 and Pi_2^0).
    2. A <=_T 0' (A is Turing reducible to the halting problem).
    3. The characteristic function chi_A is the pointwise limit of a computable
       sequence of total computable functions:
           chi_A(x) = lim_{s -> infty} g(x, s).
    """

    @staticmethod
    def verify_approximation(
        approx: LimitApproximation,
        target_set: Callable[[int], bool],
        domain: Iterable[int],
        max_s: int = 100,
    ) -> bool:
        """Verify that the approximation converges to target_set on domain."""
        for x in domain:
            expected = 1 if target_set(x) else 0
            computed = approx.limit(x, max_s=max_s)
            if computed != expected:
                return False
        return True

    @staticmethod
    def to_sigma2_formula(approx: LimitApproximation) -> ArithmeticalFormula:
        """Construct the canonical Sigma_2^0 formula for A:

        x in A <==> exists s_0 forall s (s >= s_0 ==> g(x, s) = 1).
        Matrix: (s < s_0) or (g(x, s) == 1).
        """
        prefix = QuantifierPrefix([Quantifier.EXISTS, Quantifier.FORALL])
        matrix = lambda x, s0, s: (s < s0) or (approx.evaluate(x, s) == 1)
        return ArithmeticalFormula(prefix, matrix, name=f"Sigma2({approx.name})")

    @staticmethod
    def to_pi2_formula(approx: LimitApproximation) -> ArithmeticalFormula:
        """Construct the canonical Pi_2^0 formula for A:

        x in A <==> forall s_0 exists s (s >= s_0 and g(x, s) = 1).
        Matrix: (s >= s_0) and (approx.evaluate(x, s) == 1).
        """
        prefix = QuantifierPrefix([Quantifier.FORALL, Quantifier.EXISTS])
        matrix = lambda x, s0, s: (s >= s0) and (approx.evaluate(x, s) == 1)
        return ArithmeticalFormula(prefix, matrix, name=f"Pi2({approx.name})")


# -------------------------------------------------------------
# Post's Theorem and the Turing Jump
# -------------------------------------------------------------

class TuringJump:
    """Representation of the Turing Jump Hierarchy 0^(n)."""

    def __init__(self, level: int):
        if level < 0:
            raise ValueError("Jump level must be non-negative")
        self.level = level

    def is_computable(self) -> bool:
        return self.level == 0

    def __repr__(self) -> str:
        return f"0^({self.level})"


class PostsTheorem:
    """Formalization of Post's Theorem (1948).

    Theorem:
    For all natural numbers n >= 0:
    1. A in Sigma_{n+1}^0 <==> A is computably enumerable relative to 0^(n).
    2. A in Delta_{n+1}^0 <==> A <=_T 0^(n) (computable with oracle 0^(n)).
    3. A in Pi_{n+1}^0    <==> complement(A) is c.e. relative to 0^(n).
    """

    @staticmethod
    def jump_level_for_sigma(n: int) -> TuringJump:
        """Return the oracle jump level corresponding to Sigma_n^0."""
        if n < 1:
            raise ValueError("Sigma_n requires n >= 1")
        return TuringJump(n - 1)

    @staticmethod
    def jump_level_for_delta(n: int) -> TuringJump:
        """Return the oracle jump level corresponding to Delta_n^0."""
        if n < 1:
            raise ValueError("Delta_n requires n >= 1")
        return TuringJump(n - 1)

    @staticmethod
    def verify_ce_as_sigma1(ce_predicate: Callable[[int, int], bool]) -> ArithmeticalFormula:
        """Convert a computably enumerable predicate x in W <==> exists s R(x, s) to Sigma_1^0."""
        prefix = QuantifierPrefix([Quantifier.EXISTS])
        return ArithmeticalFormula(prefix, ce_predicate, name="CE_Sigma1")

    @staticmethod
    def verify_decidable_as_delta1(
        decider: Callable[[int], bool],
    ) -> Tuple[ArithmeticalFormula, ArithmeticalFormula]:
        """Convert a decidable predicate to both Sigma_1^0 and Pi_1^0 formulas."""
        sigma1 = ArithmeticalFormula(
            QuantifierPrefix([Quantifier.EXISTS]),
            lambda x, s: decider(x),
            name="Decidable_Sigma1",
        )
        pi1 = ArithmeticalFormula(
            QuantifierPrefix([Quantifier.FORALL]),
            lambda x, s: decider(x),
            name="Decidable_Pi1",
        )
        return sigma1, pi1


# -------------------------------------------------------------
# Kleene T-Predicate & Computability Simulation Registry
# -------------------------------------------------------------

class KleeneTPredicate:
    """Simulation registry of Kleene's T-predicate: T(e, x, s).

    T(e, x, s) is true iff program e on input x halts in at most s steps.
    This predicate is primitive recursive (Delta_0^0 = Delta_1^0).
    """

    def __init__(self):
        # Maps program index e to a step-count function: step_fn(x) -> Optional[int]
        # None means the program diverges on input x.
        self._step_registry: Dict[int, Callable[[int], Optional[int]]] = {}

    def register(self, e: int, step_fn: Callable[[int], Optional[int]]) -> None:
        self._step_registry[e] = step_fn

    def T(self, e: int, x: int, s: int) -> bool:
        """Evaluate T(e, x, s): does program e on input x halt in <= s steps?"""
        if e not in self._step_registry:
            return False
        halt_time = self._step_registry[e](x)
        if halt_time is None:
            return False
        return halt_time <= s

    def U(self, e: int, x: int, s: int) -> Optional[int]:
        """Output extraction function U(e, x, s)."""
        if self.T(e, x, s):
            return x
        return None


# -------------------------------------------------------------
# Completeness and Undecidability Proofs
# -------------------------------------------------------------

class CompletenessProof:
    """Formal completeness proofs in the Arithmetical Hierarchy.

    Proves:
    1. Halting Problem K = 0' is Sigma_1^0-complete.
    2. Empty Problem Empty is Pi_1^0-complete.
    3. Finiteness Problem Fin is Sigma_2^0-complete.
    4. Totality Problem Tot is Pi_2^0-complete.
    """

    def __init__(self, kleene_t: Optional[KleeneTPredicate] = None):
        self.t_pred = kleene_t if kleene_t is not None else KleeneTPredicate()

    # 1. Halting Problem K = 0' is Sigma_1^0-complete
    def halting_formula(self) -> ArithmeticalFormula:
        """Formula for K: e in K <==> exists s T(e, e, s)."""
        prefix = QuantifierPrefix([Quantifier.EXISTS])
        matrix = lambda e, s: self.t_pred.T(e, e, s)
        return ArithmeticalFormula(prefix, matrix, name="HaltingProblem_K")

    def reduce_ce_to_halting(
        self,
        ce_matrix: Callable[[int, int], bool],
        smn_reduction: Callable[[int], int],
    ) -> ManyOneReduction:
        """Construct many-one reduction from arbitrary c.e. set W to K:

        x in W <==> exists s ce_matrix(x, s) <==> smn_reduction(x) in K.
        """
        source = lambda x: any(ce_matrix(x, s) for s in range(100))
        target = lambda e: any(self.t_pred.T(e, e, s) for s in range(100))
        return ManyOneReduction(source, target, smn_reduction, name="W_to_K")

    # 2. Empty Problem Empty is Pi_1^0-complete
    def empty_formula(self) -> ArithmeticalFormula:
        """Formula for Empty: e in Empty <==> forall x forall s not T(e, x, s)."""
        prefix = QuantifierPrefix([Quantifier.FORALL, Quantifier.FORALL])
        matrix = lambda e, x, s: not self.t_pred.T(e, x, s)
        return ArithmeticalFormula(prefix, matrix, name="EmptyProblem")

    # 3. Finiteness Problem Fin is Sigma_2^0-complete
    def finiteness_formula(self) -> ArithmeticalFormula:
        """Formula for Fin: e in Fin <==> exists n forall z (cantor_unpair(z) > n or not T(e, x, s))."""
        prefix = QuantifierPrefix([Quantifier.EXISTS, Quantifier.FORALL])

        def matrix(e: int, n: int, z: int) -> bool:
            x, s = cantor_unpair(z)
            if x <= n:
                return True
            return not self.t_pred.T(e, x, s)

        return ArithmeticalFormula(prefix, matrix, name="FinitenessProblem_Fin")

    # 4. Totality Problem Tot is Pi_2^0-complete
    def totality_formula(self) -> ArithmeticalFormula:
        """Formula for Tot: e in Tot <==> forall x exists s T(e, x, s)."""
        prefix = QuantifierPrefix([Quantifier.FORALL, Quantifier.EXISTS])
        matrix = lambda e, x, s: self.t_pred.T(e, x, s)
        return ArithmeticalFormula(prefix, matrix, name="TotalityProblem_Tot")

    def reduce_pi2_to_totality(
        self,
        pi2_matrix: Callable[[int, int, int], bool],
        reduction_fn: Callable[[int], int],
    ) -> ManyOneReduction:
        """Construct many-one reduction from arbitrary Pi_2^0 set P to Tot:

        x in P <==> forall u exists v pi2_matrix(x, u, v) <==> reduction_fn(x) in Tot.
        """
        source = lambda x: all(any(pi2_matrix(x, u, v) for v in range(50)) for u in range(10))
        target = lambda e: all(any(self.t_pred.T(e, x, s) for s in range(50)) for x in range(10))
        return ManyOneReduction(source, target, reduction_fn, name="Pi2_to_Tot")
