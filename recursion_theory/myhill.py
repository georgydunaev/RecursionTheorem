"""Myhill Isomorphism Theorem and Computable Reductions.

This module formalizes:
1. Computable Reductions:
   - Many-one reduction (A <=_m B): Total computable reduction function
     preserving set membership: x in A iff f(x) in B.
   - One-one reduction (A <=_1 B): Injective total computable reduction function.
   - Composition and algebraic preorder/equivalence properties of reductions.
2. Finite Bijection Patches:
   - FinitePatch data structure tracking domain, range, and bidirectional lookup.
3. Myhill Isomorphism Theorem (1955):
   - Constructive back-and-forth algorithm extending finite bijection patches.
   - If A <=_1 B via f and B <=_1 A via g, effectively constructs a computable
     permutation pi : N -> N such that x in A iff pi(x) in B.
   - Effective Cantor-Bernstein theorem with finite patch extension.
   - Formal proof certificate generation (MyhillCertificate).
"""

from typing import Callable, Dict, List, Optional, Set, Tuple, Union, Iterable, Any


# -------------------------------------------------------------
# Computable Set Predicate Helper
# -------------------------------------------------------------

SetPredicate = Union[Callable[[int], bool], Set[int], List[int]]


def _in_set(x: int, s: Optional[SetPredicate]) -> bool:
    """Check membership of x in a set predicate or container."""
    if s is None:
        raise ValueError("Set predicate is not provided")
    if callable(s):
        return bool(s(x))
    return x in s


# -------------------------------------------------------------
# Computable Reductions: Many-One (<=_m) and One-One (<=_1)
# -------------------------------------------------------------

class ManyOneReduction:
    """Formalization of Many-One Computable Reduction (A <=_m B).

    A set A is many-one reducible to B via computable function f if
    for all natural numbers x:
        x in A <==> f(x) in B.
    """

    def __init__(
        self,
        source: Optional[SetPredicate],
        target: Optional[SetPredicate],
        reduction_fn: Callable[[int], int],
        name: str = "ManyOneReduction",
    ):
        self.source = source
        self.target = target
        self.reduction_fn = reduction_fn
        self.name = name

    def reduce(self, x: int) -> int:
        """Apply the reduction function f(x)."""
        return self.reduction_fn(x)

    def __call__(self, x: int) -> int:
        return self.reduce(x)

    def verify(self, x: int) -> bool:
        """Verify that x in A <==> f(x) in B."""
        if self.source is None or self.target is None:
            raise ValueError("Source and target sets must be defined for verification")
        in_a = _in_set(x, self.source)
        fx = self.reduce(x)
        in_b = _in_set(fx, self.target)
        return in_a == in_b

    def verify_domain(self, domain: Iterable[int]) -> bool:
        """Verify membership preservation across a domain of test points."""
        return all(self.verify(x) for x in domain)

    def compose(self, subsequent: 'ManyOneReduction') -> 'ManyOneReduction':
        """Transitivity of many-one reductions:

        If self : A <=_m B and subsequent : B <=_m C,
        then subsequent o self : A <=_m C.
        """
        composed_fn = lambda x: subsequent.reduce(self.reduce(x))
        return ManyOneReduction(
            source=self.source,
            target=subsequent.target,
            reduction_fn=composed_fn,
            name=f"({subsequent.name} o {self.name})",
        )

    def __repr__(self) -> str:
        return f"{self.name}(A <=_m B)"


class OneOneReduction(ManyOneReduction):
    """Formalization of One-One Computable Reduction (A <=_1 B).

    A set A is one-one reducible to B via an INJECTIVE computable function f:
        1. f is injective: x != y ==> f(x) != f(y).
        2. x in A <==> f(x) in B.
    """

    def __init__(
        self,
        source: Optional[SetPredicate],
        target: Optional[SetPredicate],
        reduction_fn: Callable[[int], int],
        name: str = "OneOneReduction",
    ):
        super().__init__(source, target, reduction_fn, name=name)

    def verify_injectivity(self, domain: Iterable[int]) -> bool:
        """Verify that f is injective on the given finite domain."""
        seen: Dict[int, int] = {}
        for x in domain:
            fx = self.reduce(x)
            if fx in seen:
                return False
            seen[fx] = x
        return True

    def compose(self, subsequent: 'OneOneReduction') -> 'OneOneReduction':
        """Transitivity of one-one reductions preserves injectivity:

        If self : A <=_1 B (injective) and subsequent : B <=_1 C (injective),
        then subsequent o self : A <=_1 C is injective.
        """
        composed_fn = lambda x: subsequent.reduce(self.reduce(x))
        return OneOneReduction(
            source=self.source,
            target=subsequent.target,
            reduction_fn=composed_fn,
            name=f"({subsequent.name} o {self.name})",
        )

    def __repr__(self) -> str:
        return f"{self.name}(A <=_1 B)"


# -------------------------------------------------------------
# Finite Patch of a Bijection
# -------------------------------------------------------------

class FinitePatch:
    """A finite bidirectional map representing an approximation to a permutation."""

    def __init__(self):
        self._forward: Dict[int, int] = {}
        self._backward: Dict[int, int] = {}

    def add(self, x: int, y: int) -> None:
        """Add pair (x, y) to the patch."""
        if x in self._forward:
            if self._forward[x] == y:
                return
            raise ValueError(f"Domain conflict: {x} already mapped to {self._forward[x]}, cannot map to {y}")
        if y in self._backward:
            if self._backward[y] == x:
                return
            raise ValueError(f"Range conflict: {y} already mapped from {self._backward[y]}, cannot map from {x}")
        self._forward[x] = y
        self._backward[y] = x

    def contains_x(self, x: int) -> bool:
        return x in self._forward

    def contains_y(self, y: int) -> bool:
        return y in self._backward

    def get_y(self, x: int) -> int:
        return self._forward[x]

    def get_x(self, y: int) -> int:
        return self._backward[y]

    def domain(self) -> Set[int]:
        return set(self._forward.keys())

    def range(self) -> Set[int]:
        return set(self._backward.keys())

    def items(self) -> List[Tuple[int, int]]:
        return list(self._forward.items())

    def __len__(self) -> int:
        return len(self._forward)

    def __repr__(self) -> str:
        return f"FinitePatch(size={len(self)})"


# -------------------------------------------------------------
# Computable Permutation
# -------------------------------------------------------------

class ComputablePermutation:
    """A computable permutation of natural numbers pi : N -> N with computable inverse."""

    def __init__(self, forward: Callable[[int], int], backward: Callable[[int], int], name: str = "Permutation"):
        self.forward = forward
        self.backward = backward
        self.name = name

    def apply(self, x: int) -> int:
        """Compute pi(x)."""
        return self.forward(x)

    def invert(self, y: int) -> int:
        """Compute pi^{-1}(y)."""
        return self.backward(y)

    def __call__(self, x: int) -> int:
        return self.apply(x)

    def verify_involution(self, domain: Iterable[int]) -> bool:
        """Verify pi^{-1}(pi(x)) == x and pi(pi^{-1}(x)) == x on domain."""
        for x in domain:
            fx = self.apply(x)
            if self.invert(fx) != x:
                return False
            gx = self.invert(x)
            if self.apply(gx) != x:
                return False
        return True

    def verify_bijective(self, domain: Iterable[int]) -> bool:
        """Verify injectivity on domain."""
        seen: Set[int] = set()
        for x in domain:
            fx = self.apply(x)
            if fx in seen:
                return False
            seen.add(fx)
        return True


# -------------------------------------------------------------
# Myhill Isomorphism Theorem
# -------------------------------------------------------------

class MyhillCertificate:
    """Formal proof certificate for the Myhill Isomorphism construction."""

    def __init__(
        self,
        patch_size: int,
        stages_computed: int,
        verified_domain: List[int],
        is_bijective: bool,
        preserves_membership: bool,
        details: Dict[str, Any],
    ):
        self.patch_size = patch_size
        self.stages_computed = stages_computed
        self.verified_domain = verified_domain
        self.is_bijective = is_bijective
        self.preserves_membership = preserves_membership
        self.details = details

    def is_valid(self) -> bool:
        return self.is_bijective and self.preserves_membership

    def __repr__(self) -> str:
        return (
            f"MyhillCertificate(size={self.patch_size}, stages={self.stages_computed}, "
            f"valid={self.is_valid()})"
        )


class MyhillIsomorphism:
    """Constructive Back-and-Forth Algorithm for Myhill's Isomorphism Theorem.

    Theorem (Myhill, 1955):
    Two sets A, B subseteq N are recursively isomorphic (A equiv B)
    if and only if A <=_1 B and B <=_1 A.

    Given injective computable reductions:
        f : A <=_1 B
        g : B <=_1 A
    the algorithm constructs a computable permutation pi : N -> N such that:
        x in A <==> pi(x) in B  for all x in N.

    Construction Mechanism:
    At stage s = 2x (even, forward step):
        If x is not in dom(p_s), consider f(x). If f(x) in rng(p_s), follow
        the backward-forward chain until finding y* not in rng(p_s).
        Define p_{s+1}(x) = y*.
    At stage s = 2y + 1 (odd, backward step):
        If y is not in rng(p_s), consider g(y). If g(y) in dom(p_s), follow
        the forward-backward chain until finding x* not in dom(p_s).
        Define p_{s+1}(x*) = y.
    """

    def __init__(
        self,
        f: Union[OneOneReduction, Callable[[int], int]],
        g: Union[OneOneReduction, Callable[[int], int]],
        set_a: Optional[SetPredicate] = None,
        set_b: Optional[SetPredicate] = None,
    ):
        self.f_fn: Callable[[int], int] = f.reduce if isinstance(f, ManyOneReduction) else f
        self.g_fn: Callable[[int], int] = g.reduce if isinstance(g, ManyOneReduction) else g
        self.set_a = set_a if set_a is not None else (f.source if isinstance(f, ManyOneReduction) else None)
        self.set_b = set_b if set_b is not None else (f.target if isinstance(f, ManyOneReduction) else None)

        self.patch = FinitePatch()
        self.current_stage = 0

    def step(self) -> None:
        """Execute one stage of the back-and-forth algorithm."""
        s = self.current_stage
        k = s // 2

        if s % 2 == 0:
            # Even stage: ensure k is in domain
            if not self.patch.contains_x(k):
                curr = self.f_fn(k)
                while self.patch.contains_y(curr):
                    x_prev = self.patch.get_x(curr)
                    curr = self.f_fn(x_prev)
                self.patch.add(k, curr)
        else:
            # Odd stage: ensure k is in range
            if not self.patch.contains_y(k):
                curr = self.g_fn(k)
                while self.patch.contains_x(curr):
                    y_prev = self.patch.get_y(curr)
                    curr = self.g_fn(y_prev)
                self.patch.add(curr, k)

        self.current_stage += 1

    def run_stages(self, num_stages: int) -> None:
        """Run the construction for a fixed number of stages."""
        for _ in range(num_stages):
            self.step()

    def extend_until_x(self, x: int) -> None:
        """Run stages until x is in domain."""
        while not self.patch.contains_x(x):
            self.step()

    def extend_until_y(self, y: int) -> None:
        """Run stages until y is in range."""
        while not self.patch.contains_y(y):
            self.step()

    def pi(self, x: int) -> int:
        """Compute the permutation value pi(x)."""
        self.extend_until_x(x)
        return self.patch.get_y(x)

    def pi_inv(self, y: int) -> int:
        """Compute the inverse permutation value pi^{-1}(y)."""
        self.extend_until_y(y)
        return self.patch.get_x(y)

    def as_permutation(self) -> ComputablePermutation:
        """Return a ComputablePermutation wrapper around this isomorphism."""
        return ComputablePermutation(
            forward=self.pi,
            backward=self.pi_inv,
            name="MyhillPermutation",
        )

    def verify_isomorphism(self, domain: Iterable[int]) -> bool:
        """Verify that for all x in domain: x in A <==> pi(x) in B."""
        if self.set_a is None or self.set_b is None:
            raise ValueError("Sets A and B must be provided to verify isomorphism")
        for x in domain:
            y = self.pi(x)
            in_a = _in_set(x, self.set_a)
            in_b = _in_set(y, self.set_b)
            if in_a != in_b:
                return False
        return True

    def generate_certificate(self, max_element: int = 50) -> MyhillCertificate:
        """Generate a certified proof artifact of the Myhill construction."""
        domain = list(range(max_element + 1))
        # Ensure domain is computed
        for x in domain:
            self.extend_until_x(x)
            self.extend_until_y(x)

        perm = self.as_permutation()
        is_bij = perm.verify_involution(domain) and perm.verify_bijective(domain)
        preserves_mem = True
        if self.set_a is not None and self.set_b is not None:
            preserves_mem = self.verify_isomorphism(domain)

        sample_table = {x: self.pi(x) for x in domain[:10]}
        details = {
            "sample_mappings": sample_table,
            "domain_covered": domain,
            "patch_len": len(self.patch),
        }

        return MyhillCertificate(
            patch_size=len(self.patch),
            stages_computed=self.current_stage,
            verified_domain=domain,
            is_bijective=is_bij,
            preserves_membership=preserves_mem,
            details=details,
        )


# -------------------------------------------------------------
# Effective Cantor-Bernstein Theorem for Bijections
# -------------------------------------------------------------

def effective_cantor_bernstein(
    f: Callable[[int], int],
    g: Callable[[int], int],
) -> ComputablePermutation:
    """Constructive Cantor-Bernstein theorem for natural numbers.

    Given injective maps f : N -> N and g : N -> N, constructs a
    computable permutation pi : N -> N using the finite patch extension.
    """
    iso = MyhillIsomorphism(f=f, g=g)
    return iso.as_permutation()
