"""Comprehensive Unit Tests for Myhill Isomorphism Theorem and Arithmetical Hierarchy.

Covers:
1. Computable Reductions (ManyOneReduction, OneOneReduction):
   - Definition, evaluation, membership preservation, composition, and injectivity.
2. FiniteBijectionPatches:
   - Bidirectional mapping, consistency checks, conflict handling.
3. Myhill Isomorphism Theorem (MyhillIsomorphism):
   - Back-and-forth algorithm, permutation generation, bijectivity, involution.
   - Membership preservation: x in A <==> pi(x) in B.
   - Effective Cantor-Bernstein theorem for bijections.
   - MyhillCertificate validity.
4. Arithmetical Hierarchy (QuantifierPrefix, ArithmeticalFormula):
   - Quantifier alternations and classification into Sigma_n^0, Pi_n^0, Delta_0^0.
   - Duality and negation.
   - Contraction of adjacent like quantifiers using Cantor pairing.
   - Bounded evaluation of arithmetical formulas.
5. Shoenfield Limit Lemma (LimitApproximation, LimitLemma):
   - Pointwise limit of computable approximations, stabilization stages, mind changes.
   - Translation from approximations to canonical Sigma_2^0 and Pi_2^0 formulas.
6. Post's Theorem (PostsTheorem, TuringJump):
   - Correspondence with Turing jumps: Sigma_{n+1}^0 <==> c.e. in 0^(n).
   - Conversions of c.e. to Sigma_1^0 and decidable to Delta_1^0.
7. Completeness and Undecidability (CompletenessProof, KleeneTPredicate):
   - Sigma_1^0-completeness of Halting Problem K = 0'.
   - Pi_1^0-completeness of Empty Problem Empty.
   - Sigma_2^0-completeness of Finiteness Problem Fin.
   - Pi_2^0-completeness of Totality Problem Tot.
"""

import unittest
from typing import Optional
from recursion_theory.myhill import (
    ManyOneReduction,
    OneOneReduction,
    FinitePatch,
    ComputablePermutation,
    MyhillIsomorphism,
    effective_cantor_bernstein,
)
from recursion_theory.hierarchy import (
    Quantifier,
    QuantifierPrefix,
    ArithmeticalFormula,
    LimitApproximation,
    LimitLemma,
    TuringJump,
    PostsTheorem,
    KleeneTPredicate,
    CompletenessProof,
)


class TestComputableReductions(unittest.TestCase):
    """Unit tests for Many-One and One-One computable reductions."""

    def test_many_one_reduction_basic(self):
        # A = even numbers, B = multiples of 4
        # f(x) = 2x maps evens to multiples of 4, and odds to non-multiples of 4
        set_a = lambda x: x % 2 == 0
        set_b = lambda x: x % 4 == 0
        f = lambda x: 2 * x

        red = ManyOneReduction(set_a, set_b, f, name="Evens_to_Mult4")
        self.assertTrue(red.verify_domain(range(50)))
        self.assertEqual(red.reduce(3), 6)
        self.assertEqual(red.reduce(4), 8)

    def test_many_one_reduction_composition(self):
        # A = evens, B = multiples of 4, C = multiples of 12
        set_a = lambda x: x % 2 == 0
        set_b = lambda x: x % 4 == 0
        set_c = lambda x: x % 12 == 0

        red1 = ManyOneReduction(set_a, set_b, lambda x: 2 * x, name="A_to_B")
        red2 = ManyOneReduction(set_b, set_c, lambda y: 3 * y, name="B_to_C")

        composed = red1.compose(red2)
        self.assertEqual(composed.reduce(2), 12)
        self.assertEqual(composed.reduce(3), 18)
        self.assertTrue(composed.verify_domain(range(30)))

    def test_one_one_reduction_injectivity(self):
        set_a = lambda x: x % 2 == 0
        set_b = lambda x: x % 4 == 0
        injective_f = lambda x: 2 * x
        non_injective_f = lambda x: (x // 2) * 4

        red_inj = OneOneReduction(set_a, set_b, injective_f)
        self.assertTrue(red_inj.verify_injectivity(range(50)))
        self.assertTrue(red_inj.verify_domain(range(50)))

        red_non_inj = OneOneReduction(set_a, set_b, non_injective_f)
        self.assertFalse(red_non_inj.verify_injectivity(range(10)))

    def test_one_one_reduction_composition_preserves_injectivity(self):
        set_a = lambda x: x % 2 == 0
        set_b = lambda x: x % 4 == 0
        set_c = lambda x: x % 8 == 0

        red1 = OneOneReduction(set_a, set_b, lambda x: 2 * x)
        red2 = OneOneReduction(set_b, set_c, lambda y: 2 * y)
        comp = red1.compose(red2)

        self.assertTrue(comp.verify_injectivity(range(30)))
        self.assertTrue(comp.verify_domain(range(30)))


class TestFinitePatch(unittest.TestCase):
    """Unit tests for finite bijection patches."""

    def test_patch_operations(self):
        patch = FinitePatch()
        self.assertEqual(len(patch), 0)

        patch.add(0, 10)
        patch.add(1, 11)
        self.assertEqual(len(patch), 2)
        self.assertTrue(patch.contains_x(0))
        self.assertTrue(patch.contains_y(10))
        self.assertEqual(patch.get_y(0), 10)
        self.assertEqual(patch.get_x(10), 0)

        # Idempotent re-add
        patch.add(0, 10)
        self.assertEqual(len(patch), 2)

    def test_patch_conflicts(self):
        patch = FinitePatch()
        patch.add(0, 10)
        # Domain conflict: 0 -> 11
        with self.assertRaises(ValueError):
            patch.add(0, 11)
        # Range conflict: 1 -> 10
        with self.assertRaises(ValueError):
            patch.add(1, 10)


class TestMyhillIsomorphismTheorem(unittest.TestCase):
    """Unit tests for constructive Myhill Isomorphism Theorem."""

    def setUp(self):
        # A = evens: {2k}
        # B = multiples of 3: {3k}
        self.set_a = lambda x: x % 2 == 0
        self.set_b = lambda y: y % 3 == 0

        # Injective reduction f : A <=_1 B
        def f(x: int) -> int:
            if x % 2 == 0:
                return 3 * (x // 2)
            else:
                return 3 * (x // 2) + 1

        # Injective reduction g : B <=_1 A
        def g(y: int) -> int:
            k = y // 3
            r = y % 3
            if r == 0:
                return 2 * k
            elif r == 1:
                return 4 * k + 1
            else:
                return 4 * k + 3

        self.f = f
        self.g = g
        self.red_f = OneOneReduction(self.set_a, self.set_b, f)
        self.red_g = OneOneReduction(self.set_b, self.set_a, g)

    def test_myhill_permutation_bijectivity_and_involution(self):
        iso = MyhillIsomorphism(self.red_f, self.red_g)
        perm = iso.as_permutation()

        test_domain = list(range(35))
        self.assertTrue(perm.verify_involution(test_domain))
        self.assertTrue(perm.verify_bijective(test_domain))

        for x in test_domain:
            y = perm.apply(x)
            self.assertEqual(perm.invert(y), x)

        for y in test_domain:
            x = perm.invert(y)
            self.assertEqual(perm.apply(x), y)

    def test_myhill_membership_preservation(self):
        iso = MyhillIsomorphism(self.red_f, self.red_g)
        test_domain = list(range(40))
        self.assertTrue(iso.verify_isomorphism(test_domain))

        for x in test_domain:
            y = iso.pi(x)
            in_a = self.set_a(x)
            in_b = self.set_b(y)
            self.assertEqual(in_a, in_b, f"Failed at x={x} (in_A={in_a}), pi(x)={y} (in_B={in_b})")

    def test_myhill_proof_certificate(self):
        iso = MyhillIsomorphism(self.red_f, self.red_g)
        cert = iso.generate_certificate(max_element=30)
        self.assertTrue(cert.is_valid())
        self.assertTrue(cert.is_bijective)
        self.assertTrue(cert.preserves_membership)
        self.assertGreaterEqual(cert.patch_size, 31)

    def test_effective_cantor_bernstein(self):
        # Two injective maps: f(x) = 2x + 1, g(y) = 2y + 1
        perm = effective_cantor_bernstein(lambda x: 2 * x + 1, lambda y: 2 * y + 1)
        test_domain = list(range(25))
        self.assertTrue(perm.verify_involution(test_domain))
        self.assertTrue(perm.verify_bijective(test_domain))


class TestArithmeticalHierarchy(unittest.TestCase):
    """Unit tests for arithmetical hierarchy formulas and classifications."""

    def test_quantifier_prefix_classification(self):
        # Delta_0^0 (empty prefix)
        p0 = QuantifierPrefix([])
        self.assertEqual(p0.classification(), ("Delta", 0))

        # Sigma_1^0
        p_sig1 = QuantifierPrefix([Quantifier.EXISTS])
        self.assertEqual(p_sig1.classification(), ("Sigma", 1))

        # Pi_1^0
        p_pi1 = QuantifierPrefix([Quantifier.FORALL])
        self.assertEqual(p_pi1.classification(), ("Pi", 1))

        # Sigma_2^0
        p_sig2 = QuantifierPrefix([Quantifier.EXISTS, Quantifier.FORALL])
        self.assertEqual(p_sig2.classification(), ("Sigma", 2))

        # Pi_2^0
        p_pi2 = QuantifierPrefix([Quantifier.FORALL, Quantifier.EXISTS])
        self.assertEqual(p_pi2.classification(), ("Pi", 2))

        # Sigma_3^0
        p_sig3 = QuantifierPrefix([Quantifier.EXISTS, Quantifier.FORALL, Quantifier.EXISTS])
        self.assertEqual(p_sig3.classification(), ("Sigma", 3))

    def test_quantifier_prefix_contraction(self):
        # [exists, exists, exists] contracts to [exists] (Sigma_1^0)
        p = QuantifierPrefix([Quantifier.EXISTS, Quantifier.EXISTS, Quantifier.EXISTS])
        c = p.contract_adjacent()
        self.assertEqual(len(c), 1)
        self.assertEqual(c.classification(), ("Sigma", 1))

        # [forall, forall, exists, exists] contracts to [forall, exists] (Pi_2^0)
        p2 = QuantifierPrefix([Quantifier.FORALL, Quantifier.FORALL, Quantifier.EXISTS, Quantifier.EXISTS])
        c2 = p2.contract_adjacent()
        self.assertEqual(len(c2), 2)
        self.assertEqual(c2.classification(), ("Pi", 2))

    def test_quantifier_prefix_duality(self):
        p = QuantifierPrefix([Quantifier.EXISTS, Quantifier.FORALL])
        d = p.dual()
        self.assertEqual(d.classification(), ("Pi", 2))
        self.assertEqual(d.dual().classification(), ("Sigma", 2))

    def test_arithmetical_formula_bounded_evaluation(self):
        # Even numbers: exists y (2 * y == x)
        even_form = ArithmeticalFormula(
            QuantifierPrefix([Quantifier.EXISTS]),
            lambda x, y: 2 * y == x,
            name="IsEven",
        )
        self.assertEqual(even_form.classify(), ("Sigma", 1))
        self.assertTrue(even_form.evaluate_bounded(6, 10))
        self.assertFalse(even_form.evaluate_bounded(7, 10))

        # Dual formula: forall y (2 * y != x) (Odd numbers)
        odd_form = even_form.dual()
        self.assertEqual(odd_form.classify(), ("Pi", 1))
        self.assertFalse(odd_form.evaluate_bounded(6, 10))
        self.assertTrue(odd_form.evaluate_bounded(7, 10))

    def test_arithmetical_formula_contraction_via_pairing(self):
        # Formula: exists y1 exists y2 (y1 * y2 == x and y1 > 1 and y2 > 1) (Composite numbers)
        def is_composite_matrix(x: int, y1: int, y2: int) -> bool:
            return (y1 * y2 == x) and (y1 > 1) and (y2 > 1)

        comp_form = ArithmeticalFormula(
            QuantifierPrefix([Quantifier.EXISTS, Quantifier.EXISTS]),
            is_composite_matrix,
            name="IsComposite",
        )
        self.assertEqual(comp_form.classify(), ("Sigma", 1))

        contracted = comp_form.contract()
        self.assertEqual(contracted.classify(), ("Sigma", 1))
        self.assertEqual(len(contracted.prefix), 1)

        # 4 is composite (2 * 2), 6 is composite (2 * 3), 5 is prime (not composite)
        self.assertTrue(contracted.evaluate_bounded(4, 50))
        self.assertTrue(contracted.evaluate_bounded(6, 50))
        self.assertFalse(contracted.evaluate_bounded(5, 50))


class TestShoenfieldLimitLemma(unittest.TestCase):
    """Unit tests for the Shoenfield Limit Lemma (Delta_2^0 limits)."""

    def test_limit_approximation_convergence(self):
        # Target set A = {x : x is a square} = {0, 1, 4, 9, 16, ...}
        # Approximator g(x, s): at stage s, checks if there is k <= s such that k^2 == x
        def g_square(x: int, s: int) -> int:
            return 1 if any(k * k == x for k in range(s + 1)) else 0

        approx = LimitApproximation(g_square, name="SquareApprox")

        # 4 is a square: stabilized at s=2
        self.assertEqual(approx.limit(4, max_s=10), 1)
        self.assertEqual(approx.stabilization_stage(4, max_s=10), 2)
        self.assertEqual(approx.mind_changes(4, max_s=10), 1)

        # 3 is not a square: never changes mind, stays 0
        self.assertEqual(approx.limit(3, max_s=10), 0)
        self.assertEqual(approx.stabilization_stage(3, max_s=10), 0)
        self.assertEqual(approx.mind_changes(3, max_s=10), 0)

        # Verify on domain 0..15
        is_sq = lambda x: any(k * k == x for k in range(x + 1))
        self.assertTrue(LimitLemma.verify_approximation(approx, is_sq, range(16), max_s=16))

    def test_translation_to_sigma2_and_pi2(self):
        # A finite set A = {1, 3}
        # Approximation g(x, s) = 1 if x in {1, 3} and s >= 2 else 0
        def g_finite(x: int, s: int) -> int:
            return 1 if x in (1, 3) and s >= 2 else 0

        approx = LimitApproximation(g_finite, name="FiniteSetApprox")

        sigma2 = LimitLemma.to_sigma2_formula(approx)
        self.assertEqual(sigma2.classify(), ("Sigma", 2))

        pi2 = LimitLemma.to_pi2_formula(approx)
        self.assertEqual(pi2.classify(), ("Pi", 2))

        # Evaluate on test points with bound
        self.assertTrue(sigma2.evaluate_bounded(1, search_bounds=[5, 5]))
        self.assertTrue(pi2.evaluate_bounded(1, search_bounds=[5, 5]))
        self.assertFalse(sigma2.evaluate_bounded(2, search_bounds=[5, 5]))


class TestPostsTheorem(unittest.TestCase):
    """Unit tests for Post's Theorem and the Turing Jump Hierarchy."""

    def test_jump_hierarchy_levels(self):
        jump0 = TuringJump(0)
        self.assertTrue(jump0.is_computable())

        jump1 = TuringJump(1)
        self.assertFalse(jump1.is_computable())

        self.assertEqual(PostsTheorem.jump_level_for_sigma(1).level, 0)
        self.assertEqual(PostsTheorem.jump_level_for_sigma(2).level, 1)
        self.assertEqual(PostsTheorem.jump_level_for_sigma(3).level, 2)

        self.assertEqual(PostsTheorem.jump_level_for_delta(1).level, 0)
        self.assertEqual(PostsTheorem.jump_level_for_delta(2).level, 1)

    def test_ce_as_sigma1(self):
        # CE predicate: x is even iff exists s (2 * s == x)
        ce_pred = lambda x, s: 2 * s == x
        formula = PostsTheorem.verify_ce_as_sigma1(ce_pred)
        self.assertEqual(formula.classify(), ("Sigma", 1))
        self.assertTrue(formula.evaluate_bounded(8, 10))
        self.assertFalse(formula.evaluate_bounded(9, 10))

    def test_decidable_as_delta1(self):
        decider = lambda x: x % 3 == 0
        sig1, pi1 = PostsTheorem.verify_decidable_as_delta1(decider)
        self.assertEqual(sig1.classify(), ("Sigma", 1))
        self.assertEqual(pi1.classify(), ("Pi", 1))
        self.assertTrue(sig1.evaluate_bounded(9, 2))
        self.assertTrue(pi1.evaluate_bounded(9, 2))
        self.assertFalse(sig1.evaluate_bounded(10, 2))
        self.assertFalse(pi1.evaluate_bounded(10, 2))


class TestCompletenessAndUndecidability(unittest.TestCase):
    """Unit tests for undecidability and completeness proofs in the hierarchy."""

    def setUp(self):
        self.t_pred = KleeneTPredicate()
        # Program 10: Total program, halts in 2 steps for any input
        self.t_pred.register(10, lambda x: 2)
        # Program 20: Finite domain program, halts only on inputs x in {0, 1} in 3 steps
        self.t_pred.register(20, lambda x: 3 if x in (0, 1) else None)
        # Program 30: Empty domain program, diverges for all inputs
        self.t_pred.register(30, lambda x: None)

        self.comp = CompletenessProof(self.t_pred)

    def test_halting_problem_sigma1_completeness(self):
        k_form = self.comp.halting_formula()
        self.assertEqual(k_form.classify(), ("Sigma", 1))

        # Program 10 halts on self input 10
        self.assertTrue(k_form.evaluate_bounded(10, 5))
        # Program 20 halts on 0, 1 but not on 20
        self.assertFalse(k_form.evaluate_bounded(20, 5))
        # Program 30 diverges everywhere
        self.assertFalse(k_form.evaluate_bounded(30, 5))

    def test_empty_problem_pi1_completeness(self):
        empty_form = self.comp.empty_formula()
        self.assertEqual(empty_form.classify(), ("Pi", 1))

        # Program 30 has empty domain
        self.assertTrue(empty_form.evaluate_bounded(30, search_bounds=[5, 5]))
        # Program 10 is not empty
        self.assertFalse(empty_form.evaluate_bounded(10, search_bounds=[5, 5]))

    def test_finiteness_problem_sigma2_completeness(self):
        fin_form = self.comp.finiteness_formula()
        self.assertEqual(fin_form.classify(), ("Sigma", 2))

        # Program 20 has finite domain {0, 1}
        self.assertTrue(fin_form.evaluate_bounded(20, search_bounds=[3, 30]))
        # Program 30 has empty domain (finite)
        self.assertTrue(fin_form.evaluate_bounded(30, search_bounds=[3, 30]))

    def test_totality_problem_pi2_completeness(self):
        tot_form = self.comp.totality_formula()
        self.assertEqual(tot_form.classify(), ("Pi", 2))

        # Program 10 is total
        self.assertTrue(tot_form.evaluate_bounded(10, search_bounds=[5, 5]))
        # Program 20 is not total
        self.assertFalse(tot_form.evaluate_bounded(20, search_bounds=[5, 5]))
        # Program 30 is not total
        self.assertFalse(tot_form.evaluate_bounded(30, search_bounds=[5, 5]))


if __name__ == "__main__":
    unittest.main()
