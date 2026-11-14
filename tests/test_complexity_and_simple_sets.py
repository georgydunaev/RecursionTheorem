"""Unit tests for Blum Complexity Axioms, Speedup Theorem, and Post's Simple Sets.

Covers:
1. Blum Complexity Measures:
   - Axiom 1 (Domain Convergence): Phi_i(x) converges iff phi_i(x) converges.
   - Axiom 2 (Step Decidability): Step decider halts and decides Phi_i(x) <= m.
   - Complexity classes and bound verification.
2. Blum Compression Theorem:
   - Diagonalization against candidate programs within bound t(x).
   - Cancellation mechanics and witness generation.
   - Compression certificates and strict class separation.
3. Blum Speedup Theorem:
   - Hierarchy of algorithms computing identical total functions.
   - Arbitrary speedup verification: Phi_u(x) > r(x, Phi_{u+1}(x)).
   - Exponential and polynomial speedup operators.
   - Speedup certificate generation and validation.
4. Post's Simple Sets:
   - Post's restraint construction: x > 2e.
   - Coinfinity lower bound: at most n elements from {0, ..., 2n} in S.
   - Intersection with infinite c.e. sets.
   - Post's problem resolution for many-one reduction: empty <_m S <_m K.
5. Finite-Injury Priority Engine (PriorityWorker):
   - Priority resolution and restraint enforcement.
   - Movable markers and injury tracking.
   - Finite injury lemma and stabilization verification.
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from recursion_theory.complexity import (
    BlumComplexityMeasure,
    BlumCompressionTheorem,
    BlumSpeedupTheorem,
    CompressionCertificate,
    SpeedupCertificate,
)
from recursion_theory.simple_sets import (
    PriorityRequirement,
    PriorityWorker,
    SimpleSet,
)
from recursion_theory.kleene import ProgramSystem


class TestBlumComplexityAxioms(unittest.TestCase):
    """Test suite for Blum's Abstract Complexity Axioms."""

    def setUp(self):
        self.system = ProgramSystem()
        self.measure = BlumComplexityMeasure(self.system)

        # Program 0: Identity f(x) = x, steps = x + 1
        self.measure.register_measure(
            index=0,
            program_fn=lambda x: x,
            step_fn=lambda x: x + 1,
        )

        # Program 1: Square f(x) = x^2, steps = 2 * x + 3
        self.measure.register_measure(
            index=1,
            program_fn=lambda x: x * x,
            step_fn=lambda x: 2 * x + 3,
        )

        # Program 2: Partial function, defined only on even numbers
        # Diverges (None) on odd numbers
        def partial_even(x: int):
            return (x // 2) if x % 2 == 0 else None

        def partial_even_steps(x: int):
            return (x + 2) if x % 2 == 0 else None

        def partial_even_sim(x: int, max_steps: int):
            if x % 2 == 0:
                cost = x + 2
                if cost <= max_steps:
                    return (True, x // 2, cost)
                return (False, None, max_steps)
            else:
                # Diverges indefinitely; never halts within max_steps
                return (False, None, max_steps)

        self.measure.register_measure(
            index=2,
            program_fn=partial_even,
            step_fn=partial_even_steps,
            step_sim=partial_even_sim,
        )

    def test_axiom_1_domain_convergence(self):
        """Verify Axiom 1: Phi_i(x) is defined iff phi_i(x) is defined."""
        # Total programs: both converge everywhere
        for prog in (0, 1):
            for x in range(10):
                res = self.measure.verify_axiom_1(prog, x)
                self.assertTrue(res["holds"])
                self.assertTrue(res["phi_converges"])
                self.assertTrue(res["Phi_converges"])

        # Partial program 2: converges on evens, diverges on odds
        for x in range(10):
            res = self.measure.verify_axiom_1(2, x)
            self.assertTrue(res["holds"])
            if x % 2 == 0:
                self.assertTrue(res["phi_converges"])
                self.assertTrue(res["Phi_converges"])
            else:
                self.assertFalse(res["phi_converges"])
                self.assertFalse(res["Phi_converges"])

    def test_axiom_2_step_decidability(self):
        """Verify Axiom 2: step_decider(i, x, m) halts and correctly decides Phi_i(x) <= m."""
        # Check program 0: Phi_0(x) = x + 1
        for x in (0, 1, 2, 5):
            true_cost = x + 1
            # Below true cost: must return False
            self.assertFalse(self.measure.step_decider(0, x, true_cost - 1))
            # At or above true cost: must return True
            self.assertTrue(self.measure.step_decider(0, x, true_cost))
            self.assertTrue(self.measure.step_decider(0, x, true_cost + 5))

        # Check partial program 2 on odd inputs (divergent computation):
        # Step decider must terminate in finite time and return False!
        for x in (1, 3, 5, 7):
            for m in (0, 10, 100, 1000):
                self.assertFalse(self.measure.step_decider(2, x, m))

    def test_verify_axioms_comprehensive(self):
        """Verify both Blum axioms over systematic parameter combinations."""
        report = self.measure.verify_axioms(
            indices=[0, 1, 2],
            inputs=[0, 1, 2, 3, 4],
            bounds=[0, 2, 5, 10, 20],
        )
        self.assertTrue(report["verified"])
        self.assertGreater(report["total_checks"], 0)

    def test_complexity_classes(self):
        """Verify classification of programs into complexity-bounded classes C_t."""
        # Linear bound: t(x) = 2 * x + 1
        # Program 0 has cost x + 1 <= 2x + 1 for all x >= 0, so 0 in C_t
        # Program 1 has cost 2x + 3 > 2x + 1, so 1 not in C_t
        linear_bound = lambda x: 2 * x + 1
        test_domain = [0, 1, 2, 3, 4, 5]
        bounded = self.measure.complexity_class(linear_bound, [0, 1], test_domain)
        self.assertIn(0, bounded)
        self.assertNotIn(1, bounded)

        # Quadratic bound: t(x) = 3 * x + 10
        # Both programs 0 and 1 are bounded on test_domain
        quad_bound = lambda x: 3 * x + 10
        bounded_both = self.measure.complexity_class(quad_bound, [0, 1], test_domain)
        self.assertIn(0, bounded_both)
        self.assertIn(1, bounded_both)


class TestBlumCompressionTheorem(unittest.TestCase):
    """Test suite for Blum's Compression Theorem."""

    def setUp(self):
        self.measure = BlumComplexityMeasure()

        # Register a pool of candidate programs with known behaviors
        # Program 0: always outputs 0, cost 1
        self.measure.register_measure(0, lambda x: 0, lambda x: 1)
        # Program 1: always outputs 1, cost 2
        self.measure.register_measure(1, lambda x: 1, lambda x: 2)
        # Program 2: parity f(x) = x mod 2, cost 3
        self.measure.register_measure(2, lambda x: x % 2, lambda x: 3)
        # Program 3: constant 0 with cost 10
        self.measure.register_measure(3, lambda x: 0, lambda x: 10)

        self.compression = BlumCompressionTheorem(self.measure)

    def test_compression_diagonalization_cancellation(self):
        """Verify that diagonalization cancels bounded candidate programs."""
        # Bound t(x) = 5
        # Programs 0, 1, 2 have costs 1, 2, 3 <= 5, so they can be cancelled
        # Program 3 has cost 10 > 5, so it will not be cancelled within bound 5
        t_bound = lambda x: 5
        f_table, log, cancelled = self.compression.compute_separating_function(
            max_x=5,
            t_bound=t_bound,
            candidate_indices=[0, 1, 2, 3],
        )

        # Programs 0, 1, 2 should be cancelled at successive inputs
        self.assertIn(0, cancelled)
        self.assertIn(1, cancelled)
        self.assertIn(2, cancelled)
        self.assertNotIn(3, cancelled)

        # Verify that at each cancellation input x, f_t(x) != phi_target(x)
        for record in log:
            x = record["input"]
            target = record["cancelled_program"]
            phi_val = self.measure.phi(target, x)
            f_val = f_table[x]
            self.assertNotEqual(phi_val, f_val)

    def test_separation_verification_and_certificate(self):
        """Verify strict separation certificate generation."""
        t_bound = lambda x: 4
        candidates = [0, 1, 2]
        verification = self.compression.verify_separation(t_bound, candidates, max_x=6)
        self.assertTrue(verification["all_eliminated"])

        cert = self.compression.generate_certificate(
            t_bound=t_bound,
            bound_description="t(x) = 4",
            candidate_indices=candidates,
            max_x=6,
        )
        self.assertTrue(cert.is_valid())
        summary = cert.summary()
        self.assertEqual(summary["bound"], "t(x) = 4")
        self.assertEqual(len(summary["cancelled_programs"]), 3)


class TestBlumSpeedupTheorem(unittest.TestCase):
    """Test suite for Blum's Speedup Theorem."""

    def test_exponential_speedup(self):
        """Verify constructive speedup with exponential speedup operator r(x, y) = 2^y."""
        speedup_op = lambda x, y: (1 << min(y, 20))  # 2^y
        speedup = BlumSpeedupTheorem(
            speedup_fn=speedup_op,
            speedup_description="r(x, y) = 2^y",
        )

        test_domain = [0, 1, 2, 3, 4, 5]
        num_levels = 4
        result = speedup.verify_speedup(num_levels=num_levels, test_domain=test_domain)

        self.assertTrue(result["equivalence_verified"])
        self.assertTrue(result["speedup_verified"])

        cert = result["certificate"]
        self.assertTrue(cert.is_valid())
        self.assertEqual(len(cert.level_pairs), num_levels - 1)

    def test_polynomial_speedup(self):
        """Verify constructive speedup with cubic speedup operator r(x, y) = y^3 + x."""
        speedup_op = lambda x, y: (y ** 3) + x + 2
        speedup = BlumSpeedupTheorem(
            speedup_fn=speedup_op,
            speedup_description="r(x, y) = y^3 + x + 2",
        )

        test_domain = list(range(6))
        result = speedup.verify_speedup(num_levels=3, test_domain=test_domain)

        self.assertTrue(result["equivalence_verified"])
        self.assertTrue(result["speedup_verified"])
        self.assertTrue(result["certificate"].is_valid())


class TestPostSimpleSetConstruction(unittest.TestCase):
    """Test suite for Simple Sets and Post's Problem."""

    def setUp(self):
        # Effective stage enumerators for c.e. sets:
        # W_0: Even numbers {0, 2, 4, 6, ...}
        def enum_w0(s: int):
            return [2 * k for k in range(s + 2)]

        # W_1: Odd numbers {1, 3, 5, 7, ...}
        def enum_w1(s: int):
            return [2 * k + 1 for k in range(s + 2)]

        # W_2: Multiples of 3 {0, 3, 6, 9, ...}
        def enum_w2(s: int):
            return [3 * k for k in range(s + 2)]

        # W_3: Multiples of 5 {0, 5, 10, 15, ...}
        def enum_w3(s: int):
            return [5 * k for k in range(s + 2)]

        self.simple_set = SimpleSet({
            0: enum_w0,
            1: enum_w1,
            2: enum_w2,
            3: enum_w3,
        })

    def test_post_restraint_and_enumeration(self):
        """Verify Post's restraint condition x > 2e is strictly obeyed."""
        self.simple_set.run(stages=15)

        for event in self.simple_set.history:
            e = event["requirement"]
            x = event["element"]
            self.assertGreater(x, 2 * e)
            self.assertIn(x, self.simple_set.S)

    def test_coinfinity_lower_bound_and_verification(self):
        """Verify Post's coinfinity bound: |(N \\ S) cap {0, ..., 2n}| >= n + 1."""
        self.simple_set.run(stages=20)

        # Test specific n values
        for n in range(10):
            bound_res = self.simple_set.coinfinity_lower_bound(n)
            self.assertTrue(bound_res["holds"])
            self.assertGreaterEqual(
                bound_res["elements_in_complement"],
                bound_res["guaranteed_minimum"],
            )

        # Batch verification
        verif = self.simple_set.verify_coinfinity(max_n=12)
        self.assertTrue(verif["coinfinite_verified"])

    def test_infinite_ce_intersection(self):
        """Verify that simple set S intersects every infinite c.e. set W_e."""
        self.simple_set.run(stages=20)
        report = self.simple_set.verify_infinite_ce_intersection([0, 1, 2, 3])
        self.assertTrue(report["all_intersect"])
        for e in [0, 1, 2, 3]:
            witness = report["intersections"][e]["witness"]
            self.assertIsNotNone(witness)
            self.assertIn(witness, self.simple_set.S)

    def test_post_problem_many_one_barrier(self):
        """Verify formal deduction that S solves Post's Problem for many-one reductions."""
        barrier = self.simple_set.post_problem_many_one_barrier()
        self.assertTrue(barrier["S_is_ce"])
        self.assertTrue(barrier["S_is_coinfinite"])
        self.assertTrue(barrier["S_is_undecidable"])
        self.assertFalse(barrier["K_many_one_reduces_to_S"])
        self.assertEqual(barrier["status"], "strictly_intermediate_degree")
        self.assertEqual(barrier["reduction_chain"], "empty <_m S <_m K")


class TestFiniteInjuryPriorityWorker(unittest.TestCase):
    """Test suite for the PriorityWorker engine."""

    def test_priority_argument_execution_and_injury(self):
        """Verify that higher priority requirements act and can injure lower priority ones."""
        worker = PriorityWorker()

        # Add 3 requirements with priorities 0, 1, 2
        worker.add_requirement(index=0, priority=0, name="R_0", restraint=5)
        worker.add_requirement(index=1, priority=1, name="R_1", restraint=10)
        worker.add_requirement(index=2, priority=2, name="R_2", restraint=15)

        # Stage 0: R_1 acts with element 12 (respects R_0 restraint of 0 since R_0 unsatisfied)
        action0 = worker.step([
            (1, 12, {"new_restraint": 12}),
        ])
        self.assertIsNotNone(action0)
        self.assertEqual(action0["requirement_index"], 1)
        self.assertEqual(worker.get_requirement(1).state, "satisfied")

        # Stage 1: R_0 acts with element 8 (has higher priority 0 < 1).
        # Since element 8 <= R_1's restraint 12, this must injure R_1!
        action1 = worker.step([
            (0, 8, {"new_restraint": 8}),
        ])
        self.assertIsNotNone(action1)
        self.assertEqual(action1["requirement_index"], 0)
        self.assertEqual(worker.get_requirement(0).state, "satisfied")
        # R_1 should now be injured!
        self.assertEqual(worker.get_requirement(1).state, "injured")
        self.assertEqual(worker.get_requirement(1).injury_count, 1)

        # Stage 2: R_1 re-acts with element 20 (respects R_0's restraint of 8)
        action2 = worker.step([
            (1, 20, {"new_restraint": 20}),
        ])
        self.assertIsNotNone(action2)
        self.assertEqual(action2["requirement_index"], 1)
        self.assertEqual(worker.get_requirement(1).state, "satisfied")

        # Verify finite injury report
        verif = worker.verify_finite_injury(max_injuries_per_priority={0: 0, 1: 1, 2: 2})
        self.assertTrue(verif["finite_injury_verified"])
        self.assertEqual(verif["injury_counts"][0], 0)
        self.assertEqual(verif["injury_counts"][1], 1)


if __name__ == "__main__":
    unittest.main()
