"""Unit tests for Oracle Turing Machines, Turing Degrees, and Friedberg-Muchnik Theorem.

Covers:
1. Oracle Turing Machines (OTMs), trace generation, and use function computation.
2. The Use Principle (Oracle Continuity Lemma).
3. Explicit state-machine Oracle Turing Machine simulation.
4. Turing Reductions (identity, projections, and composition).
5. Relativized Halting, Turing Jump, and diagonal non-reducibility certificates.
6. Turing Degree algebra (0, 0', join, partial order, and incomparability).
7. Friedberg-Muchnik finite-injury priority argument:
   - Dynamic restraint preservation and follower allocation.
   - Restraint-violation injury mechanics.
   - Finite Injury Lemma bound verification (injuries <= 2^k - 1).
   - Incomparability certificate generation.
"""

import os
import sys
import unittest
from typing import Set

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from recursion_theory.turing_degrees import (
    OracleQuery,
    OracleExecutionTrace,
    OracleTuringMachine,
    TuringReduction,
    TuringDegree,
)
from recursion_theory.friedberg_muchnik import (
    FriedbergMuchnikRequirement,
    IncomparableCEDegreesCertificate,
    FriedbergMuchnikEngine,
)


class TestOracleTuringMachine(unittest.TestCase):
    """Test Oracle Turing Machine execution, trace logging, and the Use Principle."""

    def setUp(self):
        self.otm = OracleTuringMachine()
        self.primes: Set[int] = {2, 3, 5, 7, 11, 13, 17, 19, 23}

    def test_default_oracle_programs(self):
        """Verify standard canonical oracle programs."""
        # Program 0: Identity oracle query
        trace_id = self.otm.step_execute(0, self.primes, 7)
        self.assertTrue(trace_id.halted)
        self.assertEqual(trace_id.output_val, 1)
        self.assertEqual(trace_id.use, 8)  # queried 7, use is 7 + 1 = 8

        trace_id_nonprime = self.otm.step_execute(0, self.primes, 8)
        self.assertTrue(trace_id_nonprime.halted)
        self.assertEqual(trace_id_nonprime.output_val, 0)
        self.assertEqual(trace_id_nonprime.use, 9)

        # Program 1: Constant zero
        trace_c0 = self.otm.step_execute(1, self.primes, 100)
        self.assertTrue(trace_c0.halted)
        self.assertEqual(trace_c0.output_val, 0)
        self.assertEqual(trace_c0.use, 0)  # no queries made

        # Program 2: Constant one
        trace_c1 = self.otm.step_execute(2, self.primes, 100)
        self.assertTrue(trace_c1.halted)
        self.assertEqual(trace_c1.output_val, 1)
        self.assertEqual(trace_c1.use, 0)

        # Program 3: Inverted oracle query
        trace_inv = self.otm.step_execute(3, self.primes, 7)
        self.assertTrue(trace_inv.halted)
        self.assertEqual(trace_inv.output_val, 0)

        # Program 4: Bounded existential search
        # exists y <= 4 such that y in primes (2 is prime, so 1)
        trace_exists = self.otm.step_execute(4, self.primes, 4)
        self.assertTrue(trace_exists.halted)
        self.assertEqual(trace_exists.output_val, 1)

        # Program 7: Parity of primes up to 5: 2, 3, 5 are primes (3 primes, parity 1)
        trace_parity = self.otm.step_execute(7, self.primes, 5)
        self.assertTrue(trace_parity.halted)
        self.assertEqual(trace_parity.output_val, 1)

    def test_use_principle_verification(self):
        """Verify the Use Principle (Oracle Continuity Lemma)."""
        oracle_a = {2, 3, 5, 7}
        # oracle_b agrees with oracle_a on all elements < 10, but differs on 15
        oracle_b = {2, 3, 5, 7, 15}

        # Program 4 queries up to input x=6, so use is 7
        verified, msg = self.otm.verify_use_principle(4, oracle_a, oracle_b, x=6)
        self.assertTrue(verified, f"Use Principle failed: {msg}")

        # If oracle_c differs below the use (at 2 < 3)
        oracle_c = {3, 5, 7}
        verified_diff, msg_diff = self.otm.verify_use_principle(4, oracle_a, oracle_c, x=6)
        # Hypothesis of agreement below use does not hold
        self.assertFalse(verified_diff)

    def test_explicit_state_machine_simulation(self):
        """Verify explicit state-machine execution with query state and yes/no transitions."""
        # Simple TM that queries input value directly:
        # q0: if tape has 1, move to query state
        # q_query: queries query_tape_val (0). If yes, go to q_yes; if no, go to q_no
        # q_yes: write 1, halt
        # q_no: write 0, halt
        transitions = {
            ("q0", 1): ("q_query", 1, 0),
            ("q0", 0): ("q_query", 0, 0),
            ("q_yes", 1): ("q_halt", 1, 0),
            ("q_yes", 0): ("q_halt", 1, 0),
            ("q_no", 1): ("q_halt", 0, 0),
            ("q_no", 0): ("q_halt", 0, 0),
        }

        oracle_with_zero = {0, 5, 10}
        trace_yes = self.otm.simulate_state_machine(
            transitions=transitions,
            query_state="q_query",
            yes_state="q_yes",
            no_state="q_no",
            halt_state="q_halt",
            oracle=oracle_with_zero,
            input_val=1,
            max_steps=50,
        )
        self.assertTrue(trace_yes.halted)
        self.assertEqual(trace_yes.output_val, 1)

        oracle_without_zero = {5, 10}
        trace_no = self.otm.simulate_state_machine(
            transitions=transitions,
            query_state="q_query",
            yes_state="q_yes",
            no_state="q_no",
            halt_state="q_halt",
            oracle=oracle_without_zero,
            input_val=1,
            max_steps=50,
        )
        self.assertTrue(trace_no.halted)
        self.assertEqual(trace_no.output_val, 0)


class TestTuringReductions(unittest.TestCase):
    """Test Turing reductions, composition, and the Turing Jump operator."""

    def setUp(self):
        self.otm = OracleTuringMachine()

    def test_identity_reduction(self):
        """Verify A <=_T A via identity reduction program 0."""
        target_a = {1, 3, 5, 7, 9}
        reduction = TuringReduction(0, self.otm)
        verified = reduction.verify_reduction(target_a, target_a, domain=range(15))
        self.assertTrue(verified)

    def test_disjoint_sum_projections(self):
        """Verify A <=_T A (+) B and B <=_T A (+) B via programs 5 and 6."""
        set_a = {0, 2, 4}
        set_b = {1, 3, 5}
        # Disjoint sum A (+) B: 2*a for a in A, 2*b + 1 for b in B
        joined = {2 * x for x in set_a} | {2 * y + 1 for y in set_b}

        # Left projection (program 5) computes A from joined
        red_a = TuringReduction(5, self.otm)
        self.assertTrue(red_a.verify_reduction(set_a, joined, domain=range(10)))

        # Right projection (program 6) computes B from joined
        red_b = TuringReduction(6, self.otm)
        self.assertTrue(red_b.verify_reduction(set_b, joined, domain=range(10)))

    def test_reduction_composition(self):
        """Verify reduction transitivity: A <=_T B and B <=_T C implies A <=_T C."""
        # A is even numbers: {0, 2, 4, 6}
        # B is multiples of 4: {0, 4, 8, 12}
        # C is multiples of 8: {0, 8, 16, 24}
        # Suppose B <=_T C and A <=_T B
        # Let's register reduction from A to B: A(x) = B(2 * x)
        def ab_fn(x: int, oracle_b):
            return oracle_b(2 * x)

        idx_ab = self.otm.allocate_index()
        self.otm.register_oracle_program(idx_ab, ab_fn)
        red_ab = TuringReduction(idx_ab, self.otm)

        # Reduction from B to C: B(y) = C(2 * y)
        def bc_fn(y: int, oracle_c):
            return oracle_c(2 * y)

        idx_bc = self.otm.allocate_index()
        self.otm.register_oracle_program(idx_bc, bc_fn)
        red_bc = TuringReduction(idx_bc, self.otm)

        # Composed reduction A <=_T C
        red_ac = red_ab.compose(red_bc)

        oracle_c = {0, 8, 16, 24, 32}
        # B should be {0, 4, 8, 12, 16}
        # A should be {0, 2, 4, 6, 8}
        expected_a = {0, 2, 4, 6, 8}

        verified = red_ac.verify_reduction(expected_a, oracle_c, domain=range(10))
        self.assertTrue(verified)

    def test_turing_jump_and_strict_separation(self):
        """Verify that the Turing jump A' is well-defined and strictly dominates A."""
        base_set = {1, 2, 3}
        jump = TuringReduction.oracle_jump(base_set, domain=range(10), machine=self.otm)
        # Jump is a subset of domain where programs halt
        self.assertIsInstance(jump, set)

        # Diagonalization certificate: no candidate reduction computes A' from A
        strict, cert = TuringReduction.verify_jump_strict(
            base_set,
            candidate_reduction_indices=[0, 1, 2, 3],
            machine=self.otm,
        )
        self.assertTrue(strict)
        self.assertTrue(len(cert) > 0)


class TestTuringDegrees(unittest.TestCase):
    """Test Turing Degree algebraic properties, join, and partial order."""

    def test_degree_zero_and_zero_jump(self):
        """Verify properties of degree 0 and degree 0'."""
        deg_0 = TuringDegree.ZERO
        deg_0_prime = TuringDegree.ZERO_JUMP

        self.assertTrue(deg_0.is_computable())
        self.assertFalse(deg_0_prime.is_computable())

        # 0 <= 0' and 0 < 0'
        self.assertTrue(deg_0 <= deg_0_prime)
        self.assertTrue(deg_0 < deg_0_prime)
        self.assertFalse(deg_0_prime <= deg_0)

    def test_degree_join(self):
        """Verify degree join deg(A) v deg(B) = deg(A (+) B)."""
        set_a = {1, 3, 5}
        set_b = {2, 4, 6}
        deg_a = TuringDegree(set_a, name="deg(A)", is_computable=True)
        deg_b = TuringDegree(set_b, name="deg(B)", is_computable=True)

        joined = deg_a.join(deg_b)
        self.assertTrue(joined.is_computable())
        self.assertEqual(joined.name, "(deg(A) v deg(B))")

        # Operator | syntax
        joined_op = deg_a | deg_b
        self.assertEqual(joined.name, joined_op.name)

        # Semilattice least upper bound bounds: a <= a v b and b <= a v b
        self.assertTrue(deg_a <= joined)
        self.assertTrue(deg_b <= joined)
        self.assertTrue(joined >= deg_a)
        self.assertTrue(joined >= deg_b)

    def test_degree_meet_and_semilattice_order(self):
        """Verify degree meet (greatest lower bound) and order relations."""
        deg_0 = TuringDegree.ZERO
        set_a = {1, 3, 5}
        set_b = {2, 4, 6}
        deg_a = TuringDegree(set_a, name="deg(A)", is_computable=False)
        deg_b = TuringDegree(set_b, name="deg(B)", is_computable=False)

        # 0 ^ a = 0 and a ^ 0 = 0
        meet_zero_a = deg_0.meet(deg_a)
        self.assertEqual(meet_zero_a, deg_0)
        meet_a_zero = deg_a & deg_0
        self.assertEqual(meet_a_zero, deg_0)

        # If a <= j, then a ^ j = a
        j = deg_a | deg_b
        self.assertTrue(deg_a <= j)
        self.assertEqual(deg_a.meet(j), deg_a)
        self.assertEqual(j.meet(deg_a), deg_a)
        self.assertEqual(deg_a & j, deg_a)

        # For incomparable non-computable degrees without minimal pair flag, meet is None
        self.assertIsNone(deg_a.meet(deg_b))

        # With minimal pair certification, meet is 0
        meet_min = deg_a.meet(deg_b, is_minimal_pair=True)
        self.assertEqual(meet_min, deg_0)

        # Strict order: a < a v b when b is not <= a
        self.assertTrue(deg_a < j)
        self.assertTrue(j > deg_a)

        # Degree jump strict inequality: a < a'
        deg_a_prime = deg_a.jump(domain=range(10))
        self.assertTrue(deg_a <= deg_a_prime)
        self.assertTrue(deg_a < deg_a_prime)
        self.assertFalse(deg_a_prime <= deg_a)
        self.assertTrue(deg_a_prime > deg_a)

    def test_degree_incomparability_checker(self):
        """Verify that two independent degrees are detected as incomparable."""
        deg_x = TuringDegree({1, 2}, name="deg(X)", is_computable=False)
        deg_y = TuringDegree({3, 4}, name="deg(Y)", is_computable=False)

        self.assertTrue(deg_x.is_incomparable_with(deg_y))
        self.assertFalse(deg_x.is_incomparable_with(deg_x))


class TestFriedbergMuchnikEngine(unittest.TestCase):
    """Test the Friedberg-Muchnik finite-injury priority argument."""

    def setUp(self):
        self.engine = FriedbergMuchnikEngine(num_pairs=4)

    def test_initial_requirements_setup(self):
        """Verify initial requirement initialization and alternating target sets."""
        self.assertEqual(len(self.engine.requirements), 8)

        # R_0: P_0 targets A, oracle B
        r0 = self.engine.requirements[0]
        self.assertEqual(r0.target_set, "A")
        self.assertEqual(r0.oracle_set, "B")
        self.assertEqual(r0.state, "waiting")

        # R_1: N_0 targets B, oracle A
        r1 = self.engine.requirements[1]
        self.assertEqual(r1.target_set, "B")
        self.assertEqual(r1.oracle_set, "A")
        self.assertEqual(r1.state, "waiting")

    def test_stage_by_stage_execution_and_actions(self):
        """Verify that requirements act in priority order and enumerate followers."""
        # Execute first stage
        acted_first = self.engine.step_stage()
        self.assertIsNotNone(acted_first)

        # Check action log
        self.assertTrue(len(self.engine.action_log) > 0)
        first_action = self.engine.action_log[0]
        self.assertEqual(first_action["requirement"], acted_first)

        # Run several stages
        self.engine.run_stages(10)
        self.assertTrue(self.engine.stage >= 10)

        # Either A or B has received elements
        self.assertTrue(len(self.engine.A) > 0 or len(self.engine.B) > 0)

    def test_finite_injury_lemma_bound(self):
        """Verify the Finite Injury Lemma: injuries(R_k) <= 2^k - 1."""
        # Run until stabilized or 30 stages
        self.engine.run_until_stabilized(max_stages=30)

        for req in self.engine.requirements.values():
            bound = req.theoretical_injury_bound()
            self.assertLessEqual(
                req.injury_count,
                bound,
                f"Requirement {req.index} suffered {req.injury_count} injuries, exceeding 2^{req.priority}-1 = {bound}",
            )

        self.assertTrue(self.engine.verify_finite_injuries())

    def test_incomparability_verification_and_certificate(self):
        """Verify that constructed sets A and B satisfy A not <=_T B and B not <=_T A."""
        self.engine.run_until_stabilized(max_stages=40)

        a_not_le_b, b_not_le_a, diag = self.engine.verify_incomparability()
        self.assertTrue(a_not_le_b, f"A reduced to B: {diag}")
        self.assertTrue(b_not_le_a, f"B reduced to A: {diag}")

        cert = self.engine.generate_certificate()
        self.assertIsInstance(cert, IncomparableCEDegreesCertificate)
        self.assertTrue(cert.is_valid())
        self.assertTrue(cert.finite_injury_verified)
        self.assertTrue(cert.a_not_reducible_to_b)
        self.assertTrue(cert.b_not_reducible_to_a)
        self.assertTrue(cert.a_is_ce)
        self.assertTrue(cert.b_is_ce)

        # Summary contains formal deduction
        self.assertIn("Friedberg-Muchnik Theorem", cert.summary)
        self.assertIn("incomparable c.e. degrees", cert.summary)

        # Degree join and meet properties on certificate
        self.assertIsInstance(cert.degree_join, TuringDegree)
        self.assertEqual(cert.degree_join.name, "(a v b)")
        self.assertIsNone(cert.degree_meet)


if __name__ == "__main__":
    unittest.main()
