#!/usr/bin/env python3
"""Comprehensive verification test suite for RecursionTheorem.

Covers:
1. Isabelle/ZF Theory syntax, sound structure, and zero unproven obligations.
2. Primitive Recursive Function (PRF) schema, addition, multiplication, exponentiation, factorial.
3. Peano arithmetic verification (commutativity, associativity, distributivity).
4. Unbounded minimalization (Mu-operator).
5. Kleene's First Recursion Theorem (least fixed point of continuous functionals).
6. Kleene's Second Recursion Theorem (S-m-n theorem, diagonal, fixpoint index phi_e ~= phi_{f(e)}).
7. Parametric Recursion Theorem.
8. Rice's Theorem deduction and undecidability contradiction verification.
9. Quine construction via diagonal fixpoint.
10. Untyped Lambda Calculus and Fixed-Point Combinators (Y, Theta, Z, Church encodings).
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from recursion_theory.theory_checker import IsabelleTheoryChecker
from recursion_theory.primitive_recursion import (
    PRF,
    Zero,
    Succ,
    Proj,
    Compose,
    Comp,
    Recurse,
    Rec,
    Rec0,
    Mu,
    PRFVerifier,
    encode_prf,
    decode_prf,
    cantor_pair,
    cantor_unpair,
    prf_add,
    prf_mult,
    prf_exp,
    prf_fact,
    prf_pred,
    prf_sub,
    prf_const,
    prf_id,
    prf_is_zero,
    prf_signum,
    prf_max,
    prf_min,
    prf_equal,
)
from recursion_theory.kleene import (
    KleeneFirstRecursion,
    ProgramSystem,
    KleeneSecondRecursion,
    ParametricRecursionTheorem,
    RicesTheoremVerification,
    QuineConstructor,
    IndexMapping,
    IdentityMapping,
    ConstantMapping,
    ComposedMapping,
    DiagonalMapping,
    SmnMapping,
    ParametricMapping,
    ComputabilityLemmas,
    KleeneProofCertificate,
    DoubleRecursionTheorem,
)
from recursion_theory.combinators import (
    Var,
    Abs,
    App,
    Y_combinator,
    Theta_combinator,
    Z_combinator,
    church_numeral,
    church_to_int,
    reduce_step,
    reduce_normal_order,
    plus,
    times,
    succ,
    pred,
    iszero,
    make_recursive_factorial,
)


def peano_add(m: int, n: int) -> int:
    """Primitive recursive definition of addition matching recursion.thy."""
    if n == 0:
        return m
    return peano_add(m, n - 1) + 1


class TestIsabelleTheoryIntegrity(unittest.TestCase):
    """Verify Isabelle/ZF formalization integrity in Recursion-Addition/recursion.thy."""

    def setUp(self):
        self.thy_path = os.path.join(ROOT, "Recursion-Addition", "recursion.thy")
        self.checker = IsabelleTheoryChecker(self.thy_path)
        self.report = self.checker.check_integrity()

    def test_theory_file_exists(self):
        self.assertTrue(os.path.isfile(self.thy_path))

    def test_theory_header_and_soundness(self):
        self.assertEqual(self.report["theory_name"], "recursion")
        self.assertIn("ZF", self.report["imports"])
        self.assertTrue(self.report["is_sound"])

    def test_strict_zero_unproven_obligations(self):
        self.assertFalse(self.report["has_sorry"], "Forbidden 'sorry' found in recursion.thy")
        self.assertFalse(self.report["has_oops"], "Forbidden 'oops' found in recursion.thy")
        self.assertFalse(self.report["has_cheat"], "Forbidden 'cheat' found in recursion.thy")

    def test_theorems_and_lemmas_present(self):
        self.assertGreater(self.report["theorems_count"], 10)
        self.assertGreater(self.report["lemmas_count"], 15)
        self.assertIn("recursionthm", self.report["theorems"])
        self.assertIn("addition", self.report["theorems"])
        self.assertIn("domuncomp", self.report["theorems"])
        self.assertIn("recthm", self.report["locales"])

    def test_balanced_proof_blocks(self):
        self.assertEqual(
            self.report["proof_blocks"],
            self.report["qed_blocks"],
            "Mismatch between proof and qed keywords in recursion.thy",
        )


class TestPeanoAndPrimitiveRecursion(unittest.TestCase):
    """Verify primitive recursive functions and Peano arithmetic."""

    def test_primitive_recursive_addition_laws(self):
        for a in range(6):
            self.assertEqual(peano_add(a, 0), a)
            for b in range(6):
                self.assertEqual(peano_add(a, b), peano_add(b, a))
                for c in range(4):
                    self.assertEqual(peano_add(peano_add(a, b), c), peano_add(a, peano_add(b, c)))

    def test_prf_addition(self):
        add = prf_add()
        for x in range(6):
            for y in range(6):
                self.assertEqual(add(y, x), x + y)

    def test_prf_multiplication(self):
        mult = prf_mult()
        for x in range(5):
            for y in range(5):
                self.assertEqual(mult(y, x), x * y)

    def test_prf_exponentiation(self):
        exp = prf_exp()
        for base in range(4):
            for p in range(4):
                self.assertEqual(exp(p, base), base ** p)

    def test_prf_factorial(self):
        fact = prf_fact()
        expected = [1, 1, 2, 6, 24, 120]
        for n, exp_val in enumerate(expected):
            self.assertEqual(fact(n), exp_val)

    def test_prf_pred_and_sub(self):
        pred_fn = prf_pred()
        self.assertEqual(pred_fn(0), 0)
        self.assertEqual(pred_fn(5), 4)

        sub_fn = prf_sub()
        self.assertEqual(sub_fn(3, 7), 4)  # 7 - 3 = 4
        self.assertEqual(sub_fn(7, 3), 0)  # max(0, 3 - 7) = 0

    def test_peano_ring_identities(self):
        add = prf_add()
        mult = prf_mult()
        for a in range(4):
            for b in range(4):
                # Commutativity
                self.assertEqual(add(b, a), add(a, b))
                self.assertEqual(mult(b, a), mult(a, b))
                for c in range(4):
                    # Associativity
                    self.assertEqual(add(c, add(b, a)), add(add(c, b), a))
                    self.assertEqual(mult(c, mult(b, a)), mult(mult(c, b), a))
                    # Distributivity: a * (b + c) = (a * b) + (a * c)
                    lhs = mult(add(c, b), a)
                    rhs = add(mult(c, a), mult(b, a))
                    self.assertEqual(lhs, rhs)

    def test_mu_minimalization_operator(self):
        # Find y such that y * y - x == 0 for perfect squares
        # Let f(y, x) = abs(y * y - x)
        # Using simple PRF component
        class SquareDiff(Rec):
            def eval(self, *args):
                y, x = args[0], args[1]
                return abs(y * y - x)

        diff = SquareDiff(Proj(1, 1), Proj(3, 1))
        diff.arity = 2

        sqrt_op = Mu(diff)
        squares = [0, 1, 4, 9, 16, 25]
        for idx, sq in enumerate(squares):
            self.assertEqual(sqrt_op(sq), idx)


class TestKleeneFirstRecursionTheorem(unittest.TestCase):
    """Verify Kleene's First Recursion Theorem (least fixed points of continuous functionals)."""

    def test_factorial_least_fixed_point(self):
        # Functional Phi(f)(n) = 1 if n == 0 else n * f(n-1)
        def phi_fact(f):
            nxt = {}
            for n in range(7):
                if n == 0:
                    nxt[0] = 1
                elif (n - 1) in f:
                    nxt[n] = n * f[n - 1]
            return nxt

        history = KleeneFirstRecursion.iterate(phi_fact, steps=6)
        self.assertEqual(len(history), 7)
        self.assertEqual(history[0], {})
        self.assertEqual(history[1], {0: 1})
        self.assertEqual(history[2], {0: 1, 1: 1})
        self.assertEqual(history[3], {0: 1, 1: 1, 2: 2})

        lfp = KleeneFirstRecursion.least_fixed_point(phi_fact, max_iterations=10)
        self.assertEqual(lfp[5], 120)
        self.assertTrue(KleeneFirstRecursion.verify_fixed_point(phi_fact, lfp))

    def test_monotonicity(self):
        def phi_fact(f):
            nxt = {}
            if 0 not in f:
                nxt[0] = 1
            for k, v in f.items():
                nxt[k] = v
                nxt[k + 1] = (k + 1) * v
            return nxt

        f1 = {0: 1}
        f2 = {0: 1, 1: 1}
        self.assertTrue(KleeneFirstRecursion.verify_monotonicity(phi_fact, f1, f2))

    def test_continuity_and_fibonacci(self):
        # Chain of approximations
        chain = [{0: 1}, {0: 1, 1: 1}, {0: 1, 1: 1, 2: 2}]

        def phi_fact(f):
            nxt = {}
            if 0 not in f:
                nxt[0] = 1
            for k, v in f.items():
                nxt[k] = v
                nxt[k + 1] = (k + 1) * v
            return nxt

        self.assertTrue(KleeneFirstRecursion.verify_continuity(phi_fact, chain))

        # Fibonacci least fixed point
        def phi_fib(f):
            nxt = {}
            for n in range(8):
                if n == 0:
                    nxt[0] = 0
                elif n == 1:
                    nxt[1] = 1
                elif (n - 1) in f and (n - 2) in f:
                    nxt[n] = f[n - 1] + f[n - 2]
            return nxt

        fib_lfp = KleeneFirstRecursion.least_fixed_point(phi_fib, max_iterations=12)
        expected_fib = [0, 1, 1, 2, 3, 5, 8, 13]
        for idx, val in enumerate(expected_fib):
            self.assertEqual(fib_lfp[idx], val)
        self.assertTrue(KleeneFirstRecursion.verify_fixed_point(phi_fib, fib_lfp))


class TestKleeneSecondRecursionTheorem(unittest.TestCase):
    """Verify Kleene's Second Recursion Theorem and S-m-n parameter theorem."""

    def setUp(self):
        self.sys = ProgramSystem()
        # Program 1: successor x + 1
        self.sys.register_program_1(1, lambda x: x + 1)
        # Program 2: doubling 2 * x
        self.sys.register_program_1(2, lambda x: 2 * x)
        # Program 3: constant 42
        self.sys.register_program_1(3, lambda x: 42)

    def test_s11_parameter_theorem(self):
        # 2-argument program: f(x, y) = x^2 + y
        self.sys.register_program_2(10, lambda x, y: x * x + y)

        s_10_3 = self.sys.s11(10, 3)
        # phi(s(10, 3), y) should equal 3^2 + y = 9 + y
        for y in range(5):
            self.assertEqual(self.sys.phi(s_10_3, y), 9 + y)

    def test_general_smn_parameter_theorem(self):
        # 3-argument program: f(x1, y1, y2) = 2*x1 + 3*y1 + 5*y2
        # S^1_2 specializes x1, returning 2-argument function
        self.sys.register_program_n(20, 3, lambda x1, y1, y2: 2 * x1 + 3 * y1 + 5 * y2)
        e_spec1 = self.sys.s_m_n(20, 1, 2, 7)  # fixed x1 = 7, 2*7 = 14
        for y1 in range(3):
            for y2 in range(3):
                self.assertEqual(
                    self.sys.phi_n(e_spec1, y1, y2),
                    14 + 3 * y1 + 5 * y2,
                )

        # 4-argument program: g(x1, x2, y1, y2) = (x1 + x2) * (y1 + y2)
        # S^2_2 specializes (x1, x2), returning 2-argument function
        self.sys.register_program_n(30, 4, lambda x1, x2, y1, y2: (x1 + x2) * (y1 + y2))
        e_spec2 = self.sys.s_m_n(30, 2, 2, 3, 4)  # fixed x1=3, x2=4 -> sum = 7
        for y1 in range(3):
            for y2 in range(3):
                self.assertEqual(
                    self.sys.phi_n(e_spec2, y1, y2),
                    7 * (y1 + y2),
                )

    def test_second_recursion_theorem_fixpoint(self):
        kleene = KleeneSecondRecursion(self.sys)

        # Transformation f: shifts program index to another program
        # that behaves according to a known transformation
        def f(idx: int) -> int:
            new_idx = self.sys._next_index
            self.sys._next_index += 1
            # Returns function y -> y + (idx % 5)
            self.sys.register_program_1(new_idx, lambda y: y + (idx % 5))
            return new_idx

        e = kleene.find_fixed_point_index(f)
        self.assertTrue(kleene.verify_fixed_point(e, f, test_inputs=[0, 1, 2, 5, 10]))

    def test_self_referential_program_via_second_recursion(self):
        kleene = KleeneSecondRecursion(self.sys)

        # 1. Program that knows its own index e and computes e * 10 + x
        e_self = kleene.find_self_referential_index(lambda my_e, x: my_e * 10 + x)
        for x in range(4):
            self.assertEqual(self.sys.phi(e_self, x), e_self * 10 + x)

        # 2. Recursive computation of factorial via self-reference to own index:
        # phi_e(x) = 1 if x == 0 else x * phi_e(x - 1)
        def fact_body(my_e: int, x: int) -> int:
            if x <= 0:
                return 1
            prev = self.sys.phi(my_e, x - 1)
            return x * prev

        e_fact = kleene.find_self_referential_index(fact_body)
        expected_facts = [1, 1, 2, 6, 24, 120]
        for n, exp_val in enumerate(expected_facts):
            self.assertEqual(self.sys.phi(e_fact, n), exp_val)

    def test_parametric_recursion_theorem(self):
        param_rec = ParametricRecursionTheorem(self.sys)

        # 3-argument function: g(e, p, y) = y + p
        def g(e: int, p: int, y: int):
            return y + p

        h = param_rec.solve_parametric(g)
        for p in [2, 5, 10]:
            h_p = h(p)
            for y in range(4):
                self.assertEqual(self.sys.phi(h_p, y), y + p)

    def test_rices_theorem_contradiction(self):
        kleene = KleeneSecondRecursion(self.sys)
        # Property P: "computes an even number on input 0"
        idx_even = self.sys.register_program_1(50, lambda x: 4)
        idx_odd = self.sys.register_program_1(51, lambda x: 5)

        # Hypothesized decider that claims to decide P
        def candidate_decider(e: int) -> int:
            # Any total boolean function
            return 1 if (e % 2 == 0) else 0

        e_star, fe_star, contradiction = RicesTheoremVerification.derive_contradiction(
            kleene, candidate_decider, idx_even, idx_odd
        )
        self.assertTrue(contradiction)

    def test_quine_constructor(self):
        quine = QuineConstructor.construct_python_quine()
        self.assertTrue(QuineConstructor.verify_quine(quine))


class TestLambdaCalculusAndCombinators(unittest.TestCase):
    """Verify fixed-point combinators in untyped lambda calculus."""

    def test_alpha_beta_reduction(self):
        # (\\x. x) y -> y
        term = App(Abs("x", Var("x")), Var("y"))
        norm, steps = reduce_normal_order(term)
        self.assertEqual(norm.to_string(), "y")
        self.assertEqual(steps, 1)

    def test_capture_avoiding_substitution(self):
        # (\\x. (\\y. x)) y -> rename y to avoid capture
        # Replacement is Var("y"), subbing for x inside \\y. x
        abs_term = Abs("y", Var("x"))
        res = abs_term.substitute("x", Var("y"))
        self.assertIsInstance(res, Abs)
        self.assertNotEqual(res.param, "y")
        self.assertEqual(res.body.to_string(), "y")

    def test_church_numerals(self):
        for n in range(5):
            cn = church_numeral(n)
            self.assertEqual(church_to_int(cn), n)

    def test_church_arithmetic(self):
        # 2 + 3 = 5
        c2 = church_numeral(2)
        c3 = church_numeral(3)
        sum_term = App(App(plus(), c2), c3)
        res, _ = reduce_normal_order(sum_term, max_steps=500)
        self.assertEqual(church_to_int(res), 5)

        # 2 * 3 = 6
        prod_term = App(App(times(), c2), c3)
        res_prod, _ = reduce_normal_order(prod_term, max_steps=500)
        self.assertEqual(church_to_int(res_prod), 6)

    def test_fixed_point_combinator_expansion(self):
        # Y F to F (Y F)
        # Using Turing's Theta combinator: Theta F reduces directly in normal order!
        Theta = Theta_combinator()
        F = Var("F")
        term = App(Theta, F)
        # 1 step should unpack Theta
        step1 = reduce_step(term)
        self.assertIsNotNone(step1)


class TestModularPrimitiveRecursiveDatatypes(unittest.TestCase):
    """Verify Ticket 7459: Modular inductive PRF schemas and evaluation semantics."""

    def test_inductive_constructors_and_aliases(self):
        z = Zero(2)
        s = Succ()
        p = Proj(3, 2)
        c = Compose(s, [p])
        r = Recurse(Zero(1), Compose(s, [Proj(3, 2)]))

        self.assertIs(Comp, Compose)
        self.assertIs(Rec, Recurse)
        self.assertIsInstance(c, Comp)
        self.assertIsInstance(r, Rec)
        self.assertEqual(z(5, 9), 0)
        self.assertEqual(s(7), 8)
        self.assertEqual(p(10, 20, 30), 20)

    def test_ast_metrics_and_subterms(self):
        z = Zero(1)
        s = Succ()
        p = Proj(3, 2)
        self.assertEqual(z.size, 1)
        self.assertEqual(z.depth, 1)
        self.assertEqual(z.subterms(), [])

        c = Compose(s, [p])
        self.assertEqual(c.size, 3)
        self.assertEqual(c.depth, 2)
        self.assertEqual(len(c.subterms()), 2)
        self.assertTrue(c.is_well_formed())

        add_fn = prf_add()
        self.assertTrue(add_fn.size > 3)
        self.assertTrue(add_fn.depth >= 3)
        self.assertTrue(add_fn.is_well_formed())

    def test_dictionary_serialization_and_deserialization(self):
        add_fn = prf_add()
        d = add_fn.to_dict()
        self.assertEqual(d["type"], "Recurse")
        recovered = PRF.from_dict(d)
        self.assertEqual(recovered, add_fn)
        for x in range(4):
            for y in range(4):
                self.assertEqual(recovered(y, x), add_fn(y, x))

    def test_structural_equality_and_hashing(self):
        z1 = Zero(2)
        z2 = Zero(2)
        z3 = Zero(3)
        self.assertEqual(z1, z2)
        self.assertNotEqual(z1, z3)
        self.assertEqual(hash(z1), hash(z2))

        p1 = Proj(3, 2)
        p2 = Proj(3, 2)
        self.assertEqual(p1, p2)
        self.assertEqual(hash(p1), hash(p2))

        c1 = Compose(Succ(), [Proj(2, 1)])
        c2 = Compose(Succ(), [Proj(2, 1)])
        self.assertEqual(c1, c2)
        self.assertEqual(hash(c1), hash(c2))

    def test_formal_semantics_verifier(self):
        z = Zero(2)
        self.assertTrue(PRFVerifier.verify_zero_semantics(z, [(1, 2), (0, 0), (10, 5)]))

        s = Succ()
        self.assertTrue(PRFVerifier.verify_succ_semantics(s, [0, 1, 2, 10]))

        p = Proj(3, 2)
        self.assertTrue(PRFVerifier.verify_proj_semantics(p, [(1, 2, 3), (9, 8, 7)]))

        c = Compose(s, [p])
        self.assertTrue(PRFVerifier.verify_compose_semantics(c, [(1, 2, 3), (4, 5, 6)]))

        add_fn = prf_add()
        test_samples = [(y, x) for y in range(4) for x in range(4)]
        self.assertTrue(PRFVerifier.verify_recurse_semantics(add_fn, test_samples))
        self.assertTrue(PRFVerifier.verify_inductive_semantics(add_fn, test_samples))

    def test_cantor_pairing_and_godel_numbering(self):
        pairs = [(0, 0), (1, 0), (0, 1), (2, 3), (10, 20)]
        for x, y in pairs:
            c = cantor_pair(x, y)
            self.assertEqual(cantor_unpair(c), (x, y))

        prfs = [
            Zero(1),
            Succ(),
            Proj(3, 2),
            Compose(Succ(), [Proj(1, 1)]),
            prf_add(),
            prf_mult(),
            prf_pred(),
        ]
        for fn in prfs:
            code = encode_prf(fn)
            self.assertIsInstance(code, int)
            self.assertGreater(code, 0)
            decoded = decode_prf(code)
            self.assertEqual(decoded, fn)
            self.assertEqual(decoded.arity, fn.arity)

    def test_derived_prfs_and_algebraic_properties(self):
        const5 = prf_const(5, arity=2)
        self.assertEqual(const5(10, 20), 5)
        self.assertEqual(const5(0, 0), 5)

        id_fn = prf_id(arity=2)
        self.assertEqual(id_fn(42, 99), 42)

        is_zero = prf_is_zero()
        self.assertEqual(is_zero(0), 1)
        self.assertEqual(is_zero(1), 0)
        self.assertEqual(is_zero(10), 0)

        sgn = prf_signum()
        self.assertEqual(sgn(0), 0)
        self.assertEqual(sgn(1), 1)
        self.assertEqual(sgn(100), 1)

        max_fn = prf_max()
        min_fn = prf_min()
        eq_fn = prf_equal()
        for x in range(5):
            for y in range(5):
                self.assertEqual(max_fn(y, x), max(x, y))
                self.assertEqual(min_fn(y, x), min(x, y))
                self.assertEqual(eq_fn(y, x), 1 if x == y else 0)

    def test_eval_trace(self):
        add_fn = prf_add()
        res, trace = add_fn.eval_trace(3, 4)
        self.assertEqual(res, 7)
        self.assertTrue(len(trace) >= 2)


class TestIndexMappingAndComputabilityLemmas(unittest.TestCase):
    """Verify Ticket 7458: Index mapping functions, computability lemmas, and decomposed fixpoint."""

    def setUp(self):
        self.sys = ProgramSystem()
        self.sys.register_program_1(1, lambda x: x + 1)
        self.sys.register_program_1(2, lambda x: 2 * x)
        self.sys.register_program_2(10, lambda x, y: x * x + y)

    def test_index_mapping_classes(self):
        id_map = IdentityMapping()
        self.assertEqual(id_map(42), 42)

        const_map = ConstantMapping(99)
        self.assertEqual(const_map(12), 99)

        comp_map = id_map.compose(const_map)
        self.assertEqual(comp_map(7), 99)

        diag_map = DiagonalMapping(self.sys)
        self.assertEqual(diag_map(10), self.sys.s11(10, 10))

        smn_map = SmnMapping(self.sys, 1, 1, (3,))
        spec_idx = smn_map(10)
        for y in range(4):
            self.assertEqual(self.sys.phi(spec_idx, y), 3 * 3 + y)

    def test_lemma_smn_currying(self):
        self.sys.register_program_2(100, lambda x, y: 3 * x + y)
        self.assertTrue(
            ComputabilityLemmas.verify_smn_currying(
                self.sys,
                e=100,
                m=1,
                n=1,
                fixed_args=(5,),
                test_inputs=[(0,), (1,), (2,), (5,)]
            )
        )

    def test_lemma_smn_iteration(self):
        self.sys.register_program_n(200, 3, lambda x1, x2, y: 2 * x1 + 3 * x2 + 5 * y)
        self.assertTrue(
            ComputabilityLemmas.verify_smn_iteration(
                self.sys,
                e=200,
                m1=1,
                m2=1,
                n=1,
                fixed1=(4,),
                fixed2=(6,),
                test_inputs=[(0,), (1,), (2,)]
            )
        )

    def test_lemma_diagonal_computability(self):
        self.assertTrue(
            ComputabilityLemmas.verify_diagonal_computability(
                self.sys,
                test_indices=[1, 2, 10, 100]
            )
        )

    def test_lemma_padding(self):
        self.assertTrue(
            ComputabilityLemmas.verify_padding_lemma(
                self.sys,
                e=1,
                count=5,
                test_inputs=[0, 1, 2, 5]
            )
        )

    def test_lemma_index_composition(self):
        self.assertTrue(
            ComputabilityLemmas.verify_composition_lemma(
                self.sys,
                e1=1,
                e2=2,
                test_inputs=[0, 1, 2, 5]
            )
        )
        comp_idx = self.sys.compose_programs(1, 2)
        for x in [0, 1, 2, 5]:
            self.assertEqual(self.sys.phi(comp_idx, x), (2 * x) + 1)

    def test_lemma_universal_evaluation(self):
        u = self.sys.universal_index()
        pairs = [(1, 5), (1, 10), (2, 3), (2, 7)]
        self.assertTrue(
            ComputabilityLemmas.verify_universal_function(
                self.sys,
                u=u,
                test_pairs=pairs
            )
        )

    def test_decomposed_kleene_proof_certificate(self):
        kleene = KleeneSecondRecursion(self.sys)

        def f(idx: int) -> int:
            new_idx = self.sys._next_index
            self.sys._next_index += 1
            self.sys.register_program_1(new_idx, lambda y: y + 10)
            return new_idx

        cert = kleene.decompose_proof(f, test_inputs=[0, 1, 2, 5])
        self.assertIsInstance(cert, KleeneProofCertificate)
        self.assertTrue(cert.is_verified)
        self.assertEqual(len(cert.proof_steps), 4)
        summary = cert.summary()
        self.assertIn("Kleene Second Recursion Theorem Proof Certificate", summary)
        self.assertIn("Auxiliary kernel index", summary)
        self.assertIn("Fixed point index", summary)

    def test_double_recursion_theorem(self):
        double_rec = DoubleRecursionTheorem(self.sys)

        def f1(a: int, b: int) -> int:
            idx = self.sys._next_index
            self.sys._next_index += 1
            self.sys.register_program_1(idx, lambda y: y + (a % 10) + (b % 10))
            return idx

        def f2(a: int, b: int) -> int:
            idx = self.sys._next_index
            self.sys._next_index += 1
            self.sys.register_program_1(idx, lambda y: y + ((a * b) % 10))
            return idx

        a, b = double_rec.find_double_fixed_points(f1, f2)
        verified = double_rec.verify_double_fixed_points(a, b, f1, f2, test_inputs=[0, 1, 2, 5])
        self.assertTrue(verified)


if __name__ == "__main__":
    unittest.main()
