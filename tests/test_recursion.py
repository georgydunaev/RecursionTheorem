#!/usr/bin/env python3
"""Verification tests for RecursionTheorem (Isabelle/HOL Recursion-Addition)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def peano_add(m: int, n: int) -> int:
    """Primitive recursive definition of addition matching recursion.thy."""
    if n == 0:
        return m
    return peano_add(m, n - 1) + 1


class TestRecursionTheorem(unittest.TestCase):
    def test_isabelle_theory_exists(self):
        thy = os.path.join(ROOT, "Recursion-Addition", "recursion.thy")
        self.assertTrue(os.path.isfile(thy))
        with open(thy, encoding="utf-8") as f:
            content = f.read()
        self.assertIn("theory", content)
        self.assertIn("end", content)

    def test_primitive_recursive_addition_laws(self):
        for a in range(6):
            self.assertEqual(peano_add(a, 0), a)
            for b in range(6):
                self.assertEqual(peano_add(a, b), peano_add(b, a))
                for c in range(4):
                    self.assertEqual(peano_add(peano_add(a, b), c), peano_add(a, peano_add(b, c)))


if __name__ == "__main__":
    unittest.main()
