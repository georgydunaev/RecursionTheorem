#!/usr/bin/env python3
"""Test runner for RecursionTheorem verification test suites."""

import os
import sys
import unittest

def main():
    root = os.path.dirname(os.path.abspath(__file__))
    loader = unittest.defaultTestLoader
    suite = loader.discover(os.path.join(root, "tests"))
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)

if __name__ == "__main__":
    main()
