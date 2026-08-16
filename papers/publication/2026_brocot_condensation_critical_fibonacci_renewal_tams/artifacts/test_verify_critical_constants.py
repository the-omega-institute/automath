#!/usr/bin/env python3
"""Tests for verify_critical_constants.py."""

from __future__ import annotations

import unittest

import mpmath as mp

from verify_critical_constants import (
    critical_exponent,
    exact_constants,
    truncated_context_constants,
)


class CriticalConstantsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sigma = critical_exponent()

    def test_defining_zeta_equation_and_range(self) -> None:
        residual = mp.zeta(self.sigma - 1) / mp.zeta(self.sigma) - 2
        self.assertLess(abs(residual), mp.mpf("1e-40"))
        self.assertGreater(self.sigma, 2)
        self.assertLess(self.sigma, 3)

    def test_closed_form_constants(self) -> None:
        alpha, exponent, k_c, scale = exact_constants(self.sigma)
        self.assertAlmostEqual(float(alpha), 1.4787507857339603, places=14)
        self.assertAlmostEqual(float(exponent), 0.5212492142660397, places=14)
        self.assertAlmostEqual(float(k_c), 15.07798619025016, places=13)
        self.assertAlmostEqual(float(scale), 6.2639823573126, places=13)

    def test_totient_sums_approach_context_constant_from_below(self) -> None:
        values = truncated_context_constants(self.sigma, (1_000, 10_000, 100_000))
        sequence = list(values.values())
        self.assertEqual(sequence, sorted(sequence))
        self.assertGreater(sequence[-1], 7.95)
        self.assertLess(sequence[-1], 8.0)


if __name__ == "__main__":
    unittest.main()
