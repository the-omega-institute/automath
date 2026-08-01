#!/usr/bin/env python3
"""Regression tests for the Deepening Delta verification battery."""

import math
import unittest

from verify_deepening_delta import (
    bell_number,
    classify_support_three,
    factorint_fibonacci,
    omega,
    omega_big,
    upper_fiber_exhaustive,
    upper_fiber_threshold,
)


class DeepeningDeltaTests(unittest.TestCase):
    def test_corrected_n30_data_and_types(self):
        exhaustive = upper_fiber_exhaustive(30)
        threshold = upper_fiber_threshold(30)

        expected = (20, 22, 31, 244, 671)
        self.assertEqual(exhaustive.a_count, 52)
        self.assertEqual(exhaustive.minimal_generators, expected)
        self.assertEqual(threshold.a_count, 52)
        self.assertEqual(threshold.minimal_generators, expected)

        realized = {
            classify_support_three(m, 30) for m in expected
        }
        self.assertEqual(
            realized,
            {"Gamma_1", "Gamma_4", "Gamma_5", "Gamma_7", "Gamma_8"},
        )
        self.assertTrue(
            {"Gamma_3", "Gamma_6", "Gamma_9"}.isdisjoint(realized)
        )

    def test_independent_methods_agree_through_30(self):
        for n in range(2, 31):
            with self.subTest(n=n):
                exhaustive = upper_fiber_exhaustive(n)
                threshold = upper_fiber_threshold(n)
                self.assertEqual(exhaustive.a_count, threshold.a_count)
                self.assertEqual(
                    exhaustive.minimal_generators,
                    threshold.minimal_generators,
                )

    def test_finite_growth_bounds_through_50(self):
        for n in range(3, 51):
            with self.subTest(n=n):
                result = upper_fiber_threshold(n)
                k = omega(n)
                big_omega = omega_big(factorint_fibonacci(n))
                subset_bound = sum(
                    math.comb(big_omega, r)
                    for r in range(0, min(k, big_omega) + 1)
                )
                self.assertLessEqual(len(result.minimal_generators), subset_bound)
                self.assertLessEqual(len(result.minimal_generators), n**k)
                if n % 2 == 1:
                    self.assertGreaterEqual(
                        len(result.minimal_generators), bell_number(k)
                    )


if __name__ == "__main__":
    unittest.main(verbosity=2)
