#!/usr/bin/env python3
"""Unit tests for the all-real pressure verification helpers."""

from __future__ import annotations

import math
import unittest

from verify_real_tilt_pressure import (
    coexistence_local_counterexample_search,
    critical_slope_partial,
    negative_continued_fraction_value,
    orbit_padding_counterexample_search,
    regular_partial_quotient_sum,
    stern_brocot_layer_denominators,
)


class AllRealPressureHelpersTest(unittest.TestCase):
    def test_regular_and_negative_costs_agree(self) -> None:
        examples = {
            (1,): (1, 2),
            (2,): (1, 3),
            (1, 1): (2, 3),
            (1, 2): (3, 5),
        }
        for composition, fraction in examples.items():
            self.assertEqual(
                negative_continued_fraction_value(composition), fraction
            )
            numerator, denominator = fraction
            self.assertEqual(
                regular_partial_quotient_sum(numerator, denominator) - 1,
                sum(composition),
            )

    def test_layer_counts_and_denominator_extrema(self) -> None:
        fibonacci = [0, 1]
        for _ in range(10):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        for depth in range(1, 9):
            denominators = stern_brocot_layer_denominators(depth)
            self.assertEqual(len(denominators), 2 ** (depth - 1))
            self.assertGreaterEqual(min(denominators), depth + 1)
            self.assertLessEqual(max(denominators), fibonacci[depth + 2])
            self.assertEqual(
                sum(denominators), 2 * 3 ** (depth - 1)
            )

    def test_truncated_critical_slope_is_finite_and_positive(self) -> None:
        numerator, denominator, slope = critical_slope_partial(
            2.4787507857339603, 100
        )
        self.assertTrue(math.isfinite(numerator))
        self.assertTrue(math.isfinite(denominator))
        self.assertTrue(math.isfinite(slope))
        self.assertGreater(numerator, 0.0)
        self.assertGreater(denominator, 0.0)
        self.assertGreater(slope, 0.0)

    def test_orbit_capacity_and_padding_have_no_small_counterexamples(self) -> None:
        fibonacci = [0, 1]
        for _ in range(18):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        failures, capacity_checks, padding_checks = (
            orbit_padding_counterexample_search(12, 16, fibonacci)
        )
        self.assertEqual(failures, [])
        self.assertGreater(capacity_checks, 0)
        self.assertGreater(padding_checks, 0)

    def test_coexistence_local_critical_bound_has_no_small_counterexamples(
        self,
    ) -> None:
        fibonacci = [0, 1]
        for _ in range(22):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        failures, checks, rows = coexistence_local_counterexample_search(
            (12, 16, 20),
            fibonacci,
            2.4787507857339603,
            ((0.04, 0.02), (0.08, 0.02), (0.12, 0.02)),
        )
        self.assertEqual(failures, [])
        self.assertEqual(checks, 9)
        self.assertEqual(len(rows), checks)
        self.assertTrue(all(row[3] > 0 for row in rows))


if __name__ == "__main__":
    unittest.main()
