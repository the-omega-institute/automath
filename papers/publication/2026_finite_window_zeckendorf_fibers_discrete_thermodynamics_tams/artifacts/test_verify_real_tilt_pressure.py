#!/usr/bin/env python3
"""Unit tests for the all-real pressure verification helpers."""

from __future__ import annotations

import math
import unittest

import verify_real_tilt_pressure as verification
from verify_real_tilt_pressure import (
    coexistence_local_counterexample_search,
    critical_slope_partial,
    negative_continued_fraction_value,
    orbit_padding_counterexample_search,
    regular_partial_quotient_sum,
    stern_brocot_layer_denominators,
)


class AllRealPressureHelpersTest(unittest.TestCase):
    def test_dyadic_exact_multiplier_counts_match_direct_fibers(self) -> None:
        self.assertTrue(hasattr(verification, "dyadic_generator_cost_counters"))
        self.assertTrue(hasattr(verification, "dyadic_finite_window_count"))
        counters = verification.dyadic_generator_cost_counters(6)
        for exponent in range(1, 7):
            self.assertEqual(sum(counters[exponent].values()), 3 ** (exponent - 1))

        fibonacci = [0, 1]
        for _ in range(24):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        coefficients = [1]
        for m in range(1, 21):
            coefficients = verification.extend_coefficients(coefficients, fibonacci[m])
            direct = verification.Counter(coefficients)
            for exponent in range(2, 7):
                self.assertEqual(
                    verification.dyadic_finite_window_count(m, counters[exponent]),
                    direct[2**exponent],
                )

    def test_conditional_marked_scan_matches_direct_band_counts(self) -> None:
        self.assertTrue(hasattr(verification, "conditional_marked_scan"))
        fibonacci = [0, 1]
        for _ in range(20):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        generators = verification.weighted_generator_counters(18)
        rows = verification.conditional_marked_scan(
            (12, 16), generators, ((0.08, 0.02),)
        )
        coefficients = [1]
        direct_counts = {}
        for m in range(1, 17):
            coefficients = verification.extend_coefficients(coefficients, fibonacci[m])
            if m in (12, 16):
                direct_counts[m] = sum(
                    1
                    for level in coefficients
                    if abs(math.log(level) / m - 0.08) < 0.02
                )
        self.assertEqual([row[3] for row in rows], [direct_counts[12], direct_counts[16]])
        self.assertTrue(all(0.06 < row[4] < 0.10 for row in rows))
        self.assertTrue(all(0.0 < row[5] <= 1.0 for row in rows))

    def test_marked_window_counter_recovers_exact_fiber_spectrum(self) -> None:
        self.assertTrue(hasattr(verification, "marked_window_counter"))
        fibonacci = [0, 1]
        for _ in range(16):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        generators = verification.weighted_generator_counters(13)
        coefficients = [1]
        for m in range(1, 13):
            coefficients = verification.extend_coefficients(coefficients, fibonacci[m])
            if m < 4:
                continue
            marked = verification.marked_window_counter(m, generators)
            predicted = verification.Counter()
            for (cost, level), count in marked.items():
                self.assertLessEqual(cost, m + 1)
                predicted[level] += count
            actual = verification.Counter(coefficients)
            del actual[1]
            self.assertEqual(predicted, actual)

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
