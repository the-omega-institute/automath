#!/usr/bin/env python3
"""Unit tests for the all-real pressure verification helpers."""

from __future__ import annotations

import math
import unittest

import verify_real_tilt_pressure as verification
from verify_real_tilt_pressure import (
    coexistence_local_counterexample_search,
    critical_slope_partial,
    matrix_bridge_audit,
    negative_continued_fraction_value,
    orbit_padding_counterexample_search,
    prime_support_inverse_h,
    prime_support_local_asymptotic_audit,
    prime_support_saddle,
    regular_partial_quotient_sum,
    stern_brocot_layer_denominators,
    stern_brocot_word_matrices,
)


class AllRealPressureHelpersTest(unittest.TestCase):
    def test_prime_support_inverse_and_projective_saddle_scaling(self) -> None:
        inverse = prime_support_inverse_h(2, 1.0)
        self.assertAlmostEqual(inverse, 1.0 - 1.0 / math.sqrt(2.0), places=14)

        tau_unit, point_unit = prime_support_saddle((2, 3), (1.0, 1.0))
        tau_half, point_half = prime_support_saddle((2, 3), (0.5, 0.5))
        self.assertAlmostEqual(tau_half, 2.0 * tau_unit, places=13)
        for left, right in zip(point_unit, point_half):
            self.assertAlmostEqual(left, right, places=14)

    def test_prime_support_local_scale_matches_exact_diagonal_coefficients(
        self,
    ) -> None:
        audit = prime_support_local_asymptotic_audit(80)
        self.assertLess(abs(audit["corrected_ratio"] - 1.0), 0.01)
        self.assertGreater(audit["oracle_ratio"], 1.9)
        self.assertLess(audit["inverse_counterexample"], 0.5)
        self.assertGreater(audit["oracle_inverse"], 0.5)

    def test_single_layer_orbit_counter_recovers_partition_spectrum(self) -> None:
        self.assertTrue(hasattr(verification, "single_layer_orbit_counter"))
        fibonacci = [0, 1]
        for _ in range(18):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        generators = verification.weighted_generator_counters(16)
        partition_values = verification.ordinary_partition_values(
            fibonacci[18], fibonacci[2:18]
        )
        for layer in range(4, 16):
            predicted = verification.single_layer_orbit_counter(layer, generators)
            direct = verification.Counter(
                partition_values[
                    fibonacci[layer + 1] - 1 : fibonacci[layer + 2] - 1
                ]
            )
            self.assertEqual(predicted, direct)

    def test_critical_single_layer_renewal_matches_direct_partition_sum(self) -> None:
        self.assertTrue(hasattr(verification, "critical_single_layer_partition"))
        sigma = 2.4787507857339603
        generators = verification.weighted_generator_counters(17)
        renewal = verification.critical_renewal_coefficients(generators, sigma)
        fibonacci = [0, 1]
        for _ in range(20):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        partition_values = verification.ordinary_partition_values(
            fibonacci[19], fibonacci[2:19]
        )
        for layer in range(1, 17):
            predicted = verification.critical_single_layer_partition(layer, renewal)
            direct = sum(
                value ** (-sigma)
                for value in partition_values[
                    fibonacci[layer + 1] - 1 : fibonacci[layer + 2] - 1
                ]
            )
            self.assertAlmostEqual(predicted, direct, places=11)

    def test_finite_prime_support_interface_and_heavy_cost_obstruction(self) -> None:
        self.assertTrue(
            hasattr(verification, "prime_support_generator_cost_counter")
        )
        self.assertTrue(hasattr(verification, "heavy_dyadic_second_moment_terms"))

        dyadic = verification.prime_support_generator_cost_counter((2,), (6,))
        self.assertEqual(dyadic, verification.dyadic_generator_cost_counters(6)[6])

        mixed = verification.prime_support_generator_cost_counter((2, 3), (1, 1))
        self.assertEqual(sum(mixed.values()), 6)

        terms = verification.heavy_dyadic_second_moment_terms(20)
        self.assertEqual(len(terms), 20)
        self.assertTrue(all(right > left for left, right in zip(terms[2:], terms[3:])))
        self.assertGreater(terms[-1], 1000.0)

    def test_critical_window_renewal_matches_direct_partition_sum(self) -> None:
        self.assertTrue(hasattr(verification, "critical_renewal_coefficients"))
        self.assertTrue(hasattr(verification, "critical_window_partition"))
        sigma = 2.4787507857339603
        generators = verification.weighted_generator_counters(17)
        renewal = verification.critical_renewal_coefficients(generators, sigma)

        fibonacci = [0, 1]
        for _ in range(20):
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        coefficients = [1]
        for m in range(1, 17):
            coefficients = verification.extend_coefficients(coefficients, fibonacci[m])
            predicted = verification.critical_window_partition(m, renewal)
            direct = sum(level ** (-sigma) for level in coefficients)
            self.assertAlmostEqual(predicted, direct, places=11)

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
            self.assertEqual(
                sorted(denominators),
                sorted(
                    sum(matrix)
                    for matrix in stern_brocot_word_matrices(depth - 1)[-1]
                ),
            )

    def test_stern_brocot_matrix_bridge_inequalities(self) -> None:
        checks, failures = matrix_bridge_audit(5)
        self.assertGreater(checks, 0)
        self.assertEqual(failures, 0)

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
