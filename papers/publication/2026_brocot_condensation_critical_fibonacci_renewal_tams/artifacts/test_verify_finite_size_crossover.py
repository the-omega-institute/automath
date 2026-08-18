#!/usr/bin/env python3
"""Tests for the direct finite-size crossover calculation."""

from __future__ import annotations

import itertools
import unittest

import numpy as np

from verify_finite_size_crossover import (
    crossover_limit,
    fibonacci_numbers,
    layer_histogram,
    representation_counts,
    wrong_prefactor_limit,
)


class FibonacciPartitionDynamicProgramTest(unittest.TestCase):
    def test_counts_match_brute_force_subset_enumeration(self) -> None:
        maximum = 20
        observed = representation_counts(maximum)
        parts = [1, 2, 3, 5, 8, 13]
        expected = np.zeros(maximum + 1, dtype=np.int64)
        for choices in itertools.product((0, 1), repeat=len(parts)):
            value = sum(choice * part for choice, part in zip(choices, parts))
            if value <= maximum:
                expected[value] += 1
        np.testing.assert_array_equal(observed, expected)

    def test_layer_histogram_has_the_exact_raw_layer_count(self) -> None:
        fibonacci = fibonacci_numbers(7)
        counts = representation_counts(fibonacci[7] - 2)
        lower, upper, histogram = layer_histogram(counts, fibonacci, m=5)
        self.assertEqual((lower, upper), (7, 12))
        self.assertEqual(sum(histogram.values()), fibonacci[5])
        self.assertEqual(histogram, {1: 1, 2: 2, 3: 2})


class CrossoverNormalizationTest(unittest.TestCase):
    def test_theta_zero_is_the_continuous_value(self) -> None:
        mu_c = 21.75
        self.assertAlmostEqual(crossover_limit(0.0, mu_c), 2.0 / mu_c)
        self.assertAlmostEqual(crossover_limit(1.0e-9, mu_c), 2.0 / mu_c)

    def test_literal_wrong_prefactor_is_four_times_too_small(self) -> None:
        for theta in (-4.0, 0.0, 4.0):
            correct = crossover_limit(theta, 21.75)
            self.assertAlmostEqual(wrong_prefactor_limit(theta, 21.75), correct / 4.0)


if __name__ == "__main__":
    unittest.main()
