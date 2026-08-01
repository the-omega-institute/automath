#!/usr/bin/env python3
"""Regression tests for the full quadratic-Pisot threshold verifier."""

from itertools import product
import unittest

from verify_quadratic_pisot_threshold import (
    QuadraticPisot,
    block_language_profile,
    classify_minimal_polynomial,
    predicted_threshold,
)


class QuadraticPisotThresholdTests(unittest.TestCase):
    def test_minimal_polynomial_classification_covers_both_conjugate_signs(self):
        self.assertEqual(classify_minimal_polynomial(1, -1), QuadraticPisot("negative", 1, 1))
        self.assertEqual(classify_minimal_polynomial(5, -3), QuadraticPisot("negative", 5, 3))
        self.assertEqual(classify_minimal_polynomial(3, 1), QuadraticPisot("positive", 3, 1))
        self.assertEqual(classify_minimal_polynomial(7, 4), QuadraticPisot("positive", 7, 4))
        with self.assertRaises(ValueError):
            classify_minimal_polynomial(4, 3)

    def test_parry_language_rank_is_a_consecutive_interval(self):
        cases = (
            QuadraticPisot("negative", 4, 3),
            QuadraticPisot("positive", 7, 4),
        )
        for beta in cases:
            for m in range(1, 6):
                values = [
                    beta.value(word)
                    for word in product(range(beta.alphabet_size), repeat=m)
                    if beta.is_legal(word)
                ]
                self.assertEqual(sorted(values), list(range(beta.q(m))))

    def test_exact_threshold_loci(self):
        for a in range(1, 7):
            for b in range(1, a + 1):
                beta = QuadraticPisot("negative", a, b)
                self.assertEqual(predicted_threshold(beta), 3 if a == b else 2)
        for a in range(3, 9):
            for b in range(1, a - 1):
                beta = QuadraticPisot("positive", a, b)
                self.assertEqual(predicted_threshold(beta), 3 if b == 1 else 2)

    def test_block_counts_detect_only_the_predicted_two_window_obstructions(self):
        cases = (
            QuadraticPisot("negative", 1, 1),
            QuadraticPisot("negative", 4, 4),
            QuadraticPisot("negative", 5, 3),
            QuadraticPisot("positive", 3, 1),
            QuadraticPisot("positive", 7, 1),
            QuadraticPisot("positive", 7, 4),
        )
        for beta in cases:
            for m in (2, 3, 4):
                got, raw, collision = block_language_profile(beta, m, m)
                self.assertEqual(collision, m < predicted_threshold(beta))
                self.assertEqual(got, raw - 1 if collision else raw)


if __name__ == "__main__":
    unittest.main()
