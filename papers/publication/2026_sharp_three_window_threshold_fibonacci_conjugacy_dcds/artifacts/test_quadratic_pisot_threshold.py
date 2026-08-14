#!/usr/bin/env python3
"""Regression tests for the full quadratic-Pisot threshold verifier."""

from itertools import product
import unittest

from verify_quadratic_pisot_threshold import (
    QuadraticPisot,
    block_language_profile,
    causal_first_digit_is_determined,
    classify_minimal_polynomial,
    critical_periodic_fiber_histogram,
    minimum_injective_output_length,
    predicted_threshold,
    separation_proof_obligations,
    nearest_multiple_separation,
    residue_table,
)


class QuadraticPisotThresholdTests(unittest.TestCase):
    def test_nearest_multiple_proof_obligations_in_both_chambers(self):
        for a in range(1, 40):
            for b in range(1, a + 1):
                self.assertTrue(
                    separation_proof_obligations(
                        QuadraticPisot("negative", a, b)
                    )
                )

        for a in range(3, 40):
            for b in range(1, a - 1):
                self.assertTrue(
                    separation_proof_obligations(
                        QuadraticPisot("positive", a, b)
                    )
                )

    def test_nearest_multiple_separation_in_both_parameter_chambers(self):
        for a in range(1, 16):
            for b in range(1, a + 1):
                beta = QuadraticPisot("negative", a, b)
                for r in range(4, 11):
                    for e in range(1, a + 1):
                        distance, lower_bound = nearest_multiple_separation(beta, r, e)
                        self.assertGreaterEqual(distance, lower_bound)

        for a in range(3, 16):
            for b in range(1, a - 1):
                beta = QuadraticPisot("positive", a, b)
                for r in range(4, 11):
                    for e in range(1, a):
                        distance, lower_bound = nearest_multiple_separation(beta, r, e)
                        self.assertGreaterEqual(distance, lower_bound)

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

    def test_aperture_two_duality_and_exact_aperture_three_separation(self):
        for q in range(3, 8):
            for kappa in range(2, q):
                negative = QuadraticPisot("negative", q - 1, kappa)
                positive = QuadraticPisot("positive", q, q - kappa)
                self.assertEqual(residue_table(negative, 2), residue_table(positive, 2))

                negative_words = {
                    word
                    for word in product(range(q), repeat=3)
                    if negative.is_legal(word)
                }
                positive_words = {
                    word
                    for word in product(range(q), repeat=3)
                    if positive.is_legal(word)
                }
                expected_difference = {
                    (high, kappa - 1, q - 1)
                    for high in range(kappa, q)
                }
                self.assertEqual(negative_words - positive_words, expected_difference)
                self.assertFalse(positive_words - negative_words)
                self.assertEqual(negative.q(3) - positive.q(3), q - kappa)

    def test_optimal_causal_decoder_lengths_are_two_and_three(self):
        cases = (
            QuadraticPisot("negative", 1, 1),
            QuadraticPisot("negative", 4, 3),
            QuadraticPisot("positive", 3, 1),
            QuadraticPisot("positive", 5, 2),
        )
        for beta in cases:
            expected = 2 if beta.conjugate_sign == "negative" else 3
            for m in range(3, 6):
                self.assertFalse(causal_first_digit_is_determined(beta, m, expected - 1))
                self.assertTrue(causal_first_digit_is_determined(beta, m, expected))

    def test_critical_extremal_map_has_one_double_periodic_fiber(self):
        extremals = (
            QuadraticPisot("negative", 1, 1),
            QuadraticPisot("negative", 3, 3),
            QuadraticPisot("positive", 4, 1),
        )
        for beta in extremals:
            for period in range(1, 6):
                histogram = critical_periodic_fiber_histogram(beta, period)
                self.assertEqual(histogram.get(2), 1)
                singleton_fibers = beta.alphabet_size**period - 2
                self.assertEqual(histogram.get(1, 0), singleton_fibers)
                self.assertEqual(set(histogram), {2} if singleton_fibers == 0 else {1, 2})

    def test_finite_block_injectivity_begins_exactly_at_the_aperture(self):
        cases = (
            QuadraticPisot("negative", 2, 1),
            QuadraticPisot("negative", 3, 3),
            QuadraticPisot("positive", 4, 1),
            QuadraticPisot("positive", 4, 2),
        )
        for beta in cases:
            for m in range(predicted_threshold(beta), 6):
                self.assertEqual(minimum_injective_output_length(beta, m), m)


if __name__ == "__main__":
    unittest.main()
