#!/usr/bin/env python3
"""Regression tests for the simple-Parry causal-obstruction verifier."""

import unittest

import numpy as np

from verify_simple_parry_causal import (
    bad_blocks,
    bounded_multiple_order,
    collision_graph_bad_path_count,
    gamma_claims,
    p_bonacci_claims,
    periodic_collision,
    q_sequence,
    rank_is_consecutive,
)


class SimpleParryCausalTests(unittest.TestCase):
    def test_simple_parry_count_recurrences(self):
        self.assertEqual(q_sequence((1, 1, 1), 6), [1, 2, 4, 7, 13, 24, 44])
        self.assertEqual(q_sequence((1, 0, 1), 6), [1, 2, 3, 4, 6, 9, 13])

    def test_companion_polynomial_has_minimal_bounded_multiple_order(self):
        for digits in ((1, 1, 1), (1, 0, 1), (2, 1), (2, 0, 2)):
            self.assertEqual(bounded_multiple_order(digits), len(digits))

    def test_colex_rank_is_consecutive_on_simple_parry_languages(self):
        for digits in ((1, 1, 1), (1, 0, 1), (2, 1), (2, 2), (2, 0, 1)):
            for m in range(1, 7):
                self.assertTrue(rank_is_consecutive(digits, m))

    def test_collision_graph_paths_equal_toeplitz_bad_blocks(self):
        for digits, m in (((1, 1, 1), 4), ((1, 0, 1), 4), ((2, 1), 3)):
            for output_length in range(1, 5):
                self.assertEqual(
                    collision_graph_bad_path_count(digits, m, output_length),
                    len(bad_blocks(digits, m, output_length)),
                )

    def test_p_bonacci_family_has_causal_length_two(self):
        for p in range(3, 9):
            result = p_bonacci_claims(p)
            self.assertEqual(result["q_p"], 2**p - 1)
            self.assertEqual(result["q_p1"], 2 ** (p + 1) - 3)
            self.assertEqual(result["one_output_bad"], 2)
            self.assertEqual(result["two_output_bad"], 0)

    def test_p_bonacci_roots_are_pisot_and_have_the_claimed_real_sign_parity(self):
        for p in range(3, 13):
            roots = np.roots([1] + [-1] * p)
            dominant = roots[np.argmax(np.abs(roots))]
            self.assertAlmostEqual(dominant.imag, 0.0, places=9)
            self.assertGreater(dominant.real, 1.0)
            self.assertTrue(all(abs(root) < 1.0 + 1e-9 for root in roots if root != dominant))
            negative_real = [root.real for root in roots if abs(root.imag) < 1e-8 and root.real < 0]
            self.assertEqual(bool(negative_real), p % 2 == 0)

    def test_gamma_has_exact_causal_length_four_at_aperture_four(self):
        result = gamma_claims()
        self.assertEqual(result["counts"], [12, 4, 2, 0])
        self.assertEqual(result["positive_representatives"], [6, 2, 1, 0])

    def test_gamma_aperture_two_has_a_constant_collision(self):
        self.assertTrue(periodic_collision((1, 0, 1), 2, (1,)))

    def test_gamma_aperture_three_has_a_period_four_collision(self):
        self.assertTrue(periodic_collision((1, 0, 1), 3, (1, -1, -1, 1)))

    def test_gamma_root_geometry_is_pisot(self):
        roots = np.roots([1, -1, 0, -1])
        gamma = roots[np.argmax(np.abs(roots))]
        conjugates = [root for root in roots if root != gamma]
        self.assertAlmostEqual(gamma.imag, 0.0, places=10)
        self.assertGreater(gamma.real, 1.0)
        for root in conjugates:
            self.assertAlmostEqual(abs(root), gamma.real ** -0.5, places=10)
            self.assertLess(abs(root), 1.0)

    def test_gamma_three_output_witness_dies_at_fourth_window(self):
        witness = (1, -1, 1, 1, -1, 0)
        self.assertIn(witness, bad_blocks((1, 0, 1), 4, 3))
        self.assertFalse(
            any(block[: len(witness)] == witness for block in bad_blocks((1, 0, 1), 4, 4))
        )


if __name__ == "__main__":
    unittest.main()
