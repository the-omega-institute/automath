#!/usr/bin/env python3
"""Regression tests for the simple-Parry causal-obstruction verifier."""

import unittest

import numpy as np

from verify_simple_parry_causal import (
    aperture_two_claims,
    bad_blocks,
    bounded_multiple_order,
    collision_graph_analysis,
    collision_graph_bad_path_count,
    cubic_family_claims,
    cubic_family_digits,
    cubic_family_extremal_vector,
    cubic_family_q_sequence,
    gamma_claims,
    non_pisot_simple_parry_claims,
    p_bonacci_claims,
    periodic_collision,
    q_sequence,
    rank_is_consecutive,
)


class SimpleParryCausalTests(unittest.TestCase):
    def test_collision_theorems_do_not_require_the_pisot_hypothesis(self):
        result = non_pisot_simple_parry_claims()
        self.assertEqual(result["digits"], (2, 0, 0, 2))
        self.assertTrue(result["parry_admissible"])
        self.assertFalse(result["is_pisot"])
        self.assertGreater(result["largest_nondominant_modulus"], 1.0)
        self.assertEqual(result["q_prefix"], [1, 3, 7, 15, 32, 70, 154])
        self.assertTrue(all(result["rank_checks"]))
        self.assertEqual(result["aperture_two_causal_length"], 2)

    def test_cubic_family_has_the_claimed_parry_word_and_factorization(self):
        for n in range(4, 13):
            result = cubic_family_claims(n)
            self.assertEqual(len(cubic_family_digits(n)), 2 * n + 2)
            self.assertTrue(result["parry_factorization"])
            self.assertTrue(result["proper_suffixes_are_smaller"])

    def test_cubic_family_count_recurrence_and_extremal_paths(self):
        for n in range(4, 13):
            q = cubic_family_q_sequence(n, n - 1)
            self.assertEqual(q[:3], [1, n + 1, n * n + n + 2])
            for r in range(3, n):
                self.assertEqual(
                    q[r],
                    (n + 2) * q[r - 1] - 2 * n * q[r - 2] + n * q[r - 3],
                )
            for r in range(2, n):
                witness = cubic_family_extremal_vector(n, r)
                self.assertEqual(len(witness), 2 * r - 2)
                weighted = [
                    sum(q[j] * witness[t + j] for j in range(r))
                    for t in range(r - 1)
                ]
                expected = [q[r]] if r == 2 else [-q[r]] + [0] * (r - 2)
                self.assertEqual(weighted, expected)
                self.assertTrue(all(-n <= entry <= n for entry in witness))

    def test_cubic_family_has_unbounded_exact_causal_lengths(self):
        for n in range(4, 7):
            digits = cubic_family_digits(n)
            m = n - 1
            result = collision_graph_analysis(digits, m)
            self.assertTrue(result["injective"])
            self.assertEqual(result["causal_length"], n - 1)
            self.assertIsNone(result["periodic_witness"])

    def test_cubic_family_terminal_path_counts_match_the_classification(self):
        for n in range(4, 7):
            digits = cubic_family_digits(n)
            for r in range(2, n):
                self.assertEqual(
                    collision_graph_bad_path_count(digits, r, r - 1), 2
                )
                self.assertEqual(collision_graph_bad_path_count(digits, r, r), 0)

    def test_injective_folds_have_finite_causal_length_within_state_bound(self):
        for digits, m, expected_length in (
            ((1, 1, 1), 4, 2),
            ((1, 0, 1), 4, 4),
            ((2, 1), 2, 2),
            ((2, 0, 1), 2, 2),
        ):
            result = collision_graph_analysis(digits, m)
            self.assertTrue(result["injective"])
            self.assertEqual(result["causal_length"], expected_length)
            self.assertLessEqual(result["causal_length"], result["state_bound"])
            self.assertTrue(result["zero_predecessor_is_unique"])
            self.assertIsNone(result["periodic_witness"])

    def test_noninjectivity_has_a_bounded_periodic_collision_witness(self):
        for digits, m in (((1, 0, 1), 3), ((2, 2), 2)):
            result = collision_graph_analysis(digits, m)
            witness = result["periodic_witness"]
            self.assertFalse(result["injective"])
            self.assertIsNone(result["causal_length"])
            self.assertIsNotNone(witness)
            self.assertLessEqual(len(witness), result["state_bound"])
            self.assertTrue(periodic_collision(digits, m, witness))

    def test_aperture_two_has_exact_three_regime_classification(self):
        local = aperture_two_claims((1, 1, 1))
        self.assertEqual(local["boundary_parameter"], 2)
        self.assertEqual(local["regime"], "local_bijection")
        self.assertEqual(local["causal_length"], 1)

        causal = aperture_two_claims((2, 0, 1))
        self.assertEqual(causal["boundary_parameter"], 1)
        self.assertEqual(causal["regime"], "two_output_inverse")
        self.assertEqual(causal["causal_length"], 2)

        branch = aperture_two_claims((1, 0, 1))
        self.assertEqual(branch["boundary_parameter"], 1)
        self.assertEqual(branch["regime"], "constant_branch_pair")
        self.assertIsNone(branch["causal_length"])
        self.assertEqual(branch["periodic_witness"], (1,))

    def test_quadratic_aperture_two_cases_are_recovered(self):
        self.assertEqual(aperture_two_claims((2, 1))["causal_length"], 2)
        critical = aperture_two_claims((2, 2))
        self.assertEqual(critical["regime"], "constant_branch_pair")
        self.assertEqual(critical["periodic_witness"], (2,))

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
