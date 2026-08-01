import unittest

import numpy as np

from artifacts import verify_nstate_identifiability as verify


class SerialKilledLeakageTests(unittest.TestCase):
    def test_kernels_are_stochastic_and_clicks_reset(self):
        for rates in ((0.7, 1.6), (0.7, 1.2, 2.3)):
            t0, t1 = verify.serial_killed_reset_kernels(rates)
            np.testing.assert_allclose((t0 + t1).sum(axis=1), 1.0, atol=1e-13)
            self.assertGreaterEqual(float(t0.min()), -1e-14)
            self.assertGreaterEqual(float(t1.min()), -1e-14)
            self.assertTrue(np.allclose(t1[:, :-1], 0.0, atol=1e-14))

    def test_hankel_pencil_recovers_unordered_sampled_poles(self):
        for rates in ((0.7, 1.6), (0.7, 1.2, 2.3)):
            tails = verify.visible_tail_coordinates(rates, 2 * len(rates))
            recovered = verify.recover_sampled_poles(tails, len(rates))
            expected = np.sort(np.exp(-np.asarray(rates)))
            np.testing.assert_allclose(recovered, expected, rtol=1e-9, atol=1e-11)

    def test_confluent_recurrence_recovers_collision_multiplicities(self):
        examples = (
            (0.7, 0.7),
            (0.7, 1.2, 1.2),
            (0.7, 1.2, 1.2, 2.3),
        )
        for rates in examples:
            tails = verify.visible_tail_coordinates(rates, 3 * len(rates) + 1)
            polynomial, residual = verify.recover_minimal_recurrence(
                tails, len(rates)
            )
            expected = np.poly(np.exp(-np.asarray(rates, dtype=float)))
            np.testing.assert_allclose(
                polynomial, expected, rtol=2e-8, atol=2e-10
            )
            self.assertLess(residual, 2e-12)

    def test_collision_does_not_lower_serial_hankel_rank(self):
        examples = ((0.7, 0.7), (0.7, 1.2, 1.2), (0.7, 0.7, 2.3, 2.3))
        for rates in examples:
            tails = verify.visible_tail_coordinates(rates, 2 * len(rates))
            diagnostics = verify.hankel_diagnostics(tails, len(rates))
            self.assertEqual(diagnostics.rank, len(rates))
            self.assertGreater(diagnostics.smallest_singular_value, 1e-8)

    def test_visible_moments_are_permutation_invariant(self):
        rates = (0.45, 0.95, 1.8)
        baseline = verify.visible_click_moments(rates, 7)
        permuted = verify.visible_click_moments((1.8, 0.45, 0.95), 7)
        np.testing.assert_allclose(permuted, baseline, rtol=1e-12, atol=1e-13)

    def test_stochastic_similarity_changes_kernel_not_visible_law(self):
        examples = ((0.7, 1.6), (0.7, 1.2, 2.3), (0.7, 1.2, 1.2, 2.3))
        for rates in examples:
            t0, _ = verify.serial_killed_reset_kernels(rates)
            transformed = verify.equivalent_killed_reset_kernel(t0, epsilon=0.02)
            self.assertGreater(np.linalg.norm(transformed - t0), 1e-4)
            self.assertGreaterEqual(float(transformed.min()), -1e-13)
            base = verify.kernel_tail_coordinates(t0, 25)
            equivalent = verify.kernel_tail_coordinates(transformed, 25)
            np.testing.assert_allclose(equivalent, base, rtol=1e-11, atol=1e-12)

    def test_reset_preserving_similarity_tangent_has_expected_dimension(self):
        for n_states in (2, 3, 4):
            basis = verify.reset_similarity_lie_basis(n_states)
            self.assertEqual(len(basis), (n_states - 1) ** 2)
            reset = np.zeros(n_states)
            reset[-1] = 1.0
            for tangent in basis:
                np.testing.assert_allclose(tangent @ np.ones(n_states), 0.0)
                np.testing.assert_allclose(reset @ tangent, 0.0)


if __name__ == "__main__":
    unittest.main()
