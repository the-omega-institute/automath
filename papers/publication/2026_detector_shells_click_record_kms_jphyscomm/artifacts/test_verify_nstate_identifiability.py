import unittest

import numpy as np

from artifacts import verify_nstate_identifiability as verify


class SerialKilledLeakageTests(unittest.TestCase):
    def test_two_state_physical_fibre_endpoints_are_rate_swaps(self):
        gamma = 0.7
        recovery = 1.6
        delta = 0.8
        lower, upper = verify.sampled_counter_fibre_interval(gamma, recovery)
        endpoint_kernels = (
            verify.sampled_counter_fibre_kernel(gamma, recovery, delta, lower),
            verify.sampled_counter_fibre_kernel(gamma, recovery, delta, upper),
        )
        physical_endpoints = (
            verify.sampled_counter_killed_kernel(gamma, recovery, delta),
            verify.sampled_counter_killed_kernel(recovery, gamma, delta),
        )
        for expected in physical_endpoints:
            self.assertTrue(
                any(
                    np.allclose(actual, expected, atol=2e-13)
                    for actual in endpoint_kernels
                )
            )

    def test_two_state_physical_fibre_interior_is_positive_and_visible_equivalent(
        self,
    ):
        gamma = 2.1
        recovery = 0.9
        delta = 0.6
        lower, upper = verify.sampled_counter_fibre_interval(gamma, recovery)
        q = 0.35 * lower + 0.65 * upper
        baseline = verify.sampled_counter_killed_kernel(gamma, recovery, delta)
        interior = verify.sampled_counter_fibre_kernel(gamma, recovery, delta, q)
        self.assertGreater(float(interior.min()), 0.0)
        deficits = np.ones(2) - interior @ np.ones(2)
        self.assertGreater(float(deficits.min()), 0.0)
        np.testing.assert_allclose(
            verify.kernel_tail_coordinates(interior, 30),
            verify.kernel_tail_coordinates(baseline, 30),
            rtol=2e-12,
            atol=2e-13,
        )

    def test_two_state_physical_fibre_collapses_exactly_on_exchange_diagonal(
        self,
    ):
        lower, upper = verify.sampled_counter_fibre_interval(1.3, 1.3)
        self.assertEqual(lower, 1.0)
        self.assertEqual(upper, 1.0)
        with self.assertRaises(ValueError):
            verify.sampled_counter_fibre_kernel(1.3, 1.3, 0.7, 1.0 + 1e-5)

    def test_two_state_physical_fibre_rejects_points_beyond_exact_arc(self):
        gamma = 0.7
        recovery = 1.6
        lower, upper = verify.sampled_counter_fibre_interval(gamma, recovery)
        with self.assertRaises(ValueError):
            verify.sampled_counter_fibre_kernel(gamma, recovery, 1.0, lower - 1e-6)
        with self.assertRaises(ValueError):
            verify.sampled_counter_fibre_kernel(gamma, recovery, 1.0, upper + 1e-6)

    def test_exact_three_inclusion_image_equation(self):
        examples = (
            (0.35, 0.8, 0.2),
            (0.7, 1.6, 1.0),
            (2.0, 2.0, 1.0),
            (4.0, 0.45, 0.7),
        )
        for gamma, recovery, delta in examples:
            inclusions = verify.two_state_inclusion_coordinates(
                gamma, recovery, delta
            )
            residual = verify.physical_image_residual(inclusions)
            self.assertLess(abs(residual), 2e-12)

    def test_physical_image_equation_detects_intensity_perturbation(self):
        inclusions = verify.two_state_inclusion_coordinates(0.7, 1.6, 1.0)
        perturbed = inclusions.copy()
        perturbed[0] *= 1.01
        self.assertGreater(abs(verify.physical_image_residual(perturbed)), 1e-4)

    def test_hidden_mode_obeys_sharp_global_bound(self):
        grid = np.geomspace(1e-4, 50.0, 181)
        values = np.array(
            [verify.hidden_mode_secant(x, y) for x in grid for y in grid]
        )
        self.assertGreaterEqual(float(values.min()), -np.exp(-2.0) - 2e-14)
        self.assertLess(float(values.max()), 1.0)
        self.assertAlmostEqual(
            verify.hidden_mode_secant(2.0, 2.0), -np.exp(-2.0), places=15
        )

    def test_small_sampling_interval_mean_expansion_has_sixth_order_remainder(self):
        gamma = 0.7
        recovery = 1.6
        normalized_errors = []
        for delta in (0.2, 0.1, 0.05):
            exact = delta * verify.mean_cycle_length(gamma, recovery, delta)
            approximation = verify.small_delta_mean_expansion(
                gamma, recovery, delta
            )
            normalized_errors.append(abs(exact - approximation) / delta**6)
        self.assertLess(max(normalized_errors), 2e-3)

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
