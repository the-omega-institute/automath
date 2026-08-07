import math
import unittest

import numpy as np

from artifacts import verify_A8_results as verify


class PhysicalImageTests(unittest.TestCase):
    def test_physical_parameter_grid_has_zero_image_residual(self):
        for x in np.geomspace(0.02, 8.0, 24):
            for y in np.geomspace(0.03, 9.0, 23):
                coordinates = verify.sampled_counter_inclusions(float(x), float(y))
                self.assertLess(abs(verify.physical_image_residual(coordinates)), 2e-12)

    def test_symmetric_log_divided_difference_is_regular_on_diagonal(self):
        for m in (0.15, 0.35, 0.5, 0.8):
            for d in (1e-2, 4e-3, 1e-3):
                exact = verify.symmetric_log_divided_difference(m + d, m - d)
                second_order = m * (1.0 - math.log(m)) + d**2 / m * (
                    0.5 + math.log(m) / 3.0
                )
                self.assertLess(abs(exact - second_order), 3.0 * d**4 / m**3)

    def test_analytic_extension_matches_real_root_formula(self):
        for p, s in ((0.12, 0.83), (0.35, 0.5), (0.6, 0.600001)):
            expected = verify.symmetric_log_divided_difference(p, s)
            actual = verify.analytic_log_divided_difference(p + s, p * s)
            self.assertAlmostEqual(actual, expected, places=11)

    def test_analytic_extension_is_real_on_nonreal_root_side(self):
        value = verify.analytic_log_divided_difference(1.0, 0.3)
        self.assertTrue(math.isfinite(value))

    def test_joint_constraint_jacobian_has_rank_two_on_grid(self):
        for x in np.geomspace(0.1, 5.0, 12):
            for y in np.geomspace(0.1, 5.5, 11):
                coordinates = verify.sampled_counter_inclusions(float(x), float(y))
                jacobian = verify.constraint_jacobian(coordinates)
                self.assertGreater(np.linalg.svd(jacobian, compute_uv=False)[-1], 1e-5)


class JointImageTestChecks(unittest.TestCase):
    def test_regenerative_covariance_and_constraint_covariance_are_positive(self):
        for x, y in ((0.1, 0.1), (0.2, 1.7), (1.0, 1.0), (2.0, 4.0), (5.0, 5.5)):
            coordinates, sigma_r = verify.regenerative_inclusion_covariance(x, y)
            jacobian = verify.constraint_jacobian(coordinates)
            omega = jacobian @ sigma_r @ jacobian.T
            self.assertGreater(np.linalg.eigvalsh(sigma_r)[0], 1e-8)
            self.assertGreater(np.linalg.eigvalsh(omega)[0], 1e-8)

    def test_cone_distance_matches_direct_scalar_minimization(self):
        rng = np.random.default_rng(20260803)
        for _ in range(200):
            matrix = rng.normal(size=(2, 2))
            omega = matrix @ matrix.T + 0.1 * np.eye(2)
            e, d = rng.normal(size=2)
            beta = omega[0, 1] / omega[0, 0]
            minimizer = max(0.0, d - beta * e)
            residual = np.array([e, d - minimizer])
            direct = residual @ np.linalg.inv(omega) @ residual
            self.assertAlmostEqual(
                verify.cone_wald_distance(e, d, omega), direct, places=11
            )

    def test_boundary_critical_value_matches_mixture_quantile(self):
        self.assertAlmostEqual(verify.boundary_critical_value(0.05), 5.1383807853, places=9)

    def test_finite_support_submodel_has_prescribed_coordinate_changes(self):
        directions = verify.local_gap_perturbation_basis()
        cycle_lengths = np.arange(1.0, 5.0)
        self.assertTrue(np.allclose(directions.sum(axis=1), 0.0))
        self.assertTrue(
            np.allclose(directions @ cycle_lengths, np.array([1.0, 0.0, 0.0]))
        )
        self.assertTrue(np.allclose(directions[:, 0], np.array([0.0, 1.0, 0.0])))
        self.assertTrue(np.allclose(directions[:, 1], np.array([0.0, 0.0, 1.0])))

    def test_local_power_is_size_at_origin_and_increases_nonreal_side(self):
        omega = np.array([[1.4, 0.3], [0.3, 1.1]])
        alpha = 0.05
        at_origin = verify.local_power(0.0, 0.0, omega, alpha)
        nonreal_side = verify.local_power(0.0, -1.0, omega, alpha)
        physical_side = verify.local_power(0.0, 1.0, omega, alpha)
        self.assertAlmostEqual(at_origin, alpha, places=8)
        self.assertGreater(nonreal_side, alpha)
        self.assertLess(physical_side, alpha)


class HiddenModeTests(unittest.TestCase):
    def test_sharp_global_spectral_bound_and_extremizer(self):
        lower = -math.exp(-2.0)
        self.assertAlmostEqual(verify.hidden_mode(2.0, 2.0), lower, places=14)
        for x in np.geomspace(1e-4, 40.0, 160):
            for y in np.geomspace(2e-4, 35.0, 80):
                value = verify.hidden_mode(float(x), float(y))
                self.assertGreaterEqual(value, lower - 2e-14)
                self.assertLess(value, 1.0)

    def test_oracle_one_dependence_equation_has_diagonal_counterexample(self):
        x = y = 2.0
        self.assertAlmostEqual(x * math.exp(-x), y * math.exp(-y), places=15)
        self.assertNotEqual(verify.hidden_mode(x, y), 0.0)


class CompleteVisibleLawTestChecks(unittest.TestCase):
    def test_markov_gap_alternative_is_stochastic_and_preserves_gap_marginal(self):
        for x in (0.35, 1.0, 2.4, 5.0):
            g, h, transition, _ = verify.markov_gap_alternative(x, 0.005)
            self.assertGreaterEqual(np.min(transition), 0.0)
            self.assertTrue(np.allclose(transition.sum(axis=1), 1.0, atol=2e-13))
            self.assertTrue(np.allclose(g @ transition, g, atol=2e-13))
            self.assertAlmostEqual(float(g @ h), 0.0, places=13)
            self.assertEqual(h[0], 0.0)

    def test_markov_gap_alternative_preserves_three_inclusions_but_changes_word_five(self):
        x = 1.35
        null = verify.markov_gap_alternative(x, 0.0)
        alternative = verify.markov_gap_alternative(x, 0.08)
        r_null = verify.markov_gap_inclusions(null[0], null[2], null[3])
        r_alternative = verify.markov_gap_inclusions(
            alternative[0], alternative[2], alternative[3]
        )
        self.assertTrue(np.allclose(r_null, r_alternative, atol=2e-13))

        g, _, transition, mu = alternative
        observed = g[1] * transition[1, 1] / mu
        expected = g[1] ** 2 * 1.08 / mu
        self.assertAlmostEqual(observed, expected, places=13)
        self.assertGreater(observed, null[0][1] * null[2][1, 1] / null[3])

    def test_markov_gap_information_matches_score_variance_per_calendar_time(self):
        for x in (0.35, 1.0, 2.4, 5.0):
            g, h, _, mu = verify.markov_gap_alternative(x, 0.0)
            information = verify.markov_gap_information(g, h, mu)
            second_moment = float(g @ (h * h))
            expected = second_moment**2 / mu
            self.assertAlmostEqual(information, expected, places=13)
            self.assertGreater(information, 0.0)

    def test_markov_gap_local_power_has_size_at_origin_and_is_strictly_increasing(self):
        alpha = 0.05
        powers = [verify.markov_gap_local_power(1.35, t, alpha) for t in (0.0, 0.5, 1.0)]
        self.assertAlmostEqual(powers[0], alpha, places=13)
        self.assertGreater(powers[1], powers[0])
        self.assertGreater(powers[2], powers[1])


class SamplingBiasTests(unittest.TestCase):
    def test_exact_rounded_cycle_mean_matches_gap_tail_sum(self):
        for gamma, kappa, delta in ((0.7, 1.9, 0.4), (1.3, 1.3, 0.2), (3.0, 0.6, 0.1)):
            exact = verify.rounded_cycle_mean(gamma, kappa, delta)
            tail_sum = verify.rounded_cycle_mean_from_tails(gamma, kappa, delta)
            self.assertAlmostEqual(exact, tail_sum, places=12)

    def test_fast_sampling_mean_has_universal_half_interval_term(self):
        gamma, kappa = 0.8, 2.1
        for delta in (0.08, 0.04, 0.02):
            scaled_mean = delta * verify.rounded_cycle_mean(gamma, kappa, delta)
            expansion = (
                1.0 / gamma
                + 1.0 / kappa
                + delta / 2.0
                + gamma * kappa * (gamma + kappa) * delta**4 / 720.0
            )
            self.assertLess(abs(scaled_mean - expansion), 2.0 * delta**6)


if __name__ == "__main__":
    unittest.main()
