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
