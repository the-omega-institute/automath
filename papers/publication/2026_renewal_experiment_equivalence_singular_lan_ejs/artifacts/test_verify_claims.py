import math
import unittest

import verify_claims as verify


class RenewalCollisionChecks(unittest.TestCase):
    def test_all_report_checks_pass(self):
        self.assertTrue(all(ok for _, ok, _ in verify.checks()))

    def test_report_count(self):
        self.assertEqual(len(verify.checks()), 14)

    def test_report_summary(self):
        self.assertIn("Summary: 14/14 checks passed", verify.render())

    def test_unequal_tail_at_zero(self):
        self.assertAlmostEqual(verify.tail_two_rate(0, 0.8, 1.6, 0.5), 1.0)

    def test_equal_tail_at_zero(self):
        self.assertAlmostEqual(verify.tail_two_rate(0, 1.2, 1.2, 0.5), 1.0)

    def test_equal_tail_formula(self):
        expected = (1 + 1.2) * math.exp(-1.2)
        self.assertAlmostEqual(verify.tail_two_rate(2, 1.2, 1.2, 0.5), expected)

    def test_unequal_tail_positive(self):
        self.assertGreater(verify.tail_two_rate(10, 0.8, 1.6, 0.5), 0.0)

    def test_unequal_tail_decreasing(self):
        values = [verify.tail_two_rate(k, 0.8, 1.6, 0.5) for k in range(10)]
        self.assertTrue(all(a > b for a, b in zip(values, values[1:])))

    def test_simple_recurrence(self):
        dt = 0.5
        values = [verify.tail_two_rate(k, 0.8, 1.6, dt) for k in range(10)]
        roots = [math.exp(-0.8 * dt), math.exp(-1.6 * dt)]
        self.assertLess(verify.recurrence_residual(values, roots), 1e-13)

    def test_double_recurrence(self):
        dt = 0.5
        values = [verify.tail_two_rate(k, 1.2, 1.2, dt) for k in range(10)]
        root = math.exp(-1.2 * dt)
        self.assertLess(verify.recurrence_residual(values, [root, root]), 1e-13)

    def test_recurrence_requires_two_roots(self):
        with self.assertRaises(ValueError):
            verify.recurrence_residual([1.0, 0.5, 0.25], [0.5])

    def test_matching_scale(self):
        v0, n = 4.0, 10_000
        self.assertAlmostEqual(math.sqrt(v0) * n ** (-0.25), 0.2)

    def test_projection_nonexpansive_positive(self):
        x, y = -0.03, 0.04
        self.assertLessEqual(abs(max(x, 0.0) - y), abs(x - y))

    def test_square_root_inequality(self):
        x, y = 0.01, 0.04
        self.assertLessEqual(abs(math.sqrt(x) - math.sqrt(y)), math.sqrt(abs(x - y)))

    def test_gamma_range(self):
        gamma = 0.75
        self.assertTrue(0.5 < gamma < 1.0)

    def test_calendar_information_scale(self):
        palm_information, mean = 3.0, 2.5
        self.assertAlmostEqual(palm_information / mean, 1.2)

    def test_multiple_pole_identity(self):
        for multiplicity in range(3, 8):
            self.assertAlmostEqual(
                verify.multiple_rho_derivative(multiplicity, 1.4, 0.9),
                verify.multiple_rho_derivative_unsimplified(
                    multiplicity, 1.4, 0.9
                ),
            )

    def test_wrong_multiple_pole_order_is_rejected(self):
        multiplicity, centre, s = 4, 1.4, 0.9
        correct = verify.multiple_rho_derivative(multiplicity, centre, s)
        wrong = centre ** (multiplicity - 2) * (s + 2.0 * centre) / (
            s + centre
        ) ** (multiplicity + 1)
        self.assertNotAlmostEqual(correct, wrong)

    def test_equal_dispersion_shapes_are_not_permutations(self):
        r = 0.6
        first = (r, -r, 0.0)
        second = (
            r / math.sqrt(3.0),
            r / math.sqrt(3.0),
            -2.0 * r / math.sqrt(3.0),
        )
        self.assertAlmostEqual(
            verify.cluster_dispersion(first), verify.cluster_dispersion(second)
        )
        self.assertNotEqual(sorted(first), sorted(second))

    def test_perturbed_shape_breaks_equal_dispersion(self):
        r = 0.6
        first = (r, -r, 0.0)
        perturbed = (
            r / math.sqrt(3.0),
            r / math.sqrt(3.0),
            -2.1 * r / math.sqrt(3.0),
        )
        self.assertNotAlmostEqual(
            verify.cluster_dispersion(first),
            verify.cluster_dispersion(perturbed),
        )


if __name__ == "__main__":
    unittest.main()
