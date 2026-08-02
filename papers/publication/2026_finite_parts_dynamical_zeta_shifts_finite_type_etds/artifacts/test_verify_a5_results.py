import unittest

import sympy as sp

from artifacts.verify_a5_results import (
    quotient_correction_coefficients,
    render_report,
    universal_product_jet,
    verify_c2_regular_cover_factorization,
)


class OracleA5ResultTests(unittest.TestCase):
    def test_quotient_correction_matches_primitive_orbit_expansion(self):
        periodic_minus_fixed, split_orbit_product = (
            quotient_correction_coefficients(max_degree=16)
        )

        self.assertEqual(periodic_minus_fixed, split_orbit_product)
        self.assertGreater(sum(periodic_minus_fixed.values()), 0)

    def test_regular_cover_determinant_has_the_artin_factorization(self):
        self.assertTrue(verify_c2_regular_cover_factorization())

    def test_universal_harmonic_jet_has_the_claimed_coefficients(self):
        alpha = sp.Symbol("alpha")
        x = sp.Symbol("x")

        self.assertEqual(
            universal_product_jet(alpha, order=3),
            sp.expand(
            1
            - alpha * x / 2
            + alpha * (3 * alpha + 2) * x**2 / 24
            - alpha**2 * (alpha + 2) * x**3 / 48,
            ),
        )

    def test_report_records_a_clean_exact_verification(self):
        self.assertTrue(render_report().rstrip().endswith("STATUS: PASS"))


if __name__ == "__main__":
    unittest.main()
