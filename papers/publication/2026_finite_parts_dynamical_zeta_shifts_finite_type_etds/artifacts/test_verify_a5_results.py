import unittest

import sympy as sp

from artifacts import verify_a5_results as verifier
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

    def test_quotient_correction_agrees_on_an_interior_real_grid(self):
        self.assertTrue(
            hasattr(verifier, "quotient_correction_real_interval_matches"),
            "real-parameter quotient check is not implemented",
        )
        self.assertTrue(verifier.quotient_correction_real_interval_matches())

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

    def test_s3_class_constants_recover_all_fourier_coordinates(self):
        self.assertTrue(
            hasattr(verifier, "s3_constant_fourier_round_trip"),
            "class-constant Fourier inversion is not implemented",
        )
        scalar, sign, standard = sp.symbols("S F_sign F_standard")

        recovered = verifier.s3_constant_fourier_round_trip(
            scalar, sign, standard
        )

        self.assertEqual(
            tuple(sp.simplify(value) for value in recovered),
            (scalar, sign, standard),
        )

    def test_c3_fourier_inverse_has_the_claimed_conjugation_convention(self):
        self.assertTrue(
            hasattr(verifier, "c3_constant_fourier_round_trip"),
            "complex-character Fourier inversion is not implemented",
        )
        scalar, first, second = sp.symbols("S F_1 F_2")

        recovered = verifier.c3_constant_fourier_round_trip(
            scalar, first, second
        )

        self.assertEqual(
            tuple(sp.simplify(value) for value in recovered),
            (scalar, first, second),
        )

    def test_report_records_a_clean_exact_verification(self):
        report = render_report()
        self.assertTrue(report.startswith("A5 CLAIM VERIFICATION"))
        self.assertTrue(report.rstrip().endswith("STATUS: PASS"))


if __name__ == "__main__":
    unittest.main()
