import unittest

import sympy as sp

from artifacts import verify_a5_results as verifier
from artifacts.verify_a5_results import (
    quotient_correction_coefficients,
    rational_mahler_certificate_matches,
    render_report,
    unrestricted_mahler_kernel_domain_counterexample,
    universal_product_jet,
    verify_c2_regular_cover_factorization,
    verify_diagonal_realizable_mahler_subclass,
)


class OracleA5ResultTests(unittest.TestCase):
    def test_exact_c2_boundary_collision_certificate(self):
        self.assertTrue(
            hasattr(verifier, "verify_c2_boundary_collision"),
            "the exact C2 boundary-collision verifier is not implemented",
        )
        self.assertTrue(verifier.verify_c2_boundary_collision())

    def test_binary_coboundary_identity_on_a_real_parameter_grid(self):
        self.assertTrue(
            hasattr(verifier, "binary_coboundary_real_interval_matches"),
            "the real-parameter binary coboundary check is not implemented",
        )
        self.assertTrue(verifier.binary_coboundary_real_interval_matches())

    def test_positive_rational_mahler_certificate_on_a_real_parameter_grid(self):
        self.assertTrue(rational_mahler_certificate_matches())

    def test_unrestricted_mahler_kernel_needs_a_positivity_domain(self):
        self.assertTrue(unrestricted_mahler_kernel_domain_counterexample())

    def test_diagonal_mahler_subclass_is_same_base_realizable_and_strict_gap(self):
        self.assertTrue(verify_diagonal_realizable_mahler_subclass())

    def test_critical_mahler_normalization_has_the_required_square(self):
        self.assertTrue(
            hasattr(verifier, "critical_mahler_normalization_matches"),
            "the critical Mahler normalization counterexample is not implemented",
        )
        self.assertTrue(verifier.critical_mahler_normalization_matches())

    def test_determinant_parity_forces_integral_critical_mahler_coefficients(self):
        self.assertTrue(
            hasattr(verifier, "critical_mahler_integrality_matches"),
            "the critical Mahler integrality check is not implemented",
        )
        self.assertTrue(verifier.critical_mahler_integrality_matches(order=24))

    def test_rational_critical_products_have_the_stated_denominator_exponent(self):
        audit = verifier.rational_critical_denominator_audit()

        self.assertEqual(audit["radices"], (2, 3, 4, 5))
        self.assertEqual(audit["order"], 12)
        self.assertTrue(audit["all_bounds_hold"])
        self.assertTrue(audit["nonintegral_coefficient_seen"])

    def test_critical_zero_estimate_pullback_identity_and_degree_bounds(self):
        self.assertTrue(
            hasattr(verifier, "critical_zero_estimate_pullback_matches"),
            "the critical zero-estimate pullback check is not implemented",
        )
        self.assertTrue(verifier.critical_zero_estimate_pullback_matches())

    def test_kumiko_nishioka_special_value_specialization_has_all_required_parameters(self):
        self.assertTrue(
            hasattr(verifier, "nishioka_special_value_specialization"),
            "the Kumiko Nishioka specialization audit is not implemented",
        )

    def test_c3_adams_mobius_support_is_not_lacunary(self):
        self.assertTrue(
            hasattr(verifier, "c3_adams_mobius_support_obstruction"),
            "the C3 Adams-Mobius obstruction audit is not implemented",
        )
        audit = verifier.c3_adams_mobius_support_obstruction(60)
        self.assertEqual(audit[2], (0, 1, -1))
        self.assertEqual(audit[3], (-1, 1, 0))
        self.assertEqual(audit[5], (0, 1, -1))
        self.assertEqual(audit[11], (0, 1, -1))
        self.assertEqual(audit[17], (0, 1, -1))
        self.assertNotIn(7, audit)
        self.assertNotIn(13, audit)
        self.assertEqual(
            verifier.nishioka_special_value_specialization(),
            {
                "p": 2,
                "N": 0,
                "n": 1,
                "m": 2,
                "M": 2,
                "U": 1,
                "L": 1,
                "inequality_left": 4,
                "inequality_right": 8,
                "reduced_coefficients_coprime": True,
                "admissibility_polynomial": "1 - z",
                "algebraic_point": sp.Rational(1, 5),
                "sampled_orbit_admissible": True,
                "coefficients_integral": True,
            },
        )

    def test_normalized_rational_mahler_coboundaries_are_saturated_in_examples(self):
        self.assertTrue(
            hasattr(verifier, "rational_mahler_saturation_matches"),
            "the normalized Mahler saturation check is not implemented",
        )
        self.assertTrue(verifier.rational_mahler_saturation_matches())

    def test_effective_mahler_pade_reconstructs_normalized_certificates(self):
        self.assertTrue(
            hasattr(verifier, "effective_rational_mahler_coboundary"),
            "the effective rational Mahler decision procedure is not implemented",
        )
        z = sp.Symbol("z")

        first = verifier.effective_rational_mahler_coboundary(1 + z, 1 - z)
        second = verifier.effective_rational_mahler_coboundary(
            1 + z**2, (1 + z) ** 2
        )

        self.assertEqual(first["rational_function"], 1 - z)
        self.assertEqual(second["rational_function"], 1 + z)

    def test_effective_mahler_pade_rejects_a_parity_compatible_noncertificate(self):
        z = sp.Symbol("z")

        result = verifier.effective_rational_mahler_coboundary(1 + 2 * z, 1 - 2 * z)

        self.assertIsNone(result)

    def test_effective_mahler_certificate_obeys_stated_degree_and_height_bounds(self):
        self.assertTrue(
            hasattr(verifier, "effective_mahler_bounds_match"),
            "the effective Mahler degree and height checks are not implemented",
        )
        self.assertTrue(verifier.effective_mahler_bounds_match())

    def test_general_p_pade_and_logarithmic_derivative_reduction(self):
        self.assertTrue(verifier.general_p_effective_reconstruction_matches())

    def test_logarithmic_mahler_divisor_bound_survives_exact_counterexample_search(self):
        self.assertTrue(
            hasattr(verifier, "logarithmic_mahler_divisor_bound_audit"),
            "the logarithmic divisor-bound audit is not implemented",
        )

        audit = verifier.logarithmic_mahler_divisor_bound_audit()

        self.assertGreaterEqual(audit["certificates_checked"], 100)
        self.assertGreaterEqual(audit["radices_checked"], 4)
        self.assertTrue(audit["root_of_unity_cases_checked"])
        self.assertTrue(audit["all_within_bound"])

    def test_logarithmic_degree_order_is_attained_by_an_exact_family(self):
        self.assertTrue(
            hasattr(verifier, "mahler_log_degree_extremal_family_audit"),
            "the logarithmic lower-bound family audit is not implemented",
        )

        audit = verifier.mahler_log_degree_extremal_family_audit()

        self.assertGreaterEqual(audit["families_checked"], 12)
        self.assertTrue(audit["identities_hold"])
        self.assertTrue(audit["degrees_hold"])
        self.assertTrue(audit["no_cancellation"])

    def test_parametric_standard_cover_family_has_m_exact_collisions(self):
        audit = verifier.realizable_multicollision_family_audit()

        self.assertEqual(audit["vertex_counts"], (6, 10, 14, 18))
        self.assertEqual(audit["collision_counts"], (1, 2, 3, 4))
        self.assertTrue(audit["determinant_identities_hold"])
        self.assertTrue(audit["all_radii_in_perron_interval"])
        self.assertTrue(audit["same_base_realization_holds"])
        self.assertTrue(audit["strict_gap_certified"])

    def test_logarithmic_certificate_family_has_companion_realizations(self):
        audit = verifier.realizable_logarithmic_certificate_family_audit()

        self.assertEqual(audit["vertex_counts"], (2, 4, 8, 16, 32))
        self.assertTrue(audit["relative_realizations_hold"])
        self.assertTrue(audit["certificate_degrees_hold"])
        self.assertTrue(audit["zeta_ratios_nontrivial"])

    def test_different_base_elementary_two_group_interfaces_are_exact(self):
        self.assertTrue(
            hasattr(verifier, "elementary_two_group_cross_base_audit"),
            "the cross-base elementary two-group audit is not implemented",
        )

        audit = verifier.elementary_two_group_cross_base_audit()

        self.assertEqual(audit["base_sizes"], (1, 2))
        self.assertEqual(audit["perron_roots"], (2, 2))
        self.assertTrue(audit["base_determinants_equal"])
        self.assertTrue(audit["all_character_determinants_equal"])
        self.assertTrue(audit["all_character_determinants_congruent_mod_two"])
        self.assertTrue(audit["fourier_inversion_exact"])
        self.assertTrue(audit["positive_on_real_grid"])
        self.assertTrue(audit["sample_budget_independent_of_rank"])

    def test_finite_radial_collision_audit_recovers_the_exact_collision_set(self):
        self.assertTrue(
            hasattr(verifier, "finite_radial_collision_audit"),
            "the finite radial-collision audit is not implemented",
        )
        z = sp.Symbol("z")
        q = 1 - z + 4 * z**2

        audit = verifier.finite_radial_collision_audit(
            q.subs(z, z**2), q**2, sp.Rational(1, 4)
        )

        self.assertEqual(audit["rational_function"], q)
        self.assertEqual(audit["collision_polynomial"], z * (4 * z - 1))
        self.assertEqual(audit["collision_points"], (sp.Rational(1, 4),))
        self.assertEqual(audit["degree_bound"], 32)
        self.assertEqual(audit.get("collision_bound"), 31)
        self.assertEqual(audit["sample_budget"], 32)
        self.assertTrue(audit["collision_count_within_bound"])

    def test_interior_sampling_needs_no_twisted_spectral_gap(self):
        self.assertTrue(
            hasattr(verifier, "interior_no_gap_standard_zeta_audit"),
            "the no-gap interior-sampling audit is not implemented",
        )
        audit = verifier.interior_no_gap_standard_zeta_audit()

        self.assertEqual(audit["perron_root"], 2)
        self.assertEqual(audit["first_twisted_radius"], 2)
        self.assertFalse(audit["first_has_strict_gap"])
        self.assertEqual(audit["sample_radius"], sp.Rational(1, 3))
        self.assertTrue(audit["sample_is_interior"])
        self.assertTrue(audit["same_base_compatible"])
        self.assertTrue(audit["determinants_positive_at_sample"])
        self.assertEqual(audit["determinant_ratio"], 1 - 2 * sp.Symbol("z"))
        self.assertEqual(audit["standard_zeta_ratio"], 1 - 2 * sp.Symbol("z"))
        self.assertTrue(audit["determinant_ratio_is_standard_zeta_ratio"])
        self.assertTrue(audit["all_dyadic_factors_lie_between_zero_and_one"])
        self.assertTrue(audit["dyadic_logarithm_is_negative"])

    def test_same_base_characteristic_polynomial_coefficient_bound(self):
        self.assertTrue(
            hasattr(verifier, "same_base_determinant_bounds_match"),
            "the same-base determinant coefficient check is not implemented",
        )
        self.assertTrue(verifier.same_base_determinant_bounds_match())

    def test_quadratic_binary_certificate_minimality_enumeration(self):
        self.assertTrue(
            hasattr(verifier, "enumerate_quadratic_binary_certificates"),
            "the exhaustive minimality enumeration is not implemented",
        )
        self.assertEqual(
            verifier.enumerate_quadratic_binary_certificates(),
            {
                "primitive_bases": 2208,
                "first_determinant_support": 48,
                "second_determinant_support": 0,
            },
        )

    def test_radial_profile_has_triangular_leading_coefficient(self):
        self.assertTrue(
            hasattr(verifier, "radial_profile_leading_coefficient"),
            "the radial-profile triangular check is not implemented",
        )
        self.assertEqual(
            verifier.radial_profile_leading_coefficient(
                {1: 0, 2: 0, 3: sp.Integer(7), 4: sp.Integer(-5)}
            ),
            (3, sp.Integer(-7)),
        )

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
        self.assertIn("Exact C2 boundary collision: verified", report)
        self.assertIn("Primitive two-out bases: 2208", report)
        self.assertIn("Determinant supports: 48 and 0", report)
        self.assertIn("Real boundary grid: 25 points", report)
        self.assertIn("Positive rational Mahler certificate: verified", report)
        self.assertIn("Unrestricted Mahler kernel inclusion: domain counterexample", report)
        self.assertIn("Diagonal same-base Mahler subclass: compatibility", report)
        self.assertIn("Critical Mahler normalization: squared product on 49 real points", report)
        self.assertIn("Critical Mahler integrality: 24 integer coefficients", report)
        self.assertIn("Rational critical p-Mahler denominators: p=2,3,4,5", report)
        self.assertIn("Critical zero-estimate pullback: exact identity, bidegrees", report)
        self.assertIn("Kumiko Nishioka specialization: p=2, N=0, n=1, m=M=2, L=1; 4<8", report)
        self.assertIn("Normalized Mahler saturation: exact rational examples", report)
        self.assertIn("Effective rational Mahler Pade decision: verified", report)
        self.assertIn("Effective Mahler degree and height bounds: verified", report)
        self.assertIn("General-p effective reconstruction: p=2,3,4,5", report)
        self.assertIn("Logarithmic Mahler divisor bound: exact counterexample search", report)
        self.assertIn("Mahler logarithmic lower-bound family: exact identities", report)
        self.assertIn("Realizable multi-collisions: m=1,2,3,4 on 6,10,14,18 vertices", report)
        self.assertIn("Realizable logarithmic certificates: V=2,4,8,16,32", report)
        self.assertIn("Cross-base (C2)^2 interface: sizes 1 and 2", report)
        self.assertIn("Finite radial collision set: {1/4}; 1 <= 31", report)
        self.assertIn("Finite radial recovery budget: 32 samples with one algebraic anchor", report)
        self.assertIn(
            "C3 Adams-Mobius support: non-zero at primes 2, 5, 11, 17",
            report,
        )
        self.assertIn("Same-base determinant coefficient bound: verified", report)
        self.assertIn("Radial-profile leading coefficient: triangular", report)
        self.assertTrue(report.rstrip().endswith("STATUS: PASS"))


if __name__ == "__main__":
    unittest.main()
