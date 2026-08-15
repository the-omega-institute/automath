import math
import re
import unittest
from pathlib import Path

import numpy as np

from artifacts import verify_A8_results as verify


ROOT = Path(__file__).resolve().parents[1]


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


class CompleteMarkovPalmTangentChecks(unittest.TestCase):
    def setUp(self):
        self.g = np.array([0.18, 0.27, 0.31, 0.24])
        self.raw = np.array(
            [
                [0.7, -0.3, 0.2, 0.5],
                [-0.8, 0.4, 0.1, -0.6],
                [0.3, 0.9, -0.5, 0.2],
                [-0.2, 0.6, 0.8, -0.7],
            ]
        )

    def test_tangent_projection_is_double_centered_and_annihilates_zero_cell(self):
        score = verify.markov_palm_tangent_projection(self.g, self.raw)
        self.assertTrue(np.allclose(score @ self.g, 0.0, atol=2e-14))
        self.assertTrue(np.allclose(self.g @ score, 0.0, atol=2e-14))
        self.assertAlmostEqual(score[0, 0], 0.0, places=14)
        self.assertTrue(
            np.allclose(
                verify.markov_palm_tangent_projection(self.g, score),
                score,
                atol=2e-14,
            )
        )

    def test_projected_path_preserves_marginal_and_three_inclusions(self):
        score = verify.markov_palm_tangent_projection(self.g, self.raw)
        transition = verify.markov_palm_transition(self.g, score, 0.08)
        null_transition = np.broadcast_to(self.g, transition.shape)
        mean_cycle = float((np.arange(self.g.size) + 1.0) @ self.g)
        self.assertTrue(np.allclose(transition.sum(axis=1), 1.0, atol=2e-14))
        self.assertTrue(np.allclose(self.g @ transition, self.g, atol=2e-14))
        self.assertTrue(
            np.allclose(
                verify.markov_gap_inclusions(self.g, transition, mean_cycle),
                verify.markov_gap_inclusions(self.g, null_transition, mean_cycle),
                atol=2e-14,
            )
        )

    def test_calendar_time_information_has_mu_inverse_scaling(self):
        score = verify.markov_palm_tangent_projection(self.g, self.raw)
        mean_cycle = float((np.arange(self.g.size) + 1.0) @ self.g)
        norm_squared = float(np.einsum("i,j,ij->", self.g, self.g, score**2))
        information = verify.markov_palm_information(self.g, score)
        self.assertAlmostEqual(information, norm_squared / mean_cycle, places=14)

    def test_weighted_omnibus_has_strict_power_for_nonzero_direction(self):
        weights = np.array([0.5, 0.2, 0.08, 0.03])
        null_size, alternative_power = verify.weighted_omnibus_monte_carlo(
            weights,
            np.array([0.0, 0.0, 1.4, 0.0]),
            alpha=0.05,
            draws=300_000,
            seed=20260807,
        )
        self.assertLess(abs(null_size - 0.05), 0.002)
        self.assertGreater(alternative_power, null_size + 0.01)

    def test_full_markov_tangent_projection_satisfies_all_constraints(self):
        rng = np.random.default_rng(20260807)
        for x in (0.35, 1.0, 2.4, 5.0):
            g = verify.markov_gap_alternative(x, 0.0)[0][:12]
            g /= g.sum()
            projected = verify.markov_palm_tangent_projection(
                g, rng.normal(size=(g.size, g.size))
            )
            self.assertTrue(np.allclose(projected @ g, 0.0, atol=3e-13))
            self.assertTrue(np.allclose(g @ projected, 0.0, atol=3e-13))
            self.assertAlmostEqual(projected[0, 0], 0.0, places=12)

            mean_cycle = float((np.arange(g.size) + 1.0) @ g)
            scale = 0.02 / np.max(np.abs(projected))
            transition = g[None, :] * (1.0 + scale * projected)
            null_transition = np.broadcast_to(g, transition.shape)
            self.assertGreater(np.min(transition), 0.0)
            self.assertTrue(np.allclose(transition.sum(axis=1), 1.0, atol=3e-13))
            self.assertTrue(np.allclose(g @ transition, g, atol=3e-13))
            self.assertTrue(
                np.allclose(
                    verify.markov_gap_inclusions(g, transition, mean_cycle),
                    verify.markov_gap_inclusions(g, null_transition, mean_cycle),
                    atol=3e-13,
                )
            )

    def test_finite_markov_tangent_basis_is_orthonormal_and_complete(self):
        g = verify.markov_gap_alternative(1.35, 0.0)[0][:7]
        g /= g.sum()
        basis = verify.finite_markov_tangent_basis(g)
        self.assertEqual(basis.shape, ((g.size - 1) ** 2 - 1, g.size, g.size))
        gram = np.einsum("i,j,aij,bij->ab", g, g, basis, basis)
        self.assertTrue(np.allclose(gram, np.eye(basis.shape[0]), atol=4e-13))
        self.assertTrue(np.allclose(np.einsum("aij,j->ai", basis, g), 0.0, atol=3e-13))
        self.assertTrue(np.allclose(np.einsum("i,aij->aj", g, basis), 0.0, atol=3e-13))
        self.assertTrue(np.allclose(basis[:, 0, 0], 0.0, atol=3e-13))

    def test_markov_tangent_information_and_mixture_limit(self):
        g = verify.markov_gap_alternative(1.35, 0.0)[0][:9]
        g /= g.sum()
        q = verify.finite_markov_tangent_basis(g)[3]
        mean_cycle = float((np.arange(g.size) + 1.0) @ g)
        information = verify.markov_palm_information(g, q)
        self.assertAlmostEqual(information, 1.0 / mean_cycle, places=12)

        lag_covariance = np.einsum("i,j,k,ij,jk->", g, g, g, q, q)
        self.assertAlmostEqual(float(lag_covariance), 0.0, places=12)
        second_moments = [
            verify.rademacher_mixture_second_moment(1.7, mean_cycle, dimension)
            for dimension in (16, 64, 256, 1024)
        ]
        self.assertTrue(all(value > 1.0 for value in second_moments))
        self.assertTrue(all(a > b for a, b in zip(second_moments, second_moments[1:])))
        self.assertLess(second_moments[-1] - 1.0, 3e-3)

    def test_double_centering_cancels_first_order_marginal_drift(self):
        g = np.array([0.12, 0.19, 0.27, 0.23, 0.19])
        q = verify.finite_markov_tangent_basis(g)[5]
        marginal_score = np.array([-0.7, 0.2, 0.9, -0.3, 0.1])
        marginal_score -= float(g @ marginal_score)
        coefficient = float(
            np.einsum(
                "i,j,ij,i,j->",
                g,
                g,
                q,
                marginal_score,
                marginal_score,
            )
        )
        for parameter in (0.04, -0.03, 0.015):
            perturbed = g * (1.0 + parameter * marginal_score)
            actual = float(np.einsum("i,j,ij->", perturbed, perturbed, q))
            self.assertAlmostEqual(actual, parameter**2 * coefficient, places=14)


class CanonicalHelmertGrowingLayerChecks(unittest.TestCase):
    def test_equal_rate_tail_matches_direct_gap_mass_sum(self):
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            masses = verify._gap_masses(rate, rate, tolerance=1e-17)
            for layer in (0, 1, 2, 5, 10):
                direct = float(np.sum(masses[layer:]))
                exact = verify.equal_rate_gap_tail(rate, layer)
                self.assertLess(abs(direct - exact), 3e-14)

    def test_weighted_helmert_basis_and_layer_moment_bounds(self):
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            for layer in (2, 4, 8, 12, 20):
                gram_error, scaled_envelope, scaled_third_moment = (
                    verify.helmert_layer_diagnostics(rate, layer)
                )
                self.assertLess(gram_error, 2e-12)
                self.assertGreater(scaled_envelope, 0.0)
                self.assertLess(scaled_envelope, 200.0)
                self.assertGreater(scaled_third_moment, 0.0)
                self.assertLess(scaled_third_moment, 1500.0)

    def test_second_order_logarithmic_bracket_has_claimed_signs(self):
        log_n = 200.0
        for rate in (0.35, 1.0, 2.4, 5.0):
            log_log_n = math.log(log_n)
            necessary_inside = math.floor(
                (log_n + 2.0 * log_log_n - 20.0) / (2.0 * rate)
            )
            necessary_outside = math.ceil(
                (log_n + 2.0 * log_log_n + 20.0) / (2.0 * rate)
            )
            sufficient_inside = math.floor(
                (log_n - 2.0 * log_log_n - 20.0) / (2.0 * rate)
            )
            necessary_log_inside = verify.helmert_log_rate_terms(
                rate, log_n, necessary_inside
            )[0]
            necessary_log_outside = verify.helmert_log_rate_terms(
                rate, log_n, necessary_outside
            )[0]
            sufficient_log_inside = verify.helmert_log_rate_terms(
                rate, log_n, sufficient_inside
            )[1]
            self.assertGreater(necessary_log_inside, 5.0)
            self.assertLess(necessary_log_outside, -5.0)
            self.assertLess(sufficient_log_inside, -5.0)

    def test_overlap_vector_has_identity_covariance_and_zero_lag_covariance(self):
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            for layer in (1, 2, 4, 8):
                covariance_error, lag_error, scaled_third_moment = (
                    verify.helmert_overlap_diagnostics(rate, layer)
                )
                self.assertLess(covariance_error, 5e-10)
                self.assertLess(lag_error, 5e-10)
                self.assertGreater(scaled_third_moment, 0.0)
                self.assertLess(scaled_third_moment, 2000.0)

    def test_exact_small_block_third_moments_have_rosenthal_scaling(self):
        for rate in (0.2, 0.7, 1.35, 3.0):
            for layer in (1, 2, 3):
                ratios = [
                    verify.helmert_exact_block_moment_ratio(rate, layer, length)
                    for length in (1, 2, 3, 4)
                ]
                self.assertGreater(min(ratios), 0.0)
                self.assertLess(max(ratios), 40.0)

    def test_cmu_blocking_terms_vanish_inside_sufficient_boundary(self):
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            for log_n in (200.0, 800.0, 3200.0, 12800.0):
                layer = math.floor(
                    (
                        log_n
                        - 2.0 * math.log(log_n)
                        - 10.0
                        - math.sqrt(math.log(log_n))
                    )
                    / (2.0 * rate)
                )
                log_residual, log_gaussian, log_rare = verify.helmert_blocking_log_terms(
                    rate, log_n, layer
                )
                self.assertTrue(
                    all(math.isfinite(value) for value in (log_residual, log_gaussian, log_rare))
                )
            self.assertLess(max(log_residual, log_gaussian, log_rare), -1.0)

    def test_cmu_dimension_factor_exposes_the_open_logarithmic_gap(self):
        log_n = 12_800.0
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            layer = math.floor(log_n / (2.0 * rate))
            _, _, log_rare = verify.helmert_blocking_log_terms(
                rate, log_n, layer
            )
            self.assertGreater(log_rare, 1.0)

    def test_zolotarev_block_terms_close_the_old_cmu_window(self):
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            new_terms = []
            old_rare_terms = []
            for log_n in (200.0, 800.0, 3200.0, 12_800.0):
                layer = math.floor(log_n / (2.0 * rate))
                log_deleted, log_block, log_rare = (
                    verify.helmert_zolotarev_blocking_log_terms(
                        rate, log_n, layer
                    )
                )
                _, old_block, old_rare = verify.helmert_blocking_log_terms(
                    rate, log_n, layer
                )
                log_dimension = math.log((layer + 1) ** 2 - 1)
                self.assertAlmostEqual(log_block, old_block - log_dimension)
                self.assertAlmostEqual(log_rare, old_rare - log_dimension)
                new_terms.append(max(log_deleted, log_block, log_rare))
                old_rare_terms.append(old_rare)
            self.assertLess(new_terms[-1], new_terms[0])
            self.assertLess(new_terms[-1], -4.0)
            self.assertGreater(old_rare_terms[-1], old_rare_terms[0])
            self.assertGreater(old_rare_terms[-1], 1.0)

    def test_critical_window_constant_is_exp_c_over_four(self):
        c = 3.0
        target = c - math.log(4.0)
        for rate in (0.2, 0.7, 1.35, 3.0, 5.0):
            errors = [
                abs(verify.helmert_critical_log_mean(rate, layer, c) - target)
                for layer in (100, 300, 1000, 10000)
            ]
            self.assertLess(errors[-1], errors[0])
            self.assertLess(errors[-1], 0.02)


class SingularExchangeExperimentChecks(unittest.TestCase):
    def test_singular_gap_expansion_is_second_order_and_uniform_on_grid(self):
        for z in (0.12, 0.25, 0.5, 0.78, 0.9):
            diagonal, coefficient = verify.singular_gap_expansion(z, 80)
            for d in (2e-3, 1e-3, 5e-4):
                split = verify.survival_factor_gap_masses(z + d, z - d, 80)
                error = np.max(np.abs(split - diagonal - d**2 * coefficient))
                self.assertLess(error / d**4, 2.0e5)

    def test_singular_score_is_centered_with_positive_information(self):
        informations = []
        for z in np.linspace(0.1, 0.9, 17):
            gap, score, mean_cycle, information = verify.singular_gap_score(
                float(z), tolerance=1e-16
            )
            self.assertLess(abs(float(gap @ score)), 2e-11)
            self.assertAlmostEqual(float(gap.sum()), 1.0, places=12)
            self.assertGreater(mean_cycle, 1.0)
            self.assertGreater(information, 0.0)
            informations.append(information)
        self.assertGreater(min(informations), 1e-5)

    def test_n_quarter_split_is_root_n_in_symmetric_coordinates(self):
        for z in (0.15, 0.5, 0.85):
            for h in (-1.7, -0.4, 0.0, 0.9, 2.1):
                sigma_shift = verify.singular_symmetric_shift(z, h, 100_000_000)
                self.assertAlmostEqual(sigma_shift[0], 0.0, places=14)
                self.assertLess(abs(sigma_shift[1] + h**2), 2e-12)


class TheoremGCompletionChecks(unittest.TestCase):
    def setUp(self):
        self.results = (ROOT / "article_singular_results.tex").read_text(
            encoding="utf-8"
        )
        self.uniform = (ROOT / "article_singular_uniform_lemmas.tex").read_text(
            encoding="utf-8"
        )
        self.proof = (ROOT / "article_singular_proofs_part2.tex").read_text(
            encoding="utf-8"
        )

    def test_theorem_g_claims_only_the_finite_record_score_test(self):
        theorem_g = self.results.split(
            "\\label{thm:stationary-serial-double-pole-main}", 1
        )[1].split("\\end{paperthm}", 1)[0]
        theorem_g = re.sub(r"\s+", " ", theorem_g)
        self.assertNotIn("or the local likelihood-ratio test", theorem_g)
        self.assertIn(
            "The residualized score test is uniformly asymptotically level",
            theorem_g,
        )
        self.assertIn("limiting Gaussian experiment", self.results)

    def test_recurrence_fit_has_thresholded_total_definition(self):
        self.assertIn("\\widehat H_N", self.proof)
        self.assertIn("\\widehat s_N", self.proof)
        self.assertIn("N^{-1/2}", self.proof)
        self.assertIn("a^\\ast", self.proof)

    def test_score_test_has_information_formula_and_nonrejecting_gate(self):
        self.assertIn("I_N(\\eta)", self.results)
        self.assertIn("J_N(\\eta)", self.results)
        self.assertIn("\\lambda_{\\min}", self.results)
        self.assertIn("\\phi_N=0", self.results)

    def test_atlas_overlap_compatibility_is_proved(self):
        self.assertIn("argument-principle count would be two", self.proof)
        self.assertIn("same two nearby roots", self.proof)
        self.assertIn("numerical ordering", self.proof)

    def test_multiset_distance_is_only_eventually_exact_for_n_above_two(self):
        self.assertIn("for all sufficiently large", self.uniform)
        self.assertIn("c_0/2", self.uniform)
        self.assertIn("(2\\sqrt{v_0}/c_0)^4", self.uniform)


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
