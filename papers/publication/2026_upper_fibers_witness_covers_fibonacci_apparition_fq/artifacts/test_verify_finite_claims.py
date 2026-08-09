#!/usr/bin/env python3
"""Regression tests for the Deepening Delta verification battery."""

import math
import tempfile
import unittest
from pathlib import Path

from sympy import factorint

from verify_finite_claims import (
    atomic_family_multiplicity,
    bell_number,
    bicolored_graph_count,
    classify_support_three,
    connected_minimal_cover_count,
    exact_rank_prime_count,
    expected_connected_support_spectrum,
    expected_support_spectrum,
    extremal_support_product_count,
    factorint_fibonacci,
    fibotomic_error_bound,
    fibotomic_rank_entropy_data,
    load_factorization_archive,
    local_limit_probability,
    minimal_cover_count,
    minimal_cover_counts_by_size,
    omega,
    omega_big,
    private_cover_lower_bound,
    private_cover_upper_bound,
    rank_window_deaggregation_data,
    rank_pure_sector,
    run_battery,
    support_spectra,
    theta_constant,
    theta_normalized_cover_ratio,
    upper_fiber_exhaustive,
    upper_fiber_threshold,
    refined_private_cover_upper_bound,
    write_factorization_archive,
)


class FiniteClaimTests(unittest.TestCase):
    def test_exact_total_and_connected_support_spectra(self):
        expected = {
            12: ((1, 2), (1,)),
            18: ((1, 2), (1, 2)),
            24: ((1, 2), (1, 2)),
            30: ((1, 2), (1, 2)),
            60: ((1, 2, 3), (1, 2)),
            105: ((1, 2, 3), (1, 2)),
            180: ((1, 2, 3), (1, 2, 3)),
            210: ((1, 2, 3), (1, 2, 3)),
        }
        for n, spectra in expected.items():
            with self.subTest(n=n):
                self.assertEqual(support_spectra(n), spectra)
                self.assertEqual(expected_support_spectrum(n), spectra[0])
                self.assertEqual(
                    expected_connected_support_spectrum(n), spectra[1]
                )

    def test_extremal_support_slice_has_atomic_product_count(self):
        for n in range(3, 121):
            with self.subTest(n=n):
                total, _ = support_spectra(n)
                actual = sum(
                    omega(m) == omega(n)
                    for m in upper_fiber_threshold(n).minimal_generators
                )
                self.assertEqual(actual, extremal_support_product_count(n))
                self.assertEqual(omega(n) in total, actual > 0)

    def test_fibotomic_rank_entropy_and_rank_congruences_through_120(self):
        error_bound = fibotomic_error_bound()
        for rank in range(3, 121):
            with self.subTest(rank=rank):
                data = fibotomic_rank_entropy_data(rank)
                self.assertEqual(
                    len(data.exact_rank_primes), exact_rank_prime_count(rank)
                )
                self.assertEqual(
                    data.exact_rank_radical,
                    math.prod(data.exact_rank_primes),
                )
                self.assertEqual(
                    data.fibotomic_value % data.exact_rank_radical, 0
                )
                self.assertLessEqual(
                    data.entropy_lower_bound,
                    math.log(data.fibotomic_value) + 1e-12,
                )
                self.assertLessEqual(abs(data.binet_error), error_bound)
                for index, prime in enumerate(data.exact_rank_primes, start=1):
                    self.assertGreaterEqual(
                        prime, rank * math.ceil(index / 2) - 1
                    )
                    if prime not in (2, 5):
                        self.assertTrue(
                            (prime - 1) % rank == 0
                            or (prime + 1) % rank == 0
                        )

    def test_jarden_exact_rank_consequence_in_available_range(self):
        for prime in (7, 11, 13, 17, 19):
            with self.subTest(prime=prime):
                self.assertGreaterEqual(exact_rank_prime_count(10 * prime), 2)

    def test_rank_window_deaggregation_bounds_through_120(self):
        for n in range(3, 121):
            with self.subTest(n=n):
                data = rank_window_deaggregation_data(n)
                self.assertLessEqual(data.prime_window_maximum, data.multiplicity)
                self.assertLessEqual(
                    data.multiplicity, data.prime_window_maximum + 1
                )
                self.assertLessEqual(data.visible_rank_maximum, data.multiplicity)
                self.assertLessEqual(
                    data.multiplicity,
                    1 + data.visible_rank_maximum * data.exponent_product,
                )
                self.assertGreaterEqual(
                    math.log(data.multiplicity)
                    - math.log(data.visible_rank_maximum),
                    0.0,
                )
                self.assertLessEqual(
                    math.log(data.multiplicity)
                    - math.log(data.visible_rank_maximum),
                    math.log(2) + data.exponent_cost + 1e-12,
                )

    def test_squarefree_exact_rank_partition_and_blms_pigeonhole(self):
        checks = 0
        for n in range(3, 121):
            factors = factorint(n)
            if any(exponent != 1 for exponent in factors.values()):
                continue
            data = rank_window_deaggregation_data(n)
            exact_rank_total = sum(
                exact_rank_prime_count(d)
                for d in range(1, n + 1)
                if n % d == 0
            )
            self.assertEqual(exact_rank_total, len(factorint_fibonacci(n)))
            self.assertGreaterEqual(
                data.multiplicity,
                exact_rank_total / (2 ** omega(n) - 1),
            )
            checks += 1
        self.assertEqual(checks, 73)

    def test_refined_private_cover_bound_and_boundary_convention(self):
        self.assertEqual(atomic_family_multiplicity(2), 1)
        self.assertEqual(refined_private_cover_upper_bound(1, 1), 2)
        self.assertEqual(refined_private_cover_upper_bound(2, 1), 10)
        self.assertEqual(refined_private_cover_upper_bound(3, 1), 50)
        for support_size in range(1, 20):
            for multiplicity in (1, 2, 5):
                self.assertLessEqual(
                    refined_private_cover_upper_bound(support_size, multiplicity),
                    multiplicity**support_size
                    * refined_private_cover_upper_bound(support_size, 1),
                )

    def test_minimal_cover_formula_and_connected_counts(self):
        self.assertEqual(
            tuple(minimal_cover_count(k) for k in range(1, 7)),
            (1, 2, 8, 49, 462, 6424),
        )
        self.assertEqual(minimal_cover_counts_by_size(5), (1, 90, 305, 65, 1))
        self.assertEqual(
            tuple(connected_minimal_cover_count(k) for k in range(1, 6)),
            (1, 1, 4, 23, 241),
        )
        self.assertEqual(bicolored_graph_count(4), 162)

    def test_theta_asymptotic_and_local_limit_numerically(self):
        self.assertAlmostEqual(theta_constant(0), 2.128936827211877, places=14)
        self.assertAlmostEqual(theta_constant(1), 2.128931250513028, places=14)
        for parity in (0, 1):
            ratios = [
                theta_normalized_cover_ratio(k)
                for k in range(20 + parity, 81, 2)
            ]
            self.assertLess(abs(ratios[-1] - 1.0), abs(ratios[0] - 1.0))
            self.assertLess(abs(ratios[-1] - 1.0), 0.02)
        for d in (-2, -1, 0, 1, 2):
            even_actual, even_limit = local_limit_probability(80, d)
            odd_actual, odd_limit = local_limit_probability(81, d)
            self.assertLess(abs(even_actual - even_limit), 0.01)
            self.assertLess(abs(odd_actual - odd_limit), 0.01)

    def test_rank_pure_sector_handles_exceptional_and_odd_layers(self):
        even = rank_pure_sector(30)
        self.assertEqual(even.coordinate_count, 3)
        self.assertEqual(even.exceptional_support_count, 2)
        self.assertEqual(even.minimal_cover_count, 8)
        self.assertEqual(even.admissible_cover_count, 3)
        self.assertEqual(even.canonical_product_count, 3)

        odd = rank_pure_sector(105)
        self.assertEqual(odd.coordinate_count, 3)
        self.assertEqual(odd.exceptional_support_count, 0)
        self.assertEqual(odd.minimal_cover_count, 8)
        self.assertEqual(odd.admissible_cover_count, 8)
        self.assertEqual(odd.canonical_product_count, 8)

    def test_rank_pure_products_are_independent_minimal_generators(self):
        for n in (30, 42, 105, 210):
            with self.subTest(n=n):
                sector = rank_pure_sector(n)
                actual = set(upper_fiber_threshold(n).minimal_generators)
                self.assertEqual(
                    sector.canonical_product_count,
                    len(sector.canonical_products),
                )
                self.assertTrue(set(sector.canonical_products).issubset(actual))
                self.assertGreaterEqual(
                    sector.weighted_product_count,
                    sector.canonical_product_count,
                )

    def test_corrected_n30_data_and_types(self):
        exhaustive = upper_fiber_exhaustive(30)
        threshold = upper_fiber_threshold(30)

        expected = (20, 22, 31, 244, 671)
        self.assertEqual(exhaustive.a_count, 52)
        self.assertEqual(exhaustive.minimal_generators, expected)
        self.assertEqual(threshold.a_count, 52)
        self.assertEqual(threshold.minimal_generators, expected)

        realized = {
            classify_support_three(m, 30) for m in expected
        }
        self.assertEqual(
            realized,
            {"Gamma_1", "Gamma_4", "Gamma_5", "Gamma_7", "Gamma_8"},
        )
        self.assertTrue(
            {"Gamma_3", "Gamma_6", "Gamma_9"}.isdisjoint(realized)
        )

    def test_independent_methods_agree_through_30(self):
        for n in range(2, 31):
            with self.subTest(n=n):
                exhaustive = upper_fiber_exhaustive(n)
                threshold = upper_fiber_threshold(n)
                self.assertEqual(exhaustive.a_count, threshold.a_count)
                self.assertEqual(
                    exhaustive.minimal_generators,
                    threshold.minimal_generators,
                )

    def test_finite_growth_bounds_through_50(self):
        for n in range(3, 51):
            with self.subTest(n=n):
                result = upper_fiber_threshold(n)
                k = omega(n)
                big_omega = omega_big(factorint_fibonacci(n))
                subset_bound = sum(
                    math.comb(big_omega, r)
                    for r in range(0, min(k, big_omega) + 1)
                )
                self.assertLessEqual(len(result.minimal_generators), subset_bound)
                self.assertLessEqual(len(result.minimal_generators), n**k)
                if n % 2 == 1:
                    self.assertGreaterEqual(
                        len(result.minimal_generators), bell_number(k)
                    )

    def test_private_cover_bounds_through_120(self):
        for n in range(3, 121):
            with self.subTest(n=n):
                result = upper_fiber_threshold(n)
                k = omega(n)
                count = len(result.minimal_generators)
                multiplicity = atomic_family_multiplicity(n)
                self.assertGreaterEqual(multiplicity, 1)
                if k >= 3:
                    self.assertGreaterEqual(count, private_cover_lower_bound(k))
                self.assertLessEqual(
                    count, private_cover_upper_bound(k, multiplicity)
                )

    def test_private_cover_bounds_have_the_claimed_finite_values(self):
        self.assertEqual(private_cover_lower_bound(3), 1)
        self.assertEqual(private_cover_lower_bound(4), 9)
        self.assertEqual(private_cover_lower_bound(5), 27)
        self.assertEqual(private_cover_lower_bound(6), 343)
        self.assertEqual(private_cover_upper_bound(1, 1), 2)
        self.assertEqual(private_cover_upper_bound(2, 1), 12)

    def test_factorization_archive_round_trip_through_30(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "fibonacci_factorizations_2_30.tsv"
            write_factorization_archive(path, 30)
            archive = load_factorization_archive(path, 30)
            self.assertEqual(archive[2], tuple())
            self.assertEqual(archive[30], factorint_fibonacci(30))
            text = path.read_text(encoding="ascii")
            self.assertIn("python_version\tsympy_version", text)
            self.assertIn("30\t832040\t2^3*5*11*31*61", text)

    def test_report_documents_set_equalities_and_versions(self):
        report = run_battery(30, 30)
        self.assertIn("B_n direct = B_n upper fiber: 29/29 set equalities", report)
        self.assertIn("M_n direct = M_n witness: 29/29 set equalities", report)
        self.assertIn("Rank-pure layers checked: 28", report)
        self.assertIn("Odd layers realizing all minimal covers: 14/14", report)
        self.assertIn("Rank-pure canonical products in M_n: 28/28 layer checks", report)
        self.assertIn("Exact total support spectra: 28/28", report)
        self.assertIn("Exact connected support spectra: 28/28", report)
        self.assertIn("Extremal atomic-product counts: 28/28", report)
        self.assertIn("Theta-normalized C_k ratios at k=20,40,80:", report)
        self.assertIn("Central local-limit errors at k=40,80 (d=0):", report)
        self.assertIn("Rank-window deaggregation inequalities: 28/28", report)
        self.assertIn("Squarefree BLMS pigeonhole inequalities: 17/17", report)
        self.assertIn("Refined private-cover upper bounds: 28/28", report)
        self.assertIn("Fibotomic rank-entropy inequalities: 28/28", report)
        self.assertIn("Fibotomic exact-rank radical divisibilities: 28/28", report)
        self.assertIn("Jarden a(10p) >= 2 checks: 0/0", report)
        self.assertIn("Python version:", report)
        self.assertIn("SymPy version:", report)
        self.assertNotIn("Deepening Delta", report)
        self.assertNotIn("counterexample battery", report.lower())


if __name__ == "__main__":
    unittest.main(verbosity=2)
