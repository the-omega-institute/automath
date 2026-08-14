#!/usr/bin/env python3
"""Regression tests for the Deepening Delta verification battery."""

import math
import tempfile
import unittest
from pathlib import Path

from verify_deepening_delta import (
    atomic_family_multiplicity,
    bell_number,
    classify_support_three,
    factorint_fibonacci,
    load_factorization_archive,
    omega,
    omega_big,
    private_cover_lower_bound,
    private_cover_upper_bound,
    run_battery,
    upper_fiber_exhaustive,
    upper_fiber_threshold,
    write_factorization_archive,
)


class DeepeningDeltaTests(unittest.TestCase):
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
        self.assertIn("Python version:", report)
        self.assertIn("SymPy version:", report)
        self.assertNotIn("elapsed_seconds", report.lower())
        self.assertNotIn("runtime", report.lower())
        self.assertNotIn("duration", report.lower())
        self.assertNotIn("Deepening Delta", report)
        self.assertNotIn("counterexample battery", report.lower())


if __name__ == "__main__":
    unittest.main(verbosity=2)
