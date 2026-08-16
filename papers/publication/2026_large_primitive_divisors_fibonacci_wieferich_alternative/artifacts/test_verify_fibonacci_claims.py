#!/usr/bin/env python3
"""Unit tests for the finite Fibonacci consistency checks."""

from __future__ import annotations

import math
import unittest

from verify_fibonacci_claims import (
    PAPER_PRODUCT_CONSTANT,
    exact_rank_records,
    fibotomic_records,
    lifting_records,
    run_verification,
)


class FibonacciClaimsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ranks = exact_rank_records(60)
        cls.fibotomic = fibotomic_records(cls.ranks)

    def test_exact_rank_counts_include_classical_small_exceptions(self) -> None:
        counts = {record.rank: len(record.primes) for record in self.ranks}
        self.assertEqual(counts[3], 1)
        self.assertEqual(counts[5], 1)
        self.assertEqual(counts[6], 0)
        self.assertEqual(counts[12], 0)
        self.assertTrue(all(counts[n] >= 1 for n in range(3, 61) if n not in (6, 12)))

    def test_fibotomic_radical_entropy_and_primitive_part_claims(self) -> None:
        for record in self.fibotomic:
            with self.subTest(rank=record.rank):
                self.assertEqual(record.fibotomic_value % record.exact_rank_radical, 0)
                self.assertGreaterEqual(record.product_margin, -1e-12)
                self.assertGreaterEqual(record.entropy_margin, -1e-12)
                self.assertGreaterEqual(record.binet_error_margin, -1e-12)
                if record.rank >= 13:
                    self.assertEqual(record.fibotomic_value % record.primitive_part, 0)
                    self.assertTrue(
                        record.primitive_ratio == 1
                        or (
                            record.rank % record.primitive_ratio == 0
                            and record.primitive_ratio >= 2
                            and all(
                                record.primitive_ratio % divisor
                                for divisor in range(2, math.isqrt(record.primitive_ratio) + 1)
                            )
                        )
                    )
                    self.assertLessEqual(record.primitive_ratio, record.rank)

    def test_lifting_law_and_named_exceptions_are_visible(self) -> None:
        records, exceptions = lifting_records(prime_limit=200, u_limit=24)
        self.assertTrue(records)
        self.assertTrue(all(record.actual == record.expected for record in records))
        self.assertEqual(exceptions.two_first_failure_u, 2)
        self.assertEqual(exceptions.two_expected, 2)
        self.assertEqual(exceptions.two_actual, 3)
        self.assertTrue(exceptions.five_formula_holds_on_test_range)
        self.assertTrue(exceptions.five_rank_congruence_vacuous)

    def test_product_constant_perturbation_is_rejected(self) -> None:
        with self.assertRaisesRegex(AssertionError, r"rank 4"):
            fibotomic_records(self.ranks[1:], product_constant=0.76)
        self.assertEqual(PAPER_PRODUCT_CONSTANT, 2.0 / 3.0)
        fibotomic_records(self.ranks, product_constant=PAPER_PRODUCT_CONSTANT)

    def test_report_contains_observed_margins_and_ranges(self) -> None:
        report = run_verification(max_rank=60, prime_limit=200, u_limit=24)
        self.assertIn("Exact ranks computed completely: 3 <= d <= 60", report)
        self.assertIn("Minimum fibotomic product margin", report)
        self.assertIn("Minimum entropy margin", report)
        self.assertIn("Minimum Binet-error margin", report)
        self.assertIn("Primitive-part ratios checked: 13 <= n <= 60", report)
        self.assertIn("Lifting equalities checked:", report)
        self.assertIn("p=2 first failure: u=2, expected=2, actual=3", report)
        self.assertIn("p=5: lifting formula held", report)
        self.assertIn("Finite normalized exact-rank ratios", report)
        self.assertIn(
            "Sensitivity test: replacing 2/3 by 0.76 gives rank 4 product margin=",
            report,
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
