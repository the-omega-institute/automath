#!/usr/bin/env python3
"""Regression tests for the strict speed-separation certificate."""

from fractions import Fraction

import verify_speed_separation as certificate


def test_dyadic_tail_certificate_matches_exact_rational_values() -> None:
    partial = sum(
        (
            Fraction(certificate.dyadic_cost(exponent), 3 ** (exponent + 1))
            for exponent in range(1, 26)
        ),
        Fraction(0),
    )
    tail = certificate.GAMMA_TAIL
    upper = certificate.GAMMA_UPPER
    assert partial == Fraction(13_180_988_392_373, 2_541_865_828_329)
    assert tail == Fraction(126_600_871_936, 2_541_865_828_329)
    assert upper == Fraction(4_435_863_088_103, 847_288_609_443)


def test_complete_block_cost_identity_on_a_nontrivial_range() -> None:
    certificate.verify_complete_block_identity(max_denominator=250)


def test_certified_speed_gap_exceeds_oracle_claim() -> None:
    assert certificate.main() == 0
