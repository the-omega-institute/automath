#!/usr/bin/env python3
"""Regression tests for the mesoscopic spectrum verifier."""

import verify_mesoscopic_spectrum as verifier


def test_exact_cutoff_and_sharp_boundary_identities() -> None:
    assert verifier.collect_failures(20) == []


def test_negative_control_is_detected() -> None:
    assert verifier.collect_failures(12, perturb=True)
