#!/usr/bin/env python3
"""Direct finite-size check of the Fibonacci crossover partition sum.

The computation first obtains every R(N) in the requested layers by the
distinct-part subset-sum recurrence.  It prints the resulting integer
histograms before evaluating any asymptotic formula.  The factor-four
prefactor mutation is a negative control, not an alternative fit.
"""

from __future__ import annotations

import os

import argparse
import math
import sys
import textwrap
from pathlib import Path

import mpmath as mp
import numpy as np


DEFAULT_LADDER = (12, 16, 20, 24, 28, 32)
DEFAULT_THETAS = (-4.0, 0.0, 4.0)
# Independently calibrated in verify_critical_gibbs_geometry.py.  Its finite
# cutoff sensitivity is printed in critical_gibbs_geometry_check.txt.
MU_C = 21.774225990


def fibonacci_numbers(maximum_index: int) -> list[int]:
    """Return F_0 through F_maximum_index."""
    if maximum_index < 1:
        raise ValueError("maximum_index must be at least one")
    values = [0, 1]
    while len(values) <= maximum_index:
        values.append(values[-1] + values[-2])
    return values


def representation_counts(maximum: int) -> np.ndarray:
    """Return the exact distinct-Fibonacci-part counts R(0),...,R(maximum)."""
    if maximum < 0:
        raise ValueError("maximum must be nonnegative")
    counts = np.zeros(maximum + 1, dtype=np.int64)
    counts[0] = 1
    first, second = 1, 2
    while first <= maximum:
        # NumPy buffers the overlapping right-hand side, giving the usual
        # descending-index subset-sum update without a Python-level loop.
        counts[first:] += counts[:-first]
        first, second = second, first + second
    if np.any(counts < 0):
        raise OverflowError("R(N) exceeded the signed 64-bit range")
    return counts


def layer_histogram(
    counts: np.ndarray, fibonacci: list[int], m: int
) -> tuple[int, int, dict[int, int]]:
    """Return layer endpoints and the exact histogram {R-value: count}."""
    lower = fibonacci[m + 1] - 1
    upper = fibonacci[m + 2] - 1
    if upper > len(counts):
        raise ValueError("representation array does not cover the requested layer")
    values, frequencies = np.unique(counts[lower:upper], return_counts=True)
    histogram = {
        int(value): int(frequency) for value, frequency in zip(values, frequencies)
    }
    return lower, upper, histogram


def crossover_limit(theta: float, mu_c: float) -> float:
    """Return 2(1-exp(-theta/mu_C))/theta, continuously at theta=0."""
    if abs(theta) < 1.0e-8:
        return 2.0 / mu_c
    return 2.0 * (-math.expm1(-theta / mu_c)) / theta


def wrong_prefactor_limit(theta: float, mu_c: float) -> float:
    """Negative control obtained by replacing the correct prefactor 2 by 1/2."""
    return crossover_limit(theta, mu_c) / 4.0


def critical_parameters() -> tuple[float, float]:
    """Return sigma_0 and kappa=-d B_s(1)/ds at sigma_0."""
    mp.mp.dps = 40
    sigma = mp.findroot(
        lambda s: mp.zeta(s - 1) / mp.zeta(s) - 2,
        (mp.mpf("2.4"), mp.mpf("2.6")),
    )
    rho = lambda s: mp.zeta(s - 1) / mp.zeta(s)
    kappa = -mp.diff(rho, sigma)
    return float(sigma), float(kappa)


def _histogram_lines(histogram: dict[int, int], width: int = 100) -> list[str]:
    raw = " ".join(f"{value}:{count}" for value, count in histogram.items())
    return textwrap.wrap(raw, width=width, initial_indent="  ", subsequent_indent="  ")


def build_report(ladder: tuple[int, ...], thetas: tuple[float, ...]) -> tuple[str, bool]:
    """Compute the raw data and comparisons, returning the report and gate."""
    if not ladder or min(ladder) < 1:
        raise ValueError("layer indices must be positive")
    sigma_0, kappa = critical_parameters()
    fibonacci = fibonacci_numbers(max(ladder) + 2)
    maximum = fibonacci[max(ladder) + 2] - 2
    counts = representation_counts(maximum)

    histograms: dict[int, dict[int, int]] = {}
    lines = [
        "Direct finite-size crossover check from R(N)",
        "============================================",
        "",
        "PURPOSE: finite-layer corroboration only; no numerical result is used",
        "as a premise in the proof.",
        f"sigma_0 = {sigma_0:.16f}",
        f"kappa = -B'_sigma0(1) = {kappa:.16f}",
        f"mu_C input = {MU_C:.9f}",
        f"largest N computed = {maximum}",
        f"maximum observed R(N) = {int(np.max(counts))}",
        "",
        "Raw integer counts (printed before asymptotic comparisons)",
        "---------------------------------------------------------",
        "Each histogram entry is R-value:number of N in the layer.",
    ]
    raw_ok = True
    for m in ladder:
        lower, upper, histogram = layer_histogram(counts, fibonacci, m)
        histograms[m] = histogram
        raw_count = sum(histogram.values())
        expected_count = fibonacci[m]
        raw_ok &= raw_count == expected_count
        lines.extend(
            [
                "",
                f"m={m}: I_m=[{lower},{upper}), raw count={raw_count}, "
                f"F_m={expected_count}, distinct R-values={len(histogram)}",
                "R histogram:",
                *_histogram_lines(histogram),
            ]
        )

    lines.extend(
        [
            "",
            "Asymptotic comparisons",
            "----------------------",
            "The proved target is Z_m^R(-s_m)/m -> "
            "2(1-exp(-theta/mu_C))/theta.",
            "The control replaces the prefactor 2 by 1/2 and is four times smaller.",
            "",
            "m  theta       s_m          Z_m        Z_m/m      target   rel.err"
            "    control  control rel.err",
        ]
    )
    final_correct_errors: list[float] = []
    final_control_errors: list[float] = []
    normalized_by_theta: dict[float, list[float]] = {theta: [] for theta in thetas}
    for m in ladder:
        histogram = histograms[m]
        values = np.fromiter(histogram.keys(), dtype=np.float64)
        frequencies = np.fromiter(histogram.values(), dtype=np.float64)
        for theta in thetas:
            s_m = sigma_0 + theta / (kappa * m)
            partition_sum = float(np.sum(frequencies * values ** (-s_m)))
            normalized = partition_sum / m
            target = crossover_limit(theta, MU_C)
            control = wrong_prefactor_limit(theta, MU_C)
            relative_error = (normalized - target) / target
            control_relative_error = (normalized - control) / control
            normalized_by_theta[theta].append(normalized)
            lines.append(
                f"{m:2d} {theta:+6.1f}  {s_m:12.9f}  {partition_sum:10.7f}"
                f"  {normalized:10.7f}  {target:9.7f}  {relative_error:+8.3f}"
                f"  {control:9.7f}  {control_relative_error:+10.3f}"
            )
            if m == ladder[-1]:
                final_correct_errors.append(abs(normalized - target))
                final_control_errors.append(abs(normalized - control))

    trend_ok = all(
        all(later < earlier for earlier, later in zip(values, values[1:]))
        for values in normalized_by_theta.values()
    )
    control_rejected = all(
        correct < control
        for correct, control in zip(final_correct_errors, final_control_errors)
    )
    passed = raw_ok and trend_ok and control_rejected
    lines.extend(
        [
            "",
            "Conclusions",
            "-----------",
            "raw layer counts: " + ("PASS" if raw_ok else "RED"),
            "Z_m/m decreases along every displayed m-ladder: "
            + ("PASS" if trend_ok else "RED"),
            "factor-four control is farther from every largest-m observation: "
            + ("PASS (control rejected)" if control_rejected else "RED"),
            "OVERALL = " + ("PASS" if passed else "RED"),
        ]
    )
    return "\n".join(lines) + "\n", passed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ladder", type=int, nargs="+", default=DEFAULT_LADDER)
    parser.add_argument("--theta", type=float, nargs="+", default=DEFAULT_THETAS)
    parser.add_argument(
        "--output",
        default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "finite_size_crossover_check.txt"),
        help="report path relative to the paper directory, or - for stdout only",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report, passed = build_report(tuple(sorted(set(args.ladder))), tuple(args.theta))
    sys.stdout.write(report)
    if args.output != "-":
        output_path = Path(args.output)
        output_path.write_text(report, encoding="ascii", newline="\n")
        print(f"wrote {output_path}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
