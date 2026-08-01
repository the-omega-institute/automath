#!/usr/bin/env python3
"""Exact and numerical audit for the Deepening Delta extremal/LDP claims."""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter
from pathlib import Path


def fibonacci_through(n: int) -> list[int]:
    values = [0, 1]
    while len(values) <= n:
        values.append(values[-1] + values[-2])
    return values


def extend_subset_coefficients(coefficients: list[int], weight: int) -> list[int]:
    result = [0] * (len(coefficients) + weight)
    for index, value in enumerate(coefficients):
        result[index] += value
        result[index + weight] += value
    return result


def ordinary_partition_values(limit: int, weights: list[int]) -> list[int]:
    values = [0] * (limit + 1)
    values[0] = 1
    for weight in weights:
        for n in range(limit, weight - 1, -1):
            values[n] += values[n - weight]
    return values


def residue_fibers_from_affine_spectrum(
    m: int, coefficients: list[int], fib: list[int]
) -> list[int]:
    if m == 0:
        return [1]
    modulus = fib[m + 2]
    multiplier = fib[m + 1]
    translation = multiplier - 1
    fibers = [0] * modulus
    for n, value in enumerate(coefficients):
        residue = (multiplier * n + translation) % modulus
        fibers[residue] = value
    return fibers


def expected_maximum(m: int, fib: list[int]) -> int:
    if m in (0, 1):
        return 1
    if m % 2 == 0:
        return fib[m // 2 + 2]
    return 2 * fib[(m - 1) // 2 + 1]


SMALL_MAXIMIZERS = {
    0: {0},
    1: {0, 1},
    2: {0},
    3: {0, 1, 3},
    4: {0, 3},
    5: {3},
    6: {3, 8},
    7: {3, 8, 11, 16},
    8: {8, 16, 24},
    9: {16, 24, 29, 37},
    11: {37, 63, 71, 79, 105},
}


def expected_maximizers(m: int, fib: list[int]) -> set[int]:
    if m in SMALL_MAXIMIZERS:
        return SMALL_MAXIMIZERS[m]

    # G_j = F_{j+1} in the theorem.
    def g(j: int) -> int:
        return fib[j + 1]

    if m % 2 == 0 and m >= 10:
        k = m // 2
        if k % 2 == 0:
            i_value = g(k + 1) * g(k - 3) + 1
        else:
            i_value = g(k) * g(k - 2) + 1
        return {i_value - 1, g(2 * k) - 1 - i_value}

    if m % 2 == 1 and m >= 13:
        k = (m + 1) // 2
        if k % 2 == 0:
            i_value = g(k + 2) * g(k - 5) + g(3) + 1
            j_value = g(k + 1) * g(k - 3) + 1
        else:
            i_value = g(k + 1) * g(k - 4) + g(3) + 1
            j_value = g(k) * g(k - 2) + 1
        mirror_span = g(2 * k - 1) - 1
        return {
            i_value - 1,
            j_value - 1,
            mirror_span - i_value,
            mirror_span - j_value,
        }

    raise ValueError(f"No maximizer formula registered for m={m}")


def logsumexp_weighted(level_counts: Counter[int], tilt: float) -> float:
    terms = [math.log(count) + tilt * math.log(level) for level, count in level_counts.items()]
    maximum = max(terms)
    return maximum + math.log(sum(math.exp(term - maximum) for term in terms))


def empirical_ldp_audit(
    snapshots: dict[int, list[int]], output_csv: Path
) -> tuple[int, list[str]]:
    failures = 0
    messages: list[str] = []
    tilts = [value / 4 for value in range(-16, 49)]  # [-4, 12] in steps of 1/4.
    csv_rows: list[dict[str, str | int]] = []

    for m, coefficients in sorted(snapshots.items()):
        level_counts = Counter(coefficients)
        log_cardinality = math.log(len(coefficients))
        scaled_cgf = [
            (logsumexp_weighted(level_counts, tilt) - log_cardinality) / m
            for tilt in tilts
        ]

        slope_differences = [
            scaled_cgf[index + 1] - scaled_cgf[index]
            for index in range(len(scaled_cgf) - 1)
        ]
        convex_violations = sum(
            slope_differences[index + 1] < slope_differences[index] - 1.0e-12
            for index in range(len(slope_differences) - 1)
        )
        failures += convex_violations

        mean_thickness = sum(
            count * math.log(level) for level, count in level_counts.items()
        ) / (len(coefficients) * m)
        alpha_max = math.log(max(coefficients)) / m
        alphas = [alpha_max * index / 80 for index in range(81)]
        alphas.append(mean_thickness)
        alphas = sorted(set(alphas))
        rates = [
            max(tilt * alpha - cgf for tilt, cgf in zip(tilts, scaled_cgf))
            for alpha in alphas
        ]

        negative_rate_count = sum(rate < -1.0e-11 for rate in rates)
        failures += negative_rate_count
        mean_index = alphas.index(mean_thickness)
        mean_rate = rates[mean_index]
        if abs(mean_rate) > 1.0e-10:
            failures += 1

        rate_slope_violations = 0
        secant_slopes = [
            (rates[index + 1] - rates[index]) / (alphas[index + 1] - alphas[index])
            for index in range(len(alphas) - 1)
        ]
        for index in range(len(secant_slopes) - 1):
            if secant_slopes[index + 1] < secant_slopes[index] - 1.0e-9:
                rate_slope_violations += 1
        failures += rate_slope_violations

        messages.append(
            "LDP_SHAPE m={} cgf_convex_violations={} rate_convex_violations={} "
            "negative_rates={} I(mean)={:.3e} alpha_mean={:.9f} alpha_max={:.9f}".format(
                m,
                convex_violations,
                rate_slope_violations,
                negative_rate_count,
                mean_rate,
                mean_thickness,
                alpha_max,
            )
        )
        for alpha, rate in zip(alphas, rates):
            csv_rows.append(
                {
                    "m": m,
                    "alpha": f"{alpha:.12f}",
                    "empirical_rate": f"{rate:.12f}",
                }
            )

    output_csv.parent.mkdir(parents=True, exist_ok=True)
    with output_csv.open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=["m", "alpha", "empirical_rate"])
        writer.writeheader()
        writer.writerows(csv_rows)
    return failures, messages


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=28)
    parser.add_argument(
        "--rate-csv",
        type=Path,
        default=Path(__file__).with_name("ldp_rate_shape.csv"),
    )
    args = parser.parse_args()
    if args.max_m < 13:
        parser.error("--max-m must be at least 13")

    fib = fibonacci_through(args.max_m + 4)
    ordinary_limit = fib[args.max_m + 3] - 1
    ordinary = ordinary_partition_values(
        ordinary_limit, [fib[index] for index in range(2, args.max_m + 3)]
    )

    failures = 0
    counterexamples = 0
    maxima: list[int] = []
    coefficients = [1]
    snapshot_indices = {18, 22, 26, args.max_m}
    snapshots: dict[int, list[int]] = {}
    final_top_levels: list[tuple[int, int]] = []

    for m in range(args.max_m + 1):
        if m > 0:
            coefficients = extend_subset_coefficients(coefficients, fib[m])
        fibers = residue_fibers_from_affine_spectrum(m, coefficients, fib)

        interval_mismatches = 0
        for residue, value in enumerate(fibers):
            if residue <= fib[m + 1] - 2:
                expected = ordinary[fib[m + 2] + residue]
            else:
                expected = ordinary[residue]
            if value != expected:
                interval_mismatches += 1
        failures += interval_mismatches

        direct_maximum = max(coefficients)
        maxima.append(direct_maximum)
        if direct_maximum != expected_maximum(m, fib):
            failures += 1
            counterexamples += 1

        actual_maximizers = {
            residue for residue, value in enumerate(fibers) if value == direct_maximum
        }
        predicted_maximizers = expected_maximizers(m, fib)
        if actual_maximizers != predicted_maximizers:
            failures += 1
            counterexamples += 1

        if m >= 6 and direct_maximum != maxima[m - 2] + maxima[m - 4]:
            failures += 1
            counterexamples += 1

        if m in snapshot_indices:
            snapshots[m] = coefficients.copy()
        if m == args.max_m:
            counts = Counter(coefficients)
            final_top_levels = [(level, counts[level]) for level in sorted(counts, reverse=True)[:8]]

    ldp_failures, ldp_messages = empirical_ldp_audit(snapshots, args.rate_csv)
    failures += ldp_failures

    print("DEEPENING DELTA NUMERICAL VERIFICATION")
    print(f"exact_window_range=0..{args.max_m}")
    print(f"largest_direct_coefficient_array={len(coefficients)}")
    print("checks=interval_identity,closed_forms,recurrence,maximizer_classification")
    print(f"recurrence_counterexample_search=6..{args.max_m}")
    print(f"classification_counterexample_search=0..{args.max_m}")
    print(f"top_8_levels_at_m={args.max_m}: {final_top_levels}")
    for message in ldp_messages:
        print(message)
    print(f"empirical_rate_csv={args.rate_csv}")
    print(f"failures={failures}")
    print(f"counterexamples={counterexamples}")
    if failures == 0 and counterexamples == 0:
        print("RESULT: 0 failures / 0 counterexamples")
        return 0
    print("RESULT: VERIFICATION FAILED")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
