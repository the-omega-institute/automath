#!/usr/bin/env python3
"""Exact finite-window checks for the mesoscopic spectrum theorem."""

from __future__ import annotations

import argparse
import math
import sys
from collections import Counter


def fibonacci_through(index: int) -> list[int]:
    values = [0, 1]
    while len(values) <= index:
        values.append(values[-1] + values[-2])
    return values


def totient(n: int) -> int:
    result = n
    divisor = 2
    remainder = n
    while divisor * divisor <= remainder:
        if remainder % divisor == 0:
            while remainder % divisor == 0:
                remainder //= divisor
            result -= result // divisor
        divisor += 1
    if remainder > 1:
        result -= result // remainder
    return result


def divisors(n: int) -> list[int]:
    small: list[int] = []
    large: list[int] = []
    for divisor in range(1, math.isqrt(n) + 1):
        if n % divisor:
            continue
        small.append(divisor)
        if divisor * divisor != n:
            large.append(n // divisor)
    return small + large[::-1]


def generator_counts(limit: int) -> list[int]:
    """Coefficients of the free ordered-factorization series."""
    counts = [0] * (limit + 1)
    counts[1] = 1
    for n in range(2, limit + 1):
        counts[n] = sum(
            totient(divisor) * counts[n // divisor]
            for divisor in divisors(n)
            if divisor >= 2
        )
    return counts


def extend_coefficients(coefficients: list[int], weight: int) -> list[int]:
    result = coefficients + [0] * weight
    for index, value in enumerate(coefficients):
        result[index + weight] += value
    return result


def collect_failures(max_m: int, perturb: bool = False) -> list[str]:
    fib = fibonacci_through(max_m + 2)
    psi = generator_counts(max_m // 2)
    if perturb and len(psi) > 3:
        psi[3] += 1

    failures: list[str] = []
    coefficients = [1]
    spectra: dict[int, Counter[int]] = {}
    for m in range(1, max_m + 1):
        coefficients = extend_coefficients(coefficients, fib[m])
        spectrum = Counter(coefficients)
        spectra[m] = spectrum

        for cutoff in range(2, m // 2 + 1):
            actual = sum(count for level, count in spectrum.items() if level <= cutoff)
            expected = 2 + 4 * sum(psi[2 : cutoff + 1])
            if actual != expected:
                failures.append(
                    f"cutoff m={m} K={cutoff}: actual={actual} expected={expected}"
                )

    for level in range(3, max_m // 2 + 1):
        stable = spectra[2 * level][level]
        boundary = spectra[2 * level - 1][level]
        expected_stable = 4 * psi[level]
        expected_boundary = expected_stable - 2
        if stable != expected_stable:
            failures.append(
                f"stable k={level}: actual={stable} expected={expected_stable}"
            )
        if boundary != expected_boundary:
            failures.append(
                f"boundary k={level}: actual={boundary} expected={expected_boundary}"
            )
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=24)
    parser.add_argument(
        "--negative-control",
        action="store_true",
        help="perturb Psi(3) and pass only if the verifier detects the error",
    )
    args = parser.parse_args(argv)
    if args.max_m < 8:
        parser.error("--max-m must be at least 8")

    failures = collect_failures(args.max_m, perturb=args.negative_control)
    if args.negative_control:
        if failures:
            print(f"NEGATIVE CONTROL: detected {len(failures)} induced failures")
            return 0
        print("NEGATIVE CONTROL FAILED: induced error was not detected")
        return 1

    print("MESOSCOPIC SPECTRUM EXACT VERIFICATION")
    print(f"window_range=1..{args.max_m}")
    print("checks=moving_cutoff_identity,sharp_stabilization_boundary")
    print(f"failures={len(failures)}")
    if failures:
        for failure in failures[:20]:
            print(failure)
        print("RESULT: VERIFICATION FAILED")
        return 1
    print("RESULT: 0 failures / exact identities verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
