#!/usr/bin/env python3
"""Verify the second-extremal formulas and source-block classification."""

from __future__ import annotations

import argparse


def fibonacci(limit: int) -> list[int]:
    values = [0, 1]
    while len(values) <= limit:
        values.append(values[-1] + values[-2])
    return values


def partition_counts(fib: list[int], upper: int) -> list[int]:
    counts = [0] * upper
    counts[0] = 1
    for part in fib[2:]:
        if part >= upper:
            break
        for n in range(upper - 1, part - 1, -1):
            counts[n] += counts[n - part]
    return counts


def coefficient_spectrum(fib: list[int], m: int) -> list[int]:
    coefficients = [1]
    for part in fib[1 : m + 1]:
        extended = [0] * (len(coefficients) + part)
        for n, value in enumerate(coefficients):
            extended[n] += value
            extended[n + part] += value
        coefficients = extended
    assert len(coefficients) == fib[m + 2]
    return coefficients


def top_two(values: list[int]) -> tuple[int, int]:
    levels = sorted(set(values), reverse=True)
    assert len(levels) >= 2
    return levels[0], levels[1]


def zeckendorf_tuple(n: int, length: int, fib: list[int]) -> tuple[int, ...]:
    bits: list[int] = []
    remainder = n
    for index in range(length, 0, -1):
        part = fib[index + 1]
        if part <= remainder:
            bits.append(1)
            remainder -= part
        else:
            bits.append(0)
    assert remainder == 0 and bits[0] == 1
    assert all(not (bits[i] and bits[i + 1]) for i in range(length - 1))

    runs: list[int] = []
    zeros = 0
    for bit in bits[1:]:
        if bit:
            runs.append(zeros)
            zeros = 0
        else:
            zeros += 1
    runs.append(zeros)
    return tuple(runs)


def layer_tuples(
    counts: list[int], fib: list[int], length: int, level: int
) -> set[tuple[int, ...]]:
    lower = fib[length + 1]
    upper = fib[length + 2]
    return {
        zeckendorf_tuple(n, length, fib)
        for n in range(lower, upper)
        if counts[n] == level
    }


def maximizing_tuples(
    counts: list[int], fib: list[int], length: int
) -> set[tuple[int, ...]]:
    lower = fib[length + 1]
    upper = fib[length + 2]
    maximum = max(counts[lower:upper])
    return layer_tuples(counts, fib, length, maximum)


def concatenate(
    left: set[tuple[int, ...]], right: set[tuple[int, ...]]
) -> set[tuple[int, ...]]:
    return {a + b for a in left for b in right}


def verify(inject_error: bool = False) -> None:
    largest_k = 12
    largest_m = 2 * largest_k + 1
    fib = fibonacci(largest_m + 4)
    counts = partition_counts(fib, fib[largest_m + 3])

    value_checks = 0
    classification_checks = 0
    for k in range(5, largest_k + 1):
        for m in (2 * k, 2 * k + 1):
            coefficients = coefficient_spectrum(fib, m)
            maximum, runner_up = top_two(coefficients)
            expected_maximum = fib[k + 2] if m % 2 == 0 else 2 * fib[k + 1]
            expected_runner_up = 4 * fib[k - 1] if m % 2 == 0 else 5 * fib[k - 1]
            if inject_error and value_checks == 0:
                expected_runner_up += 1

            assert maximum == expected_maximum, (m, maximum, expected_maximum)
            assert runner_up == expected_runner_up, (m, runner_up, expected_runner_up)
            value_checks += 1
            if k < 8:
                continue

            expected_count = 6 if m % 2 == 0 else 8
            assert coefficients.count(runner_up) == expected_count, (
                m,
                coefficients.count(runner_up),
                expected_count,
            )
            source_length = m + 1
            actual = layer_tuples(counts, fib, source_length, runner_up)
            if m % 2 == 0:
                expected = concatenate(
                    maximizing_tuples(counts, fib, 6),
                    maximizing_tuples(counts, fib, 2 * k - 5),
                ) | concatenate(
                    maximizing_tuples(counts, fib, 2 * k - 2),
                    maximizing_tuples(counts, fib, 3),
                )
            else:
                expected = concatenate(
                    maximizing_tuples(counts, fib, 7),
                    maximizing_tuples(counts, fib, 2 * k - 5),
                ) | concatenate(
                    maximizing_tuples(counts, fib, 2 * k - 5),
                    maximizing_tuples(counts, fib, 7),
                )
            assert actual == expected, (m, actual ^ expected)
            classification_checks += 1

    print(
        "RESULT: PASS "
        f"({value_checks} value checks; {classification_checks} classifications)"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inject-error",
        action="store_true",
        help="perturb the first expected value to demonstrate failure sensitivity",
    )
    args = parser.parse_args()
    verify(inject_error=args.inject_error)


if __name__ == "__main__":
    main()
