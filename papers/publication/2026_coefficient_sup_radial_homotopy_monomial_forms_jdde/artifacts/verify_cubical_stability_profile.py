#!/usr/bin/env python3
"""Numerically verify the exact one-cell cubical stability profile."""

from __future__ import annotations

import argparse
import itertools
import math
import random


def rectangle_data(lengths: list[float]) -> tuple[list[float], float]:
    volume = math.prod(lengths)
    areas = [volume / length for length in lengths]
    weights = [area for area in areas for _ in range(2)]
    m_value = 1.0 / (2.0 * sum(1.0 / length for length in lengths))
    return weights, m_value


def sharp_profile(
    weights: list[float], m_value: float, deficit: float
) -> tuple[float, tuple[int, ...]]:
    perimeter = sum(weights)
    best_value = -1.0
    best_subset: tuple[int, ...] = ()
    face_count = len(weights)
    for size in range(1, face_count):
        for subset in itertools.combinations(range(face_count), size):
            subset_weight = sum(weights[index] for index in subset)
            value = 2.0 * min(
                deficit * (perimeter - subset_weight),
                (2.0 * m_value + deficit) * subset_weight,
            )
            if value > best_value:
                best_value = value
                best_subset = subset
    return best_value, best_subset


def extremizer(
    weights: list[float], m_value: float, deficit: float
) -> tuple[list[float], float]:
    profile, subset = sharp_profile(weights, m_value, deficit)
    perimeter = sum(weights)
    subset_weight = sum(weights[index] for index in subset)
    transfer = min(
        deficit * (perimeter - subset_weight),
        (2.0 * m_value + deficit) * subset_weight,
    )
    negative = set(subset)
    errors = [
        -transfer / subset_weight
        if index in negative
        else transfer / (perimeter - subset_weight)
        for index in range(len(weights))
    ]
    return errors, profile


def weighted_error(weights: list[float], errors: list[float]) -> float:
    return sum(weight * abs(error) for weight, error in zip(weights, errors))


def actual_deficit(m_value: float, errors: list[float]) -> float:
    norm = max(abs(m_value + error) for error in errors)
    return norm - m_value


def assert_close(left: float, right: float, tolerance: float = 1e-9) -> None:
    scale = max(1.0, abs(left), abs(right))
    assert abs(left - right) <= tolerance * scale, (left, right)


def run_checks(seed: int, trials: int, negative_control: bool) -> None:
    rng = random.Random(seed)
    checked_samples = 0
    for dimension in range(1, 6):
        for _ in range(trials):
            lengths = [10.0 ** rng.uniform(-0.7, 0.7) for _ in range(dimension)]
            weights, m_value = rectangle_data(lengths)
            deficit = 10.0 ** rng.uniform(-5.0, 1.0)
            errors, profile = extremizer(weights, m_value, deficit)

            assert_close(sum(w * q for w, q in zip(weights, errors)), 0.0)
            assert all(q <= deficit + 1e-10 for q in errors)
            assert all(q >= -2.0 * m_value - deficit - 1e-10 for q in errors)
            assert_close(actual_deficit(m_value, errors), deficit)
            assert_close(weighted_error(weights, errors), profile)

            if negative_control:
                false_profile = profile - 1e-8 * max(1.0, profile)
                assert weighted_error(weights, errors) <= false_profile

            cap = 2.0 * m_value + deficit
            for _ in range(40):
                candidate = [rng.uniform(-cap, deficit) for _ in weights[:-1]]
                final = -sum(
                    weight * value
                    for weight, value in zip(weights[:-1], candidate)
                ) / weights[-1]
                if not -cap <= final <= deficit:
                    continue
                candidate.append(final)
                candidate_deficit = actual_deficit(m_value, candidate)
                candidate_profile, _ = sharp_profile(
                    weights, m_value, candidate_deficit
                )
                error = weighted_error(weights, candidate)
                assert error <= candidate_profile + 1e-9 * max(1.0, candidate_profile)
                checked_samples += 1

    print(
        f"verified {5 * trials} exact extremizers and "
        f"{checked_samples} random admissible cochains"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--trials", type=int, default=40)
    parser.add_argument(
        "--negative-control",
        action="store_true",
        help="lower the claimed optimum; this mode must fail",
    )
    args = parser.parse_args()
    run_checks(args.seed, args.trials, args.negative_control)


if __name__ == "__main__":
    main()
