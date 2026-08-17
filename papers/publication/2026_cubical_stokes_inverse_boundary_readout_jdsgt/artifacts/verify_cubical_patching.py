#!/usr/bin/env python3
"""Exact checks for the anisotropic two-by-two patching obstruction."""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations


CELLS = ((0, 0), (0, 1), (1, 0), (1, 1))
WIDTHS = (1, 2)
HEIGHTS = (2, 7)
BOUNDARY = (
    ((0, 0), "left", 2),
    ((0, 0), "bottom", 1),
    ((0, 1), "left", 7),
    ((0, 1), "top", 1),
    ((1, 0), "right", 2),
    ((1, 0), "bottom", 2),
    ((1, 1), "right", 7),
    ((1, 1), "top", 2),
)
INTERIOR = (
    ((0, 0), (1, 0), 2),
    ((0, 0), (0, 1), 1),
    ((0, 1), (1, 1), 7),
    ((1, 0), (1, 1), 2),
)


def nonempty_subsets(items):
    for size in range(1, len(items) + 1):
        yield from combinations(items, size)


def cut_area(cells):
    chosen = set(cells)
    area = sum(weight for cell, _, weight in BOUNDARY if cell in chosen)
    area += sum(
        weight for first, second, weight in INTERIOR
        if (first in chosen) != (second in chosen)
    )
    return Fraction(area)


def volume(cells):
    return sum(Fraction(WIDTHS[i] * HEIGHTS[j]) for i, j in cells)


def atomic_profile(delta, h):
    weights = tuple(Fraction(entry[2]) for entry in BOUNDARY)
    perimeter = sum(weights)
    values = {}
    for subset in nonempty_subsets(range(len(weights))):
        if len(subset) == len(weights):
            continue
        weight = sum(weights[index] for index in subset)
        values[subset] = 2 * min(
            delta * (perimeter - weight),
            (2 * h + delta) * weight,
        )
    return max(values.values()), values


def residual_and_capacity(negative, chosen_cells, bound):
    chosen = set(chosen_cells)
    boundary_flux = Fraction(0)
    for index, (cell, _, weight) in enumerate(BOUNDARY):
        if cell in chosen:
            boundary_flux += weight * (-bound if index in negative else bound)
    residual = volume(chosen) - boundary_flux
    capacity = bound * sum(
        weight for first, second, weight in INTERIOR
        if (first in chosen) != (second in chosen)
    )
    return abs(residual), capacity


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--negative-control",
        action="store_true",
        help="replace the proved atomic value by an incorrect value",
    )
    args = parser.parse_args()

    ratios = {
        subset: volume(subset) / cut_area(subset)
        for subset in nonempty_subsets(CELLS)
    }
    h = max(ratios.values())
    assert h == Fraction(9, 8)
    assert ratios[CELLS] == h

    delta = Fraction(9, 4)
    bound = h + delta
    profile, values = atomic_profile(delta, h)
    expected = Fraction(73 if args.negative_control else 72)
    assert profile == expected

    maximizers = {subset for subset, value in values.items() if value == profile}
    expected_maximizers = {
        (1, 2),
        (2, 3),
        (0, 1, 3, 4, 5),
        (1, 6),
        (3, 6),
        (0, 1, 3, 4, 7),
        (0, 1, 3, 5, 7),
        (0, 4, 5, 7),
        (1, 3, 4, 5, 7),
    }
    assert maximizers == expected_maximizers

    witnesses = {}
    for negative in sorted(maximizers):
        violations = []
        for chosen in nonempty_subsets(CELLS):
            residual, capacity = residual_and_capacity(negative, chosen, bound)
            if residual > capacity:
                violations.append((chosen, residual, capacity))
        assert violations, f"atomic extremizer {negative} unexpectedly extends"
        witnesses[negative] = violations[0]

    printed = ", ".join(
        f"{negative}: {residual}>{capacity}"
        for negative, (_, residual, capacity) in witnesses.items()
    )
    print(f"h={h}, delta={delta}, atomic profile={profile}")
    print(f"all {len(maximizers)} atomic maximizers violate an internal cut")
    print(printed)


if __name__ == "__main__":
    main()
