#!/usr/bin/env python3
"""Exact falsification checks for arbitrary bounded coefficient alphabets.

The parameter-uniform proof is algebraic.  These finite enumerations only
test the first apertures at and beyond the computed contraction thresholds.
"""

from __future__ import annotations


def recurrence(initial: tuple[int, int, int], length: int) -> list[int]:
    values = list(initial)
    while len(values) < length:
        values.append(3 * values[-1] - 2 * values[-2] + values[-3])
    return values


def adjacent_solutions(
    initial: tuple[int, int, int], coefficient_bound: int, aperture: int
) -> tuple[int, int]:
    """Count adjacent exact relations and violations of adjacent collapse."""

    u = recurrence(initial, aperture + 1)
    modulus = u[aperture]
    digits = range(-coefficient_bound, coefficient_bound + 1)
    carry_bound = coefficient_bound * sum(u[:aperture]) // modulus
    remaining_bounds = [0] * aperture
    running = 0
    for index in range(1, aperture):
        running += coefficient_bound * u[index]
        remaining_bounds[index] = running

    middle = [0] * (aperture - 1)
    solution_count = 0
    violation_count = 0

    def finish(k0: int) -> None:
        nonlocal solution_count, violation_count
        shifted_sum = sum(
            u[index - 1] * middle[index - 1]
            for index in range(1, aperture)
        )
        for final_coefficient in digits:
            numerator = shifted_sum + u[aperture - 1] * final_coefficient
            if numerator % modulus:
                continue
            k1 = numerator // modulus
            solution_count += 1
            if k1 != 0 or final_coefficient != -k0:
                violation_count += 1

    def solve_middle(index: int, target: int, k0: int) -> None:
        if index == 0:
            if target == 0:
                finish(k0)
            return
        tail_bound = remaining_bounds[index - 1]
        weight = u[index]
        for coefficient in digits:
            residual = target - coefficient * weight
            if -tail_bound <= residual <= tail_bound:
                middle[index - 1] = coefficient
                solve_middle(index - 1, residual, k0)

    for k0 in range(-carry_bound, carry_bound + 1):
        for first_coefficient in digits:
            target = k0 * modulus - first_coefficient
            if abs(target) <= remaining_bounds[aperture - 1]:
                solve_middle(aperture - 1, target, k0)

    return solution_count, violation_count


def main() -> None:
    # The root is the non-Condition-F Pisot root of x^3-3x^2+2x-1.
    # For canonical counts (1,3,7), valid effective bounds give m_0=5 for
    # D=2 and D=3.  The nonstandard initial values (1,2,4) give m_0=5 for
    # D=2 and m_0=9 for D=3.
    cases = {
        ((1, 3, 7), 2, 5): 17,
        ((1, 3, 7), 2, 6): 35,
        ((1, 3, 7), 2, 7): 75,
        ((1, 3, 7), 2, 8): 161,
        ((1, 3, 7), 3, 5): 65,
        ((1, 3, 7), 3, 6): 195,
        ((1, 3, 7), 3, 7): 589,
        ((1, 3, 7), 3, 8): 1777,
        ((1, 2, 4), 2, 5): 27,
        ((1, 2, 4), 2, 6): 63,
        ((1, 2, 4), 3, 9): 9217,
        ((1, 2, 4), 3, 10): 27745,
    }

    passed = 0
    for (initial, coefficient_bound, aperture), expected_count in cases.items():
        count, violations = adjacent_solutions(initial, coefficient_bound, aperture)
        assert count == expected_count, (
            initial,
            coefficient_bound,
            aperture,
            count,
            expected_count,
        )
        assert violations == 0, (
            initial,
            coefficient_bound,
            aperture,
            violations,
        )
        passed += 1
        print(
            f"PASS initial={initial} D={coefficient_bound} m={aperture} "
            f"adjacent_solutions={count} violations={violations}"
        )

    print(f"PASS: {passed}/{len(cases)} arbitrary-D adjacent-collapse cases")


if __name__ == "__main__":
    main()
