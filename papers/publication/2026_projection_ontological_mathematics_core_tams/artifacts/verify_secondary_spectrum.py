"""Verify the exact secondary-root separation for q=9,...,17."""

from __future__ import annotations

import sympy as sp
from sympy.polys.rootisolation import dup_isolate_complex_roots_sqf


X = sp.symbols("x")

RECURRENCES = {
    9: (2, 62, 386, 2819, 62, 900, -450),
    10: (2, 96, 830, 7945, 2, 1852, -830, 4, -4),
    11: (2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174),
    12: (
        2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242,
        15404, -7216, 8, -8,
    ),
    13: (
        2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891,
        318938, 289380, -144690,
    ),
    14: (
        2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566,
        1443750, 63044, -30280, 8, -8,
    ),
    15: (
        2, 1000, 30766, 994458, -6188172, -119408756, 8289820,
        134208623, 6186122, 16637076, -8318538,
    ),
    16: (
        2, 1611, 62312, 2559407, -24862788, -585266591, 62312,
        -44606766, 24862794, 255692, -124624, 8, -8,
    ),
    17: (
        2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032,
        -15022392733, 769974566, 15329386299, 642908352, 1347896340,
        -673948170,
    ),
}

# (negative interval, positive interval, radius containing every other root)
CERTIFICATES = {
    9: (("-7.065332", "-7.065330"), ("11.778421", "11.778423"), "6.4"),
    10: (("-9.100143", "-9.100140"), ("14.771097", "14.771100"), "8.3"),
    11: (("-11.712941", "-11.712938"), ("18.535846", "18.535849"), "10.8"),
    12: (("-15.066710", "-15.066707"), ("23.273458", "23.273461"), "14"),
    13: (("-19.369973", "-19.369970"), ("29.237337", "29.237340"), "18"),
    14: (("-24.889363", "-24.889360"), ("36.747375", "36.747378"), "23"),
    15: (("-31.965665", "-31.965662"), ("46.207509", "46.207512"), "30"),
    16: (("-41.034238", "-41.034235"), ("58.127950", "58.127953"), "38"),
    17: (("-52.651061", "-52.651058"), ("73.153328", "73.153331"), "49"),
}


def recurrence_polynomial(coefficients: tuple[int, ...]) -> sp.Poly:
    degree = len(coefficients)
    expression = X**degree - sum(
        coefficient * X ** (degree - index - 1)
        for index, coefficient in enumerate(coefficients)
    )
    return sp.Poly(expression, X, domain=sp.ZZ)


def rational(value: str) -> sp.Rational:
    return sp.Rational(value)


def verify_polynomial(q: int) -> tuple[float, float, int, int]:
    polynomial = recurrence_polynomial(RECURRENCES[q])
    negative, positive, radius_text = CERTIFICATES[q]
    negative_low, negative_high = map(rational, negative)
    positive_low, positive_high = map(rational, positive)
    radius = rational(radius_text)

    assert polynomial.count_roots(negative_low, negative_high) == 1
    assert polynomial.count_roots(positive_low, positive_high) == 1
    assert sp.gcd(polynomial, polynomial.diff()).degree() == 0

    real_intervals = polynomial.intervals(eps=sp.Rational(1, 10**7))
    complex_intervals = dup_isolate_complex_roots_sqf(
        [int(coefficient) for coefficient in polynomial.all_coeffs()],
        sp.ZZ,
        eps=sp.Rational(1, 10**5),
        blackbox=True,
    )

    maximum_other_squared = sp.Rational(0)
    negative_modulus_lower = None
    negative_modulus_upper = None
    positive_root_lower = None

    for (left, right), multiplicity in real_intervals:
        assert multiplicity == 1
        if negative_low < left and right < negative_high:
            negative_modulus_lower = -right
            negative_modulus_upper = -left
        elif positive_low < left and right < positive_high:
            positive_root_lower = left
        else:
            maximum_other_squared = max(
                maximum_other_squared, max(abs(left), abs(right)) ** 2
            )

    for interval in complex_intervals:
        real_bound = max(abs(interval.ax), abs(interval.bx))
        imaginary_bound = max(abs(interval.ay), abs(interval.by))
        maximum_other_squared = max(
            maximum_other_squared, real_bound**2 + imaginary_bound**2
        )

    assert len(real_intervals) + len(complex_intervals) == polynomial.degree()
    assert negative_modulus_lower is not None
    assert negative_modulus_upper is not None
    assert positive_root_lower is not None
    assert maximum_other_squared < radius**2
    assert radius**2 < negative_modulus_lower**2
    assert negative_modulus_upper < positive_root_lower

    maximum_other = sp.sqrt(maximum_other_squared)
    certified_gap = negative_modulus_lower - maximum_other
    return (
        float(maximum_other),
        float(certified_gap),
        len(real_intervals),
        len(complex_intervals),
    )


def main() -> None:
    minimum_gap = float("inf")
    print("q real nonreal max_other certified_gap")
    for q in sorted(RECURRENCES):
        maximum_other, gap, real_count, nonreal_count = verify_polynomial(q)
        minimum_gap = min(minimum_gap, gap)
        print(
            f"{q:2d} {real_count:4d} {nonreal_count:7d} "
            f"{maximum_other:9.6f} {gap:13.6f}"
        )
    print(f"minimum_certified_gap={minimum_gap:.6f}")


if __name__ == "__main__":
    main()
