"""Verify the harmonic weights for multivariate Poisson smoothing.

The checks use two independent descriptions of the iterated radial
Laplacian: a differential recurrence in |y|^2 and the terminating
hypergeometric polynomial in Theorem 6.  They also reduce the beta-sum
weights at orders two and three and recover the one-dimensional Laurent
coefficient at orders one through eight.
"""

from __future__ import annotations

import argparse
import math

import sympy as sp


HALF = sp.Rational(1, 2)


def beta(a: sp.Expr, b: sp.Expr) -> sp.Expr:
    return sp.gamma(a) * sp.gamma(b) / sp.gamma(a + b)


def hypergeometric_polynomial(C: sp.Expr, j: int, x: sp.Symbol) -> sp.Expr:
    return sp.expand(
        sum(
            sp.rf(-j, k)
            * sp.rf(C + j + HALF, k)
            / (sp.rf(C, k) * sp.factorial(k))
            * x**k
            for k in range(j + 1)
        )
    )


def recurrent_radial_numerator(d: int, ell: int, j: int) -> sp.Expr:
    """Numerator after removing (1+s)^(-b-2j) and the factor 4^j."""
    s = sp.Symbol("s")
    C = sp.Rational(d, 2) + ell
    b = C + HALF
    numerator = sp.Integer(1)
    for step in range(j):
        exponent = b + 2 * step
        derivative = sp.diff(numerator, s)
        second = sp.diff(numerator, s, 2)
        numerator = sp.expand(
            s * (1 + s) ** 2 * second
            + (1 + s) * (C * (1 + s) - 2 * exponent * s) * derivative
            + exponent
            * ((exponent + 1) * s - C * (1 + s))
            * numerator
        )
    return sp.factor(numerator)


def theorem_radial_numerator(d: int, ell: int, j: int) -> sp.Expr:
    s = sp.Symbol("s")
    x = sp.Symbol("x")
    C = sp.Rational(d, 2) + ell
    b = C + HALF
    polynomial = hypergeometric_polynomial(C, j, x)
    polynomial = sp.together(polynomial.subs(x, s / (1 + s)))
    return sp.factor(
        (-1) ** j
        * sp.rf(b, j)
        * sp.rf(C, j)
        * (1 + s) ** j
        * polynomial
    )


def harmonic_weight(d: sp.Expr, r: int, j: int) -> sp.Expr:
    ell = r - 2 * j
    C = d / 2 + ell
    a = (d + 1) / 2
    K = (
        sp.Rational(2**r, math.factorial(r))
        * sp.rf(a, ell)
        * sp.rf(C + HALF, j)
        * sp.rf(C, j)
    )
    coefficients = [
        sp.rf(-j, k)
        * sp.rf(C + j + HALF, k)
        / (sp.rf(C, k) * sp.factorial(k))
        for k in range(j + 1)
    ]
    integral = sum(
        coefficients[k]
        * coefficients[m]
        * beta(C + k + m, r + HALF)
        for k in range(j + 1)
        for m in range(j + 1)
    )
    answer = (
        K**2
        * sp.factorial(ell)
        * integral
        / (
            2 ** (ell + 1)
            * sp.rf(d / 2, ell)
            * beta(d / 2, HALF)
        )
    )
    return sp.factor(sp.simplify(sp.expand_func(sp.combsimp(answer))))


def verify_radial_identity() -> None:
    for d in range(1, 8):
        for r in range(1, 9):
            for j in range(r // 2 + 1):
                ell = r - 2 * j
                difference = sp.simplify(
                    recurrent_radial_numerator(d, ell, j)
                    - theorem_radial_numerator(d, ell, j)
                )
                assert difference == 0, (d, r, j, difference)


def verify_closed_weights(inject_error: bool) -> None:
    d = sp.Symbol("d", positive=True)
    expected = {
        (2, 0): 3 * (d + 1) * (d + 3) / (4 * (d + 5) * (d + 7)),
        (2, 1): 3
        * d
        * (d + 1)
        * (7 * d + 9)
        / (4 * (d + 3) * (d + 5) * (d + 7)),
        (3, 0): 5
        * (d + 1)
        * (d + 3)
        * (d + 5)
        / (4 * (d + 7) * (d + 9) * (d + 11)),
        (3, 1): 5
        * (d + 1)
        * (d + 2)
        * (d + 3)
        * (5 * d + 13)
        / (4 * (d + 5) * (d + 7) * (d + 9) * (d + 11)),
    }
    if inject_error:
        expected[(3, 1)] += 1
    for (r, j), closed in expected.items():
        difference = sp.factor(
            sp.simplify(sp.expand_func(harmonic_weight(d, r, j) - closed))
        )
        assert difference == 0, (r, j, difference)


def verify_one_dimensional_reduction() -> None:
    for r in range(1, 9):
        j = r // 2
        expected = sp.Rational(sp.binomial(2 * r - 2, r - 1), 4**r)
        difference = sp.simplify(harmonic_weight(sp.Integer(1), r, j) - expected)
        assert difference == 0, (r, difference)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inject-error",
        action="store_true",
        help="perturb the order-three trace weight to exercise failure detection",
    )
    args = parser.parse_args()

    verify_radial_identity()
    verify_closed_weights(args.inject_error)
    verify_one_dimensional_reduction()
    print("radial identities: d=1..7, r=1..8: PASS")
    print("closed weights: orders 2 and 3: PASS")
    print("one-dimensional reduction: r=1..8: PASS")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
