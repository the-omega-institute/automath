"""Exact Laurent certificate for the N=4 Poisson entropy coefficients.

Run from the paper root with

    python certificates/eighth_order_laurent_certificate.py

The script uses only Python's standard-library rational arithmetic.  It
constructs Q_2,...,Q_6 from the formulas in the manuscript, computes constant
Laurent coefficients by exact convolution, and asserts the two-point sanity
checks for rho_sigma.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


def add_poly(a, b):
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
        if out[exponent] == 0:
            del out[exponent]
    return out


def mul_poly(a, b):
    out = {}
    for exponent_a, coefficient_a in a.items():
        for exponent_b, coefficient_b in b.items():
            exponent = exponent_a + exponent_b
            out[exponent] = out.get(exponent, Fraction(0)) + coefficient_a * coefficient_b
    return {exponent: coefficient for exponent, coefficient in out.items() if coefficient}


def q_even(two_m):
    m = two_m // 2
    scale = Fraction((-1) ** m, 2 ** (2 * m))
    out = {}
    for j in range(2 * m):
        coefficient = scale * comb(2 * m - 1, j)
        out = add_poly(out, {j + 1: coefficient, -(j + 1): coefficient})
    return out


def q_odd(two_m_plus_one):
    # Store coefficients in the real Laurent representative after factoring
    # out 1/i.  Constant terms below use the resulting rational products with
    # the signs already implied by 1/i^2 = -1 for odd-odd products.
    m = (two_m_plus_one - 1) // 2
    scale = Fraction((-1) ** m, 2 ** (2 * m + 1))
    out = {}
    for j in range(2 * m + 1):
        coefficient = scale * comb(2 * m, j)
        out = add_poly(out, {j + 1: coefficient, -(j + 1): -coefficient})
    return out


def q(n):
    if n % 2 == 0:
        return q_even(n)
    return q_odd(n)


Q = {n: q(n) for n in range(2, 7)}


def const_term(indices):
    product = {0: Fraction(1)}
    odd_factor_count = 0
    for n in indices:
        product = mul_poly(product, Q[n])
        if n % 2:
            odd_factor_count += 1
    value = product.get(0, Fraction(0))
    if odd_factor_count % 2:
        if value:
            raise ValueError(f"unexpected nonzero odd-mode constant term in {indices}: {value}")
        return value
    if odd_factor_count % 4 == 2:
        value = -value
    return value


def fmt(frac):
    if frac.denominator == 1:
        return str(frac.numerator)
    return f"{frac.numerator}/{frac.denominator}"


EXPECTED = {
    (2, 2): Fraction(1, 4),
    (2, 4): Fraction(-1, 8),
    (3, 3): Fraction(3, 16),
    (2, 2, 2): Fraction(-3, 32),
    (2, 6): Fraction(3, 64),
    (3, 5): Fraction(-15, 128),
    (4, 4): Fraction(5, 32),
    (2, 2, 4): Fraction(3, 32),
    (2, 3, 3): Fraction(-9, 128),
    (2, 2, 2, 2): Fraction(9, 64),
}

VANISHING = {
    (2, 3): Fraction(0),
    (2, 5): Fraction(0),
    (3, 4): Fraction(0),
    (2, 2, 3): Fraction(0),
}


def a6_two_point():
    # rho_sigma has mu_2=sigma^2, mu_3=mu_5=0, mu_4=sigma^4, mu_6=sigma^6.
    return Fraction(1, 64) + Fraction(-8, 64)


def a8_two_point():
    return Fraction(3, 256) + Fraction(-12, 256) + Fraction(12, 256) + Fraction(20, 256)


def main():
    assert sum(Q[2].values()) == Fraction(-1), "Q_2(1) sanity check failed"
    for indices, expected in EXPECTED.items():
        actual = const_term(indices)
        assert actual == expected, f"I{indices}: expected {expected}, got {actual}"
    for indices, expected in VANISHING.items():
        actual = const_term(indices)
        assert actual == expected, f"I{indices}: expected {expected}, got {actual}"
    assert a6_two_point() == Fraction(-7, 64), "A_6(rho_sigma) sanity check failed"
    assert a8_two_point() == Fraction(23, 256), "A_8(rho_sigma) sanity check failed"

    print("Exact Laurent certificate for Q_2,...,Q_6")
    print("support(Q_j) = {+-1,...,+-j}, 2 <= j <= 6")
    print("I(n_1,...,n_r) = [z^0] prod_j Q_{n_j}")
    for indices in EXPECTED:
        name = "I(" + ",".join(str(n) for n in indices) + ")"
        print(f"{name:18s} = {fmt(const_term(indices))}")
    print("vanishing odd-order checks:")
    for indices in VANISHING:
        name = "I(" + ",".join(str(n) for n in indices) + ")"
        print(f"{name:18s} = {fmt(const_term(indices))}")
    print("Q_2(1) = -1")
    print("A_6(rho_sigma) = -7*sigma^6/64")
    print("A_8(rho_sigma) = 23*sigma^8/256")


if __name__ == "__main__":
    main()
