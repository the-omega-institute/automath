"""Exact Laurent certificate for the N=4 Poisson entropy coefficients.

The manuscript displays the coefficient vectors, deterministic convolution
recurrence, and zero-sum convolution sums used in the proof.  This paper-local
script is an exact-rational reproducibility check for those displayed finite
data; it is not an additional mathematical hypothesis.

Run from the paper root with

    python certificates/eighth_order_laurent_certificate.py

The script uses only Python's standard-library rational arithmetic.  It
constructs Q_2,...,Q_6 from the formulas in the manuscript, checks the exact
Laurent coefficient vectors, computes every zero-sum convolution row through
order eight, and asserts the two-point sanity checks for rho_sigma.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Dict, Iterable, List, Tuple


QI = Tuple[Fraction, Fraction]
Poly = Dict[int, QI]
Row = Tuple[int, ...]

ZERO: QI = (Fraction(0), Fraction(0))
ONE: QI = (Fraction(1), Fraction(0))
I: QI = (Fraction(0), Fraction(1))


def qi_add(a: QI, b: QI) -> QI:
    return (a[0] + b[0], a[1] + b[1])


def qi_neg(a: QI) -> QI:
    return (-a[0], -a[1])


def qi_mul(a: QI, b: QI) -> QI:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def qi_scale(a: QI, c: Fraction) -> QI:
    return (a[0] * c, a[1] * c)


def qi_is_zero(a: QI) -> bool:
    return a == ZERO


def add_poly(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = qi_add(out.get(exponent, ZERO), coefficient)
        if qi_is_zero(out[exponent]):
            del out[exponent]
    return out


def mul_poly(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for exponent_a, coefficient_a in a.items():
        for exponent_b, coefficient_b in b.items():
            exponent = exponent_a + exponent_b
            out[exponent] = qi_add(
                out.get(exponent, ZERO), qi_mul(coefficient_a, coefficient_b)
            )
    return {exponent: coefficient for exponent, coefficient in out.items() if not qi_is_zero(coefficient)}


def q_even(two_m: int) -> Poly:
    m = two_m // 2
    scale = Fraction((-1) ** m, 2 ** (2 * m))
    out: Poly = {}
    for j in range(2 * m):
        coefficient = scale * comb(2 * m - 1, j)
        out = add_poly(out, {j + 1: (coefficient, Fraction(0)), -(j + 1): (coefficient, Fraction(0))})
    return out


def q_odd(two_m_plus_one: int) -> Poly:
    m = (two_m_plus_one - 1) // 2
    scale = qi_scale(qi_neg(I), Fraction((-1) ** m, 2 ** (2 * m + 1)))
    out: Poly = {}
    for j in range(2 * m + 1):
        coefficient = qi_scale(scale, Fraction(comb(2 * m, j)))
        out = add_poly(out, {j + 1: coefficient, -(j + 1): qi_neg(coefficient)})
    return out


def q(n: int) -> Poly:
    if n % 2 == 0:
        return q_even(n)
    return q_odd(n)


Q = {n: q(n) for n in range(2, 7)}


def const_term(indices: Row) -> QI:
    product = {0: ONE}
    for n in indices:
        product = mul_poly(product, Q[n])
    return product.get(0, ZERO)


def lambda_n(n: int) -> QI:
    if n % 2 == 0:
        return (Fraction((-1) ** (n // 2), 2**n), Fraction(0))
    m = (n - 1) // 2
    return qi_scale(qi_neg(I), Fraction((-1) ** m, 2**n))


def epsilon(n: int, k: int) -> int:
    if n % 2 == 0:
        return 1
    return 1 if k > 0 else -1


def zero_sum_tuples(indices: Row) -> List[Tuple[int, ...]]:
    tuples: List[Tuple[int, ...]] = []

    def rec(pos: int, current: List[int], total: int) -> None:
        if pos == len(indices):
            if total == 0:
                tuples.append(tuple(current))
            return
        n = indices[pos]
        for k in range(-n, n + 1):
            if k == 0:
                continue
            current.append(k)
            rec(pos + 1, current, total + k)
            current.pop()

    rec(0, [], 0)
    return tuples


def signed_integer_sum(indices: Row) -> int:
    total = 0
    for ks in zero_sum_tuples(indices):
        term = 1
        for n, k in zip(indices, ks):
            term *= epsilon(n, k) * comb(n - 1, abs(k) - 1)
        total += term
    return total


def scalar_product(indices: Row) -> QI:
    out = ONE
    for n in indices:
        out = qi_mul(out, lambda_n(n))
    return out


def fmt_fraction(frac: Fraction) -> str:
    if frac.denominator == 1:
        return str(frac.numerator)
    return f"{frac.numerator}/{frac.denominator}"


def fmt_qi(value: QI) -> str:
    re, im = value
    if im == 0:
        return fmt_fraction(re)
    if re == 0:
        if im == 1:
            return "i"
        if im == -1:
            return "-i"
        return f"{fmt_fraction(im)}i"
    sign = "+" if im > 0 else "-"
    return f"{fmt_fraction(re)}{sign}{fmt_fraction(abs(im))}i"


EXPECTED_POSITIVE_COEFFICIENTS = {
    2: [(-Fraction(1, 4), Fraction(0)), (-Fraction(1, 4), Fraction(0))],
    3: [(Fraction(0), Fraction(1, 8)), (Fraction(0), Fraction(1, 4)), (Fraction(0), Fraction(1, 8))],
    4: [(Fraction(1, 16), Fraction(0)), (Fraction(3, 16), Fraction(0)), (Fraction(3, 16), Fraction(0)), (Fraction(1, 16), Fraction(0))],
    5: [(Fraction(0), -Fraction(1, 32)), (Fraction(0), -Fraction(1, 8)), (Fraction(0), -Fraction(3, 16)), (Fraction(0), -Fraction(1, 8)), (Fraction(0), -Fraction(1, 32))],
    6: [(-Fraction(1, 64), Fraction(0)), (-Fraction(5, 64), Fraction(0)), (-Fraction(5, 32), Fraction(0)), (-Fraction(5, 32), Fraction(0)), (-Fraction(5, 64), Fraction(0)), (-Fraction(1, 64), Fraction(0))],
}

EXPECTED_ROWS = {
    (2, 2): (4, 4, (Fraction(1, 16), Fraction(0)), (Fraction(1, 4), Fraction(0))),
    (2, 3): (4, 0, (Fraction(0), -Fraction(1, 32)), ZERO),
    (2, 4): (4, 8, (-Fraction(1, 64), Fraction(0)), (-Fraction(1, 8), Fraction(0))),
    (3, 3): (6, -12, (-Fraction(1, 64), Fraction(0)), (Fraction(3, 16), Fraction(0))),
    (2, 2, 2): (6, 6, (-Fraction(1, 64), Fraction(0)), (-Fraction(3, 32), Fraction(0))),
    (2, 5): (4, 0, (Fraction(0), Fraction(1, 128)), ZERO),
    (3, 4): (6, 0, (Fraction(0), Fraction(1, 128)), ZERO),
    (2, 2, 3): (10, 0, (Fraction(0), Fraction(1, 128)), ZERO),
    (2, 6): (4, 12, (Fraction(1, 256), Fraction(0)), (Fraction(3, 64), Fraction(0))),
    (3, 5): (6, -30, (Fraction(1, 256), Fraction(0)), (-Fraction(15, 128), Fraction(0))),
    (4, 4): (8, 40, (Fraction(1, 256), Fraction(0)), (Fraction(5, 32), Fraction(0))),
    (2, 2, 4): (12, 24, (Fraction(1, 256), Fraction(0)), (Fraction(3, 32), Fraction(0))),
    (2, 3, 3): (14, -18, (Fraction(1, 256), Fraction(0)), (-Fraction(9, 128), Fraction(0))),
    (2, 2, 2, 2): (36, 36, (Fraction(1, 256), Fraction(0)), (Fraction(9, 64), Fraction(0))),
}


def a6_two_point() -> Fraction:
    # rho_sigma has mu_2=sigma^2, mu_3=mu_5=0, mu_4=sigma^4, mu_6=sigma^6.
    return Fraction(1, 64) + Fraction(-8, 64)


def a8_two_point() -> Fraction:
    return Fraction(3, 256) + Fraction(-12, 256) + Fraction(12, 256) + Fraction(20, 256)


Monomial = Tuple[int, int, int, int, int]
Polynomial = Dict[Monomial, Fraction]


def poly_term(coefficient: Fraction, exponents: Monomial) -> Polynomial:
    return {} if coefficient == 0 else {exponents: coefficient}


def poly_add(*polynomials: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            out[monomial] = out.get(monomial, Fraction(0)) + coefficient
            if out[monomial] == 0:
                del out[monomial]
    return out


def poly_scale(polynomial: Polynomial, scalar: Fraction) -> Polynomial:
    return {
        monomial: coefficient * scalar
        for monomial, coefficient in polynomial.items()
        if coefficient * scalar != 0
    }


def const_fraction(indices: Row) -> Fraction:
    value = const_term(indices)
    assert value[1] == 0, f"I{indices} is not real: {fmt_qi(value)}"
    return value[0]


def coefficient_polynomials() -> Tuple[Polynomial, Polynomial, Polynomial]:
    m2_2 = (2, 0, 0, 0, 0)
    m2_3 = (3, 0, 0, 0, 0)
    m3_2 = (0, 2, 0, 0, 0)
    m2_m4 = (1, 0, 1, 0, 0)
    m2_4 = (4, 0, 0, 0, 0)
    m2_2_m4 = (2, 0, 1, 0, 0)
    m2_m3_2 = (1, 2, 0, 0, 0)
    m2_m6 = (1, 0, 0, 0, 1)
    m3_m5 = (0, 1, 0, 1, 0)
    m4_2 = (0, 0, 2, 0, 0)

    a4 = poly_term(Fraction(1, 2) * const_fraction((2, 2)), m2_2)
    a6 = poly_add(
        poly_term(const_fraction((2, 4)), m2_m4),
        poly_term(Fraction(1, 2) * const_fraction((3, 3)), m3_2),
        poly_term(-Fraction(1, 6) * const_fraction((2, 2, 2)), m2_3),
    )
    a8 = poly_add(
        poly_term(const_fraction((2, 6)), m2_m6),
        poly_term(const_fraction((3, 5)), m3_m5),
        poly_term(Fraction(1, 2) * const_fraction((4, 4)), m4_2),
        poly_term(-Fraction(1, 2) * const_fraction((2, 2, 4)), m2_2_m4),
        poly_term(-Fraction(1, 2) * const_fraction((2, 3, 3)), m2_m3_2),
        poly_term(Fraction(1, 12) * const_fraction((2, 2, 2, 2)), m2_4),
    )
    return a4, a6, a8


def assert_coefficient_polynomials() -> None:
    a4, a6, a8 = coefficient_polynomials()
    assert a4 == {(2, 0, 0, 0, 0): Fraction(1, 8)}, f"A_4 mismatch: {a4}"
    assert a6 == {
        (3, 0, 0, 0, 0): Fraction(1, 64),
        (0, 2, 0, 0, 0): Fraction(6, 64),
        (1, 0, 1, 0, 0): Fraction(-8, 64),
    }, f"A_6 mismatch: {a6}"
    assert a8 == {
        (4, 0, 0, 0, 0): Fraction(3, 256),
        (2, 0, 1, 0, 0): Fraction(-12, 256),
        (1, 2, 0, 0, 0): Fraction(9, 256),
        (1, 0, 0, 0, 1): Fraction(12, 256),
        (0, 1, 0, 1, 0): Fraction(-30, 256),
        (0, 0, 2, 0, 0): Fraction(20, 256),
    }, f"A_8 mismatch: {a8}"


def assert_coefficient_vectors() -> None:
    for n, expected in EXPECTED_POSITIVE_COEFFICIENTS.items():
        actual = [Q[n][k] for k in range(1, n + 1)]
        assert actual == expected, f"positive vector Q_{n}: expected {expected}, got {actual}"
        for k in range(1, n + 1):
            if n % 2 == 0:
                assert Q[n][-k] == Q[n][k], f"even symmetry failed for Q_{n}, k={k}"
            else:
                assert Q[n][-k] == qi_neg(Q[n][k]), f"odd antisymmetry failed for Q_{n}, k={k}"


def assert_rows() -> None:
    for indices, expected in EXPECTED_ROWS.items():
        expected_count, expected_signed_sum, expected_scalar, expected_constant = expected
        actual_count = len(zero_sum_tuples(indices))
        actual_signed_sum = signed_integer_sum(indices)
        actual_scalar = scalar_product(indices)
        actual_constant = const_term(indices)
        reconstructed = qi_scale(actual_scalar, Fraction(actual_signed_sum))
        assert actual_count == expected_count, f"K{indices}: expected {expected_count}, got {actual_count}"
        assert actual_signed_sum == expected_signed_sum, (
            f"signed sum {indices}: expected {expected_signed_sum}, got {actual_signed_sum}"
        )
        assert actual_scalar == expected_scalar, f"lambda product {indices}: expected {expected_scalar}, got {actual_scalar}"
        assert reconstructed == expected_constant, (
            f"reconstructed I{indices}: expected {expected_constant}, got {reconstructed}"
        )
        assert actual_constant == expected_constant, f"I{indices}: expected {expected_constant}, got {actual_constant}"


def fmt_row(indices: Iterable[int]) -> str:
    return "(" + ",".join(str(n) for n in indices) + ")"


def main() -> None:
    assert_coefficient_vectors()
    assert_rows()
    assert_coefficient_polynomials()
    assert sum((c[0] for c in Q[2].values()), Fraction(0)) == Fraction(-1), "Q_2(1) sanity check failed"
    assert all(c[1] == 0 for c in Q[2].values()), "Q_2 has unexpected imaginary coefficients"
    assert a6_two_point() == Fraction(-7, 64), "A_6(rho_sigma) sanity check failed"
    assert a8_two_point() == Fraction(23, 256), "A_8(rho_sigma) sanity check failed"

    print("Exact Laurent certificate for Q_2,...,Q_6")
    print("support(Q_j) = {+-1,...,+-j}, 2 <= j <= 6")
    print("positive coefficient vectors q_{n,1},...,q_{n,n}:")
    for n in range(2, 7):
        vector = ", ".join(fmt_qi(Q[n][k]) for k in range(1, n + 1))
        extension = "q_{n,-k}=q_{n,k}" if n % 2 == 0 else "q_{n,-k}=-q_{n,k}"
        print(f"Q_{n}: ({vector}); {extension}")
    print("I(n_1,...,n_r) = [z^0] prod_j Q_{n_j}")
    print("row: |K|, signed zero-sum binomial convolution, lambda product, constant term")
    for indices, (count, signed_sum, scalar, _) in EXPECTED_ROWS.items():
        name = "I" + fmt_row(indices)
        print(
            f"{name:18s}: |K|={count:2d}, sum={signed_sum:3d}, "
            f"lambda={fmt_qi(scalar):>7s}, I={fmt_qi(const_term(indices))}"
        )
    print("Q_2(1) = -1")
    print("A_4 = mu2^2/8; A_6 = (mu2^3 + 6*mu3^2 - 8*mu2*mu4)/64; "
          "A_8 = (3*mu2^4 - 12*mu2^2*mu4 + 9*mu2*mu3^2 + "
          "12*mu2*mu6 - 30*mu3*mu5 + 20*mu4^2)/256")
    print("A_6(rho_sigma) = -7*sigma^6/64")
    print("A_8(rho_sigma) = 23*sigma^8/256")


if __name__ == "__main__":
    main()
