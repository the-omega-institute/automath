#!/usr/bin/env python3
"""Rigorous certificate for the dyadic/critical speed separation.

All combinatorial sums are integer computations.  Transcendental quantities
are evaluated with ``decimal`` and enclosed by directed rounding.  The zeta
and zeta-derivative enclosures use Euler--Maclaurin through B_16, including
an explicit differentiated periodic-Bernoulli remainder bound.
"""

from __future__ import annotations

import argparse
import sys
from contextlib import redirect_stdout
from dataclasses import dataclass
from decimal import (
    Decimal,
    ROUND_CEILING,
    ROUND_FLOOR,
    ROUND_HALF_EVEN,
    Context,
    localcontext,
)
from fractions import Fraction
from io import StringIO
from math import factorial, gcd
from pathlib import Path

import numpy as np
from numba import njit, prange


PRECISION = 80
N_EM = 32
Q_CUTOFF = 20_000
P_CUTOFF = 7_900
SIGMA_LO = Decimal("2.4787")
SIGMA_HI = Decimal("2.4788")

GAMMA_25 = Fraction(13_180_988_392_373, 2_541_865_828_329)
GAMMA_TAIL = Fraction(126_600_871_936, 2_541_865_828_329)
GAMMA_UPPER = Fraction(4_435_863_088_103, 847_288_609_443)

H_LO_CERT = Decimal("2.588435643856306896")
H_HI_CERT = Decimal("2.589951928201414596")
D_FINITE_LO_CERT = Decimal("19.302273469878911856")
D_FINITE_HI_CERT = Decimal("19.311145544445741772")
D_TAIL_LO_CERT = Decimal("0.434421763138508560")
D_TAIL_HI_CERT = Decimal("347.686170804099215772")
D_LO_CERT = Decimal("19.736695233017420416")
D_HI_CERT = Decimal("366.997316348544957544")
V2_LO_CERT = Decimal("0.132397168057576261")
VC_HI_CERT = Decimal("0.131225207544812100")
SEPARATION_CERT = Decimal("0.001171960512764161")


def _context(rounding: str) -> Context:
    return Context(prec=PRECISION, rounding=rounding)


CTX_DOWN = _context(ROUND_FLOOR)
CTX_UP = _context(ROUND_CEILING)
CTX_NEAR = _context(ROUND_HALF_EVEN)


@dataclass(frozen=True)
class Interval:
    lo: Decimal
    hi: Decimal

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")


@dataclass(frozen=True)
class SpeedCertificate:
    sigma_lower: Decimal
    sigma_upper: Decimal
    gamma_upper: Decimal
    h_upper: Decimal
    d_lower: Decimal
    v2_lower: Decimal
    vc_upper: Decimal
    speed_gap_lower: Decimal


def point(value: Decimal | int | str) -> Interval:
    value = value if isinstance(value, Decimal) else Decimal(value)
    return Interval(value, value)


def rational(numerator: int, denominator: int = 1) -> Interval:
    return Interval(
        CTX_DOWN.divide(Decimal(numerator), Decimal(denominator)),
        CTX_UP.divide(Decimal(numerator), Decimal(denominator)),
    )


def add(left: Interval, right: Interval) -> Interval:
    return Interval(
        CTX_DOWN.add(left.lo, right.lo),
        CTX_UP.add(left.hi, right.hi),
    )


def neg(value: Interval) -> Interval:
    return Interval(-value.hi, -value.lo)


def sub(left: Interval, right: Interval) -> Interval:
    return add(left, neg(right))


def mul(left: Interval, right: Interval) -> Interval:
    products_down = [
        CTX_DOWN.multiply(a, b)
        for a in (left.lo, left.hi)
        for b in (right.lo, right.hi)
    ]
    products_up = [
        CTX_UP.multiply(a, b)
        for a in (left.lo, left.hi)
        for b in (right.lo, right.hi)
    ]
    return Interval(min(products_down), max(products_up))


def div(left: Interval, right: Interval) -> Interval:
    if right.lo <= 0 <= right.hi:
        raise ZeroDivisionError("interval denominator contains zero")
    quotients_down = [
        CTX_DOWN.divide(a, b)
        for a in (left.lo, left.hi)
        for b in (right.lo, right.hi)
    ]
    quotients_up = [
        CTX_UP.divide(a, b)
        for a in (left.lo, left.hi)
        for b in (right.lo, right.hi)
    ]
    return Interval(min(quotients_down), max(quotients_up))


def abs_upper(value: Interval) -> Decimal:
    return max(abs(value.lo), abs(value.hi))


def decimal_ln(value: Decimal) -> Interval:
    with localcontext(CTX_NEAR) as context:
        result = value.ln(context=context)
        return Interval(result.next_minus(context), result.next_plus(context))


def interval_exp(value: Interval) -> Interval:
    with localcontext(CTX_NEAR) as context:
        lower = value.lo.exp(context=context).next_minus(context)
        upper = value.hi.exp(context=context).next_plus(context)
    return Interval(lower, upper)


def decimal_power(base: int, exponent: Interval) -> Interval:
    return interval_exp(mul(exponent, decimal_ln(Decimal(base))))


def rising(value: Interval, length: int) -> Interval:
    result = point(1)
    for offset in range(length):
        result = mul(result, add(value, point(offset)))
    return result


def rising_derivative(value: Interval, length: int) -> Interval:
    product = rising(value, length)
    reciprocal_sum = point(0)
    for offset in range(length):
        reciprocal_sum = add(
            reciprocal_sum, div(point(1), add(value, point(offset)))
        )
    return mul(product, reciprocal_sum)


def integer_power(value: Interval, exponent: int) -> Interval:
    result = point(1)
    for _ in range(exponent):
        result = mul(result, value)
    return result


BERNOULLI = {
    2: Fraction(1, 6),
    4: Fraction(-1, 30),
    6: Fraction(1, 42),
    8: Fraction(-1, 30),
    10: Fraction(5, 66),
    12: Fraction(-691, 2730),
    14: Fraction(7, 6),
    16: Fraction(-3617, 510),
}


def zeta_and_derivative(sigma: Decimal) -> tuple[Interval, Interval]:
    """Enclose zeta(sigma) and zeta'(sigma), for sigma > 1."""
    s = point(sigma)
    value = point(0)
    derivative = point(0)

    for integer in range(1, N_EM):
        power = decimal_power(integer, neg(s))
        log_integer = decimal_ln(Decimal(integer)) if integer > 1 else point(0)
        value = add(value, power)
        derivative = sub(derivative, mul(log_integer, power))

    log_n = decimal_ln(Decimal(N_EM))
    s_minus_one = sub(s, point(1))
    n_one_minus_s = decimal_power(N_EM, sub(point(1), s))
    integral_term = div(n_one_minus_s, s_minus_one)
    value = add(value, integral_term)
    derivative = sub(
        derivative,
        mul(
            n_one_minus_s,
            add(div(log_n, s_minus_one), div(point(1), mul(s_minus_one, s_minus_one))),
        ),
    )

    n_minus_s = decimal_power(N_EM, neg(s))
    value = add(value, mul(rational(1, 2), n_minus_s))
    derivative = sub(derivative, mul(rational(1, 2), mul(log_n, n_minus_s)))

    for order in range(2, 17, 2):
        coefficient = BERNOULLI[order] / factorial(order)
        coefficient_i = rational(coefficient.numerator, coefficient.denominator)
        product = rising(s, order - 1)
        product_prime = rising_derivative(s, order - 1)
        power = decimal_power(N_EM, sub(point(1 - order), s))
        value = add(value, mul(coefficient_i, mul(product, power)))
        derivative = add(
            derivative,
            mul(
                coefficient_i,
                mul(power, sub(product_prime, mul(product, log_n))),
            ),
        )

    absolute_b16 = rational(abs(BERNOULLI[16].numerator), BERNOULLI[16].denominator)
    factorial_16 = point(factorial(16))
    prefactor = div(absolute_b16, factorial_16)
    product_16 = rising(s, 16)
    product_16_prime = rising_derivative(s, 16)
    tail_power = decimal_power(N_EM, sub(point(-15), s))
    s_plus_15 = add(s, point(15))
    integral_zero = div(tail_power, s_plus_15)
    integral_log = mul(
        tail_power,
        add(div(log_n, s_plus_15), div(point(1), mul(s_plus_15, s_plus_15))),
    )
    remainder = mul(prefactor, mul(product_16, integral_zero))
    derivative_remainder = mul(
        prefactor,
        add(mul(product_16_prime, integral_zero), mul(product_16, integral_log)),
    )
    value_error = abs_upper(remainder)
    derivative_error = abs_upper(derivative_remainder)
    value = Interval(
        CTX_DOWN.subtract(value.lo, value_error),
        CTX_UP.add(value.hi, value_error),
    )
    derivative = Interval(
        CTX_DOWN.subtract(derivative.lo, derivative_error),
        CTX_UP.add(derivative.hi, derivative_error),
    )
    return value, derivative


def ratio_minus_two(sigma: Decimal) -> Interval:
    zeta_lower, _ = zeta_and_derivative(sigma - 1)
    zeta_upper, _ = zeta_and_derivative(sigma)
    return sub(div(zeta_lower, zeta_upper), point(2))


def totient_dirichlet_log_moment(sigma: Decimal) -> Interval:
    """Enclose -d/ds (zeta(s-1)/zeta(s)) at sigma."""
    zeta_lower, derivative_lower = zeta_and_derivative(sigma - 1)
    zeta_upper, derivative_upper = zeta_and_derivative(sigma)
    numerator = sub(
        mul(zeta_lower, derivative_upper),
        mul(derivative_lower, zeta_upper),
    )
    return div(numerator, mul(zeta_upper, zeta_upper))


@njit
def integer_gcd(left: int, right: int) -> int:
    while right:
        left, right = right, left % right
    return left


@njit(parallel=True)
def fixed_denominator_costs(max_denominator: int) -> np.ndarray:
    """Return C(q) exactly for 0 <= q <= max_denominator."""
    costs = np.zeros(max_denominator + 1, dtype=np.int64)
    for denominator in prange(2, max_denominator + 1):
        total = 0
        for numerator in range(1, denominator):
            if integer_gcd(numerator, denominator) != 1:
                continue
            left, right = denominator, numerator
            digit_sum = 0
            while right:
                digit_sum += left // right
                left, right = right, left % right
            total += 2 * digit_sum - 1
        costs[denominator] = total
    return costs


@njit(parallel=True)
def dyadic_cost(exponent: int) -> int:
    denominator = 1 << exponent
    total = 0
    for index in prange(denominator // 2):
        numerator = 2 * index + 1
        left, right = denominator, numerator
        digit_sum = 0
        while right:
            digit_sum += left // right
            left, right = right, left % right
        total += 2 * digit_sum - 1
    return total


def totients_through(limit: int) -> np.ndarray:
    values = np.arange(limit + 1, dtype=np.int64)
    values[1] = 1
    for prime in range(2, limit + 1):
        if values[prime] == prime:
            values[prime::prime] -= values[prime::prime] // prime
    return values


def finite_d_interval(costs: np.ndarray) -> Interval:
    lower = point(0)
    upper = point(0)
    for denominator in range(2, Q_CUTOFF + 1):
        lower = add(
            lower,
            mul(point(int(costs[denominator])), decimal_power(denominator, point(-SIGMA_HI))),
        )
        upper = add(
            upper,
            mul(point(int(costs[denominator])), decimal_power(denominator, point(-SIGMA_LO))),
        )
    return Interval(lower.lo, upper.hi)


def lower_d_tail(
    q_cutoff: int = Q_CUTOFF,
    p_cutoff: int = P_CUTOFF,
    sigma_upper: Decimal = SIGMA_HI,
) -> Interval:
    """Selected symmetric residues, integrated block by block."""
    phi = totients_through(p_cutoff)
    sigma = point(sigma_upper)
    total = point(0)
    for numerator in range(1, p_cutoff + 1):
        start = q_cutoff + numerator
        first = mul(
            div(point(4), mul(point(numerator), sub(sigma, point(2)))),
            decimal_power(start, sub(point(2), sigma)),
        )
        second = mul(
            div(point(6), sub(sigma, point(1))),
            decimal_power(start, sub(point(1), sigma)),
        )
        integral = sub(first, second)
        total = add(
            total,
            mul(rational(int(phi[numerator]), numerator), integral),
        )
    return total


def upper_d_tail() -> Interval:
    """Integral-test upper bound for q > Q_CUTOFF."""
    sigma = point(SIGMA_LO)
    delta = sub(sigma, point(2))
    log_q = decimal_ln(Decimal(Q_CUTOFF))
    q_one_minus_sigma = decimal_power(Q_CUTOFF, sub(point(1), sigma))
    polynomial = add(
        point(9), mul(point(8), integer_power(add(point(1), log_q), 3))
    )
    first_term = mul(q_one_minus_sigma, polynomial)

    exponential = decimal_power(Q_CUTOFF, neg(delta))
    integral_polynomial = point(0)
    coefficients = (17, 24, 24, 8)
    for degree, coefficient in enumerate(coefficients):
        degree_integral = point(0)
        for index in range(degree + 1):
            falling = factorial(degree) // factorial(degree - index)
            delta_power = integer_power(delta, index + 1)
            log_power = integer_power(log_q, degree - index)
            degree_integral = add(
                degree_integral,
                mul(point(falling), div(log_power, delta_power)),
            )
        integral_polynomial = add(
            integral_polynomial, mul(point(coefficient), degree_integral)
        )
    integral = mul(exponential, integral_polynomial)
    return add(first_term, integral)


def fraction_to_interval(value: Fraction) -> Interval:
    return rational(value.numerator, value.denominator)


def decimal_string(value: Decimal, places: int = 24) -> str:
    quantum = Decimal(1).scaleb(-places)
    with localcontext(CTX_NEAR):
        return str(value.quantize(quantum))


def dyadic_gamma_certificate() -> tuple[Fraction, Fraction, Fraction]:
    """Return the exact finite part, analytic tail, and resulting upper bound."""
    return GAMMA_25, GAMMA_TAIL, GAMMA_UPPER


def _regular_digit_sum(numerator: int, denominator: int) -> int:
    total = 0
    left, right = denominator, numerator
    while right:
        quotient, remainder = divmod(left, right)
        total += quotient
        left, right = right, remainder
    return total


def verify_complete_block_identity(max_denominator: int = 250) -> None:
    """Audit the exact block count and symmetric continued-fraction costs."""
    if max_denominator < 2:
        raise ValueError("max_denominator must be at least two")
    phi = totients_through(max_denominator)
    for modulus in range(1, max_denominator + 1):
        for block_index in range(3):
            start = block_index * modulus + 1
            coprime_count = sum(
                gcd(value, modulus) == 1
                for value in range(start, start + modulus)
            )
            if coprime_count != int(phi[modulus]):
                raise AssertionError(
                    f"complete-block identity failed for modulus {modulus}"
                )

    for denominator in range(3, max_denominator + 1):
        for numerator in range(1, (denominator + 1) // 2):
            if gcd(numerator, denominator) != 1:
                continue
            left = _regular_digit_sum(numerator, denominator)
            right = _regular_digit_sum(denominator - numerator, denominator)
            if left != right:
                raise AssertionError(
                    "symmetric cost identity failed for "
                    f"{numerator}/{denominator}"
                )
            if 4 * left - 2 < Fraction(4 * denominator, numerator) - 6:
                raise AssertionError(
                    f"symmetric cost lower bound failed for {numerator}/{denominator}"
                )


def _refined_root_interval(iterations: int = 18) -> Interval:
    lower = SIGMA_LO
    upper = SIGMA_HI
    for _ in range(iterations):
        midpoint = (lower + upper) / 2
        sign = ratio_minus_two(midpoint)
        if sign.lo > 0:
            lower = midpoint
        elif sign.hi < 0:
            upper = midpoint
        else:
            raise ArithmeticError("root sign interval contains zero")
    return Interval(lower, upper)


def build_certificate() -> SpeedCertificate:
    """Build a tighter certificate used by the regression-test interface."""
    sigma = _refined_root_interval()
    gamma_upper_i = fraction_to_interval(GAMMA_UPPER)
    v2_lower = div(decimal_ln(Decimal(2)), gamma_upper_i).lo
    h_upper = totient_dirichlet_log_moment(sigma.lo).hi

    extended_cutoff = 40_000
    costs = fixed_denominator_costs(extended_cutoff)
    d_finite = point(0)
    for denominator in range(2, extended_cutoff + 1):
        d_finite = add(
            d_finite,
            mul(
                point(int(costs[denominator])),
                decimal_power(denominator, point(-sigma.hi)),
            ),
        )
    d_tail = lower_d_tail(
        q_cutoff=extended_cutoff,
        p_cutoff=P_CUTOFF,
        sigma_upper=sigma.hi,
    )
    d_lower = CTX_DOWN.add(d_finite.lo, d_tail.lo)
    vc_upper = CTX_UP.divide(h_upper, d_lower)
    speed_gap = CTX_DOWN.subtract(v2_lower, vc_upper)
    return SpeedCertificate(
        sigma_lower=sigma.lo,
        sigma_upper=sigma.hi,
        gamma_upper=gamma_upper_i.hi,
        h_upper=h_upper,
        d_lower=d_lower,
        v2_lower=v2_lower,
        vc_upper=vc_upper,
        speed_gap_lower=speed_gap,
    )


def _run_verification() -> int:
    failures: list[str] = []

    dyadic_values = [dyadic_cost(exponent) for exponent in range(1, 26)]
    gamma_25 = sum(
        (Fraction(value, 3 ** (exponent + 1)) for exponent, value in enumerate(dyadic_values, 1)),
        Fraction(0),
    )
    if gamma_25 != GAMMA_25:
        failures.append("dyadic finite sum")

    exact_tail = sum(
        (
            Fraction(1, 3)
            * Fraction(2, 3) ** exponent
            * (
                Fraction(17, 2)
                + 16 * (1 + Fraction(7 * exponent, 20)) ** 2
            )
            for exponent in range(26, 500)
        ),
        Fraction(0),
    )
    # Close the geometrically weighted quadratic tail symbolically.
    ratio = Fraction(2, 3)
    start = 26
    sum_0 = ratio**start / (1 - ratio)
    sum_1 = ratio**start * (start - (start - 1) * ratio) / (1 - ratio) ** 2
    sum_2 = ratio**start * (
        start**2
        + (-2 * start**2 + 2 * start + 1) * ratio
        + (start - 1) ** 2 * ratio**2
    ) / (1 - ratio) ** 3
    closed_tail = Fraction(1, 3) * (
        Fraction(49, 25) * sum_2 + Fraction(56, 5) * sum_1 + Fraction(49, 2) * sum_0
    )
    if closed_tail != GAMMA_TAIL or GAMMA_25 + GAMMA_TAIL != GAMMA_UPPER:
        failures.append("dyadic rational tail")
    if exact_tail >= closed_tail:
        # The finite truncation must be strictly below the infinite closed tail.
        failures.append("dyadic tail sanity check")

    gamma_upper_i = fraction_to_interval(GAMMA_UPPER)
    log_two = decimal_ln(Decimal(2))
    v2_lower = div(log_two, gamma_upper_i).lo
    if v2_lower < V2_LO_CERT:
        failures.append("v2 lower endpoint")

    root_left = ratio_minus_two(SIGMA_LO)
    root_right = ratio_minus_two(SIGMA_HI)
    if root_left.lo <= 0 or root_right.hi >= 0:
        failures.append("critical root bracket")

    h_at_lo = totient_dirichlet_log_moment(SIGMA_LO)
    h_at_hi = totient_dirichlet_log_moment(SIGMA_HI)
    h_interval = Interval(h_at_hi.lo, h_at_lo.hi)
    if h_interval.lo < H_LO_CERT or h_interval.hi > H_HI_CERT:
        failures.append("critical H interval")

    costs = fixed_denominator_costs(Q_CUTOFF)
    finite_d = finite_d_interval(costs)
    if finite_d.lo < D_FINITE_LO_CERT or finite_d.hi > D_FINITE_HI_CERT:
        failures.append("finite D interval")

    lower_tail = lower_d_tail()
    upper_tail = upper_d_tail()
    if lower_tail.lo < D_TAIL_LO_CERT:
        failures.append("D lower tail")
    if upper_tail.hi > D_TAIL_HI_CERT:
        failures.append("D upper tail")

    d_interval = Interval(
        CTX_DOWN.add(D_FINITE_LO_CERT, D_TAIL_LO_CERT),
        CTX_UP.add(D_FINITE_HI_CERT, D_TAIL_HI_CERT),
    )
    if d_interval.lo != D_LO_CERT or d_interval.hi != D_HI_CERT:
        failures.append("stated D interval arithmetic")

    vc_upper = CTX_UP.divide(H_HI_CERT, D_LO_CERT)
    if vc_upper > VC_HI_CERT:
        failures.append("vc upper endpoint")
    separation = CTX_DOWN.subtract(V2_LO_CERT, VC_HI_CERT)
    if separation < SEPARATION_CERT or separation <= 0:
        failures.append("strict speed separation")

    print("STRICT SPEED SEPARATION VERIFICATION")
    print(f"dyadic_exact_exponents=1..25 gamma_25={GAMMA_25}")
    print(f"gamma_tail_upper={GAMMA_TAIL} gamma_upper={GAMMA_UPPER}")
    print(f"v2_lower={decimal_string(v2_lower, 24)}")
    print(
        "root_signs="
        f"[{root_left.lo},{root_left.hi}] "
        f"[{root_right.lo},{root_right.hi}]"
    )
    print(f"H_enclosure=[{h_interval.lo},{h_interval.hi}]")
    print(f"finite_D_enclosure=[{finite_d.lo},{finite_d.hi}]")
    print(f"tail_D_lower={lower_tail.lo} tail_D_upper={upper_tail.hi}")
    print(f"D_certificate=[{D_LO_CERT},{D_HI_CERT}]")
    print(f"vc_upper={decimal_string(vc_upper, 24)}")
    print(f"speed_gap_lower={decimal_string(separation, 24)}")
    print(f"failures={failures}")
    if failures:
        print("STATUS: FAIL")
        return 1
    print("STATUS: PASS")
    return 0


def main(argv=()) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.output is None:
        return _run_verification()

    capture = StringIO()
    with redirect_stdout(capture):
        status = _run_verification()
    report = capture.getvalue()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="ascii", newline="\n")
    print(report, end="")
    return status


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
