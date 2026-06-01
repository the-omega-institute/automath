"""Independent exact checks for the displayed algebraic certificates.

The script intentionally recomputes the determinant/resultant and
pseudo-remainder interfaces from the formulas printed in the manuscript.
It is not used as a hidden proof input: successful output is a submission
audit check that the displayed certificates remain synchronized.
"""

from __future__ import annotations

import sympy as sp


lambda_, t, y = sp.symbols("lambda t y")


def assert_equal(name: str, lhs: sp.Expr, rhs: sp.Expr) -> None:
    diff = sp.factor(sp.expand(lhs - rhs))
    if diff != 0:
        raise AssertionError(f"{name} failed: {diff}")
    print(f"ok: {name}")


def check_discriminant_resultant() -> None:
    pi = lambda_**4 - lambda_**3 - (2 * y + 1) * lambda_**2 + lambda_ + y * (y + 1)
    dpi = sp.diff(pi, lambda_)
    resultant = sp.resultant(pi, dpi, lambda_)
    displayed = -256 * y**5 - 155 * y**4 + 246 * y**3 + 133 * y**2 + 32 * y
    factored = -y * (y - 1) * (256 * y**3 + 411 * y**2 + 165 * y + 32)
    assert_equal("lambda-discriminant expanded form", resultant, displayed)
    assert_equal("lambda-discriminant factorization", displayed, factored)


def check_cubic_branch_resultant() -> None:
    p = 16 * lambda_**3 - 9 * lambda_**2 + 1
    q = 4 * lambda_ * y - 4 * lambda_**3 + 3 * lambda_**2 + 2 * lambda_ - 1
    resultant = sp.resultant(p, q, lambda_)
    displayed = -64 * (256 * y**3 + 411 * y**2 + 165 * y + 32)
    assert_equal("cubic branch resultant", resultant, displayed)


def check_minimal_order_resultant() -> None:
    n = 1 + y * t + (y**2 - y - 1) * t**2 + (y**3 - 2 * y) * t**3
    d = 1 - t - (2 * y + 1) * t**2 + t**3 + y * (y + 1) * t**4
    resultant = sp.resultant(n, d, t)
    displayed = y**3 * (y - 1) ** 3 * (y + 1) ** 6
    assert_equal("N-D resultant", resultant, displayed)


def check_opposite_modulus_resultant() -> None:
    x = sp.symbols("x")
    pi_x = x**4 - x**3 - (2 * y + 1) * x**2 + x + y * (y + 1)
    pi_neg_x = pi_x.subs(x, -x)
    resultant = sp.resultant(pi_x, pi_neg_x, x)
    displayed = 16 * y**3 * (y - 1) ** 2 * (y + 1)
    assert_equal("opposite-modulus resultant", resultant, displayed)


def check_sturm_pseudo_remainders() -> None:
    pi = lambda_**4 - lambda_**3 - (2 * y + 1) * lambda_**2 + lambda_ + y * (y + 1)
    s0 = sp.Poly(pi, lambda_, domain=sp.QQ.frac_field(y))
    s1 = sp.Poly(sp.diff(pi, lambda_), lambda_, domain=sp.QQ.frac_field(y))

    s2_expr = ((16 * y + 11) * lambda_**2 + (4 * y - 10) * lambda_ - 16 * y**2 - 16 * y - 1) / 16
    s2 = sp.Poly(s2_expr, lambda_, domain=sp.QQ.frac_field(y))

    numerator_s3 = 4 * lambda_ * y**2 - 68 * lambda_ * y - 8 * lambda_ - 64 * y**3 - 41 * y**2 + 25 * y + 8
    s3_expr = -16 * numerator_s3 / (16 * y + 11) ** 2
    s3 = sp.Poly(s3_expr, lambda_, domain=sp.QQ.frac_field(y))

    s4_expr = -y * (y - 1) * (16 * y + 11) ** 2 * (256 * y**3 + 411 * y**2 + 165 * y + 32) / (
        256 * (y**2 - 17 * y - 2) ** 2
    )
    s4 = sp.Poly(s4_expr, lambda_, domain=sp.QQ.frac_field(y))

    _, rem01 = sp.div(s0, s1)
    _, rem12 = sp.div(s1, s2)
    _, rem23 = sp.div(s2, s3)
    assert_equal("Sturm remainder S0,S1", rem01.as_expr(), -s2.as_expr())
    assert_equal("Sturm remainder S1,S2", rem12.as_expr(), -s3.as_expr())
    assert_equal("Sturm remainder S2,S3", rem23.as_expr(), -s4.as_expr())

    prem01 = sp.Poly(pi, lambda_).prem(sp.Poly(sp.diff(pi, lambda_), lambda_)).as_expr()
    prem12 = sp.Poly(sp.diff(pi, lambda_), lambda_).prem(sp.Poly(16 * s2_expr, lambda_)).as_expr()
    prem23 = sp.Poly(16 * s2_expr, lambda_).prem(sp.Poly(numerator_s3, lambda_)).as_expr()
    assert_equal("primitive pseudo-remainder S0,S1", prem01, -16 * s2_expr)
    assert_equal("primitive pseudo-remainder S1,16S2", prem12, 16 * numerator_s3)
    assert_equal(
        "primitive pseudo-remainder 16S2,S3 numerator",
        prem23,
        y * (y - 1) * (16 * y + 11) ** 2 * (256 * y**3 + 411 * y**2 + 165 * y + 32),
    )


def sign(value: sp.Expr) -> str:
    simplified = sp.simplify(value)
    if simplified > 0:
        return "+"
    if simplified < 0:
        return "-"
    raise AssertionError(f"unexpected zero sign sample: {simplified}")


def sign_variations(signs: tuple[str, ...]) -> int:
    return sum(left != right for left, right in zip(signs, signs[1:]))


def check_positive_axis_sturm_sign_table() -> None:
    c = 256 * y**3 + 411 * y**2 + 165 * y + 32
    leading_minus = (
        sp.Integer(1),
        sp.Integer(-4),
        (16 * y + 11) / 16,
        4 * y**2 - 68 * y - 8,
        -y * (y - 1) * (16 * y + 11) ** 2 * c / (256 * (y**2 - 17 * y - 2) ** 2),
    )
    leading_plus = (
        sp.Integer(1),
        sp.Integer(4),
        (16 * y + 11) / 16,
        -4 * y**2 + 68 * y + 8,
        -y * (y - 1) * (16 * y + 11) ** 2 * c / (256 * (y**2 - 17 * y - 2) ** 2),
    )
    rows = (
        ("0<y<1", sp.Rational(1, 2), ("+", "-", "+", "-", "+"), ("+", "+", "+", "+", "+"), 4),
        ("1<y<y0", sp.Integer(2), ("+", "-", "+", "-", "-"), ("+", "+", "+", "+", "-"), 2),
        ("y>y0", sp.Integer(20), ("+", "-", "+", "+", "-"), ("+", "+", "+", "-", "-"), 2),
    )
    for name, sample, expected_minus, expected_plus, expected_drop in rows:
        actual_minus = tuple(sign(expr.subs(y, sample)) for expr in leading_minus)
        actual_plus = tuple(sign(expr.subs(y, sample)) for expr in leading_plus)
        if actual_minus != expected_minus:
            raise AssertionError(f"{name} signs at -infinity failed: {actual_minus}")
        if actual_plus != expected_plus:
            raise AssertionError(f"{name} signs at +infinity failed: {actual_plus}")
        actual_drop = sign_variations(actual_minus) - sign_variations(actual_plus)
        if actual_drop != expected_drop:
            raise AssertionError(f"{name} variation drop failed: {actual_drop}")
        print(f"ok: positive-axis Sturm sign table {name}")

    y0 = (17 + sp.sqrt(297)) / 2
    assert_equal("positive Euclidean denominator root", y0**2 - 17 * y0 - 2, 0)
    if not (17 < y0 < 18):
        raise AssertionError(f"positive Euclidean denominator root not in (17,18): {y0}")
    if sp.simplify(c.subs(y, y0)) <= 0:
        raise AssertionError("c(y0) is not positive")
    print("ok: positive-axis denominator cell check")


def coefficient(expr: sp.Expr, symbol: sp.Symbol, degree: int) -> sp.Expr:
    return sp.expand(expr).coeff(symbol, degree)


def check_endpoint_branch_coefficient_equations() -> None:
    s, A, B, C, D = sp.symbols("s A B C D")
    pi = lambda_**4 - lambda_**3 - (2 * y + 1) * lambda_**2 + lambda_ + y * (y + 1)

    w = A * s + B * s**2 + C * s**3 + D * s**4
    endpoint_expansion = sp.expand(pi.subs({lambda_: 1 + w, y: s**2}))
    expected_s2 = 2 * A**2 - 1
    expected_s3 = A * (3 * A**2 + 4 * B - 4)
    expected_s4 = A**4 + 9 * A**2 * B - 2 * A**2 + 4 * A * C + 2 * B**2 - 4 * B + 1
    assert_equal("endpoint branch coefficient s^2", coefficient(endpoint_expansion, s, 2), expected_s2)
    assert_equal("endpoint branch coefficient s^3", coefficient(endpoint_expansion, s, 3), expected_s3)
    assert_equal("endpoint branch coefficient s^4", coefficient(endpoint_expansion, s, 4), expected_s4)

    A_value = sp.sqrt(2) / 2
    B_value = sp.Rational(5, 8)
    C_value = -sp.Rational(43, 64) / sp.sqrt(2)
    assert_equal("endpoint A equation", expected_s2.subs(A, A_value), 0)
    assert_equal("endpoint B equation", expected_s3.subs({A: A_value, B: B_value}), 0)
    assert_equal("endpoint C equation", expected_s4.subs({A: A_value, B: B_value, C: C_value}), 0)

    noncolliding_minus_one = pi.subs({lambda_: -1 + A * y}).expand().coeff(y, 1)
    noncolliding_zero = pi.subs({lambda_: A * y}).expand().coeff(y, 1)
    assert_equal("non-colliding branch near -1", noncolliding_minus_one, -4 * A - 1)
    assert_equal("non-colliding branch near 0", noncolliding_zero, A + 1)
    assert_equal("non-colliding coefficient near -1", noncolliding_minus_one.subs(A, -sp.Rational(1, 4)), 0)
    assert_equal("non-colliding coefficient near 0", noncolliding_zero.subs(A, -1), 0)

    B_star, E = sp.symbols("B_star E")
    amplitude_eq_z2 = -2 * sp.sqrt(2) * B_star + 2 * E - sp.Rational(1, 8)
    amplitude_eq_z3 = -3 * sp.sqrt(2) * B_star + 2 * E + sp.Rational(1, 4)
    solution = sp.solve((amplitude_eq_z2, amplitude_eq_z3), (B_star, E), dict=True)[0]
    assert_equal("endpoint amplitude B_*", solution[B_star], 3 * sp.sqrt(2) / 16)
    assert_equal("endpoint amplitude E", solution[E], sp.Rational(7, 16))
    print("ok: endpoint branch coefficient equations")


def main() -> None:
    check_discriminant_resultant()
    check_cubic_branch_resultant()
    check_minimal_order_resultant()
    check_opposite_modulus_resultant()
    check_sturm_pseudo_remainders()
    check_positive_axis_sturm_sign_table()
    check_endpoint_branch_coefficient_equations()
    print("all algebraic certificate checks passed")


if __name__ == "__main__":
    main()
