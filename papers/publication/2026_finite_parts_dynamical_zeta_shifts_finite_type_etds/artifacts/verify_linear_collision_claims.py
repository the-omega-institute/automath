"""Exact finite checks for the linear collision claims.

These computations are sanity checks only.  The manuscript proofs use divisor
duality, Rolle's theorem, Mahler lifting, and exact Fourier inversion.
"""

from __future__ import annotations

from itertools import product

import sympy as sp


z = sp.Symbol("z")


def _reduced_degrees(value: sp.Expr) -> tuple[int, int]:
    numerator, denominator = sp.fraction(sp.cancel(value))
    return sp.degree(numerator, z), sp.degree(denominator, z)


def _squarefree_degree(poly: sp.Expr) -> int:
    polynomial = sp.Poly(poly, z, domain=sp.QQ)
    return sp.degree(polynomial.sqf_part())


def squarefree_mahler_audit() -> dict[str, object]:
    roots = (sp.Rational(1, 2), sp.Integer(1), -sp.Integer(1), sp.Rational(-1, 2))
    checked = 0
    minimum_slack = None

    for p in range(2, 6):
        for exponents in product(range(-2, 3), repeat=len(roots)):
            if not any(exponents):
                continue
            divisor = {
                root: exponent
                for root, exponent in zip(roots, exponents)
                if exponent
            }
            degree = 0
            for root, order in divisor.items():
                degree += abs(divisor.get(root**p, 0) - p * order)
            for target, order in divisor.items():
                internal_preimages = sum(root**p == target for root in divisor)
                degree += (p - internal_preimages) * abs(order)
            support = len(divisor)
            slack = degree - 2 * (p - 1) * support
            assert slack >= 0, (p, exponents, degree, support)
            minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
            checked += 1

    sharp_cases = 0
    for p in range(2, 6):
        for q in range(1, 7):
            certificate = 1 - z**q
            mahler_input = sp.cancel(
                certificate.subs(z, z**p) / certificate**p
            )
            degree = sum(_reduced_degrees(mahler_input))
            assert degree == 2 * (p - 1) * q
            assert _squarefree_degree(certificate) == q
            sharp_cases += 1

    return {
        "certificates_checked": checked,
        "radices": (2, 3, 4, 5),
        "minimum_slack": minimum_slack,
        "sharp_cases": sharp_cases,
    }


def _order_at_zero(poly: sp.Expr) -> int:
    polynomial = sp.Poly(sp.expand(poly), z, domain=sp.QQ)
    return min(monomial[0] for monomial, coefficient in polynomial.terms() if coefficient)


def collision_jet_audit() -> dict[str, object]:
    positive_rational_cases = 0
    maximum_collisions = 0

    factors = (1 + z, 1 + 2 * z, 1 + 3 * z)
    for exponents in product(range(-2, 3), repeat=len(factors)):
        if not any(exponents):
            continue
        numerator = sp.Integer(1)
        denominator = sp.Integer(1)
        for factor, exponent in zip(factors, exponents):
            if exponent > 0:
                numerator *= factor**exponent
            elif exponent < 0:
                denominator *= factor ** (-exponent)
        numerator = sp.expand(numerator)
        denominator = sp.expand(denominator)
        collision = sp.Poly(numerator - denominator, z, domain=sp.QQ)
        nu = _order_at_zero(collision.as_expr())
        reduced_collision = sp.Poly(
            collision.as_expr() / z**nu, z, domain=sp.QQ
        ).sqf_part()
        collisions = int(reduced_collision.count_roots(0, 1))
        support = sum(exponent != 0 for exponent in exponents)
        assert collisions + nu <= support, (exponents, collisions, nu, support)
        maximum_collisions = max(maximum_collisions, collisions)
        positive_rational_cases += 1

    equality_cases = 0
    for nu in range(1, 5):
        for radii in (
            (sp.Rational(1, 4),),
            (sp.Rational(1, 5), sp.Rational(2, 5)),
            (sp.Rational(1, 6), sp.Rational(1, 3), sp.Rational(1, 2)),
        ):
            collision_factor = z**nu
            for radius in radii:
                collision_factor *= z - radius
            coefficient_bound = sum(
                abs(coefficient)
                for coefficient in sp.Poly(collision_factor, z).all_coeffs()
            )
            epsilon = sp.Rational(1, 2 * coefficient_bound + 1)
            certificate = sp.expand(1 + epsilon * collision_factor)
            # On [0,1], |collision_factor| is at most the coefficient l1 norm.
            assert 1 - epsilon * coefficient_bound > 0
            support = _squarefree_degree(certificate)
            assert len(radii) + nu <= support
            for radius in radii:
                assert certificate.subs(z, radius) == 1
            equality_cases += 1

    return {
        "positive_rational_cases": positive_rational_cases,
        "maximum_open_interval_collisions": maximum_collisions,
        "constructed_collision_cases": equality_cases,
    }


def _odd_prime_instance(ell: int, m: int) -> None:
    a = ell**ell
    scale = 4 * ell**2
    stages = [a * (scale * (m + 1) + i) for i in range(1, m + 1)]
    q = 2 * m + 1
    size = ell * q

    c_matrix = sp.zeros(q)
    for i, stage in enumerate(stages, start=1):
        c_matrix[i - 1, i] = -a
        c_matrix[i - 1, m + i] = stage
        c_matrix[m + i, i] = stage
    c_matrix[m, 0] = -a

    staged_product = sp.Integer(1)
    for stage in stages:
        staged_product *= -a * z + stage**2 * z**2
    q_poly = sp.expand(1 + a * z * staged_product)
    assert sp.expand(c_matrix.charpoly(z).as_expr().subs(z, 1 / z) * z**q) == q_poly

    blocks = [[sp.zeros(q) for _ in range(ell)] for _ in range(ell)]
    blocks[0][1] = c_matrix / ell ** (ell - 1)
    for j in range(1, ell - 1):
        blocks[j][j + 1] = ell * sp.eye(q)
    blocks[ell - 1][0] = ell * sp.eye(q)
    first = sp.Matrix.vstack(
        *(sp.Matrix.hstack(*row) for row in blocks)
    )
    second = sp.diag(*([c_matrix] * ell))
    assert all(entry.q == 1 and entry % ell == 0 for entry in first)
    assert all(entry % ell == 0 for entry in second)
    assert sp.expand(first.charpoly(z).as_expr().subs(z, 1 / z) * z**size) == sp.expand(
        q_poly.subs(z, z**ell)
    )
    assert sp.expand(second.charpoly(z).as_expr().subs(z, 1 / z) * z**size) == sp.expand(
        q_poly**ell
    )

    s_value = ell * stages[-1]
    base = s_value * sp.ones(size)
    for twisted in (first, second):
        label_zero = (base + (ell - 1) * twisted) / ell
        label_nonzero = (base - twisted) / ell
        assert all(entry.q == 1 and entry >= 0 for entry in label_zero)
        assert all(entry.q == 1 and entry >= 0 for entry in label_nonzero)
        assert label_zero + (ell - 1) * label_nonzero == base
        assert label_zero - label_nonzero == twisted
        assert max(abs(entry) for entry in twisted) < s_value

    perron_root = s_value * size
    for stage in stages:
        radius = sp.Rational(a, stage**2)
        assert 0 < radius < sp.Rational(1, perron_root)
        assert q_poly.subs(z, radius) == 1

    first_degree = m + 1
    leading = (-1) ** m * a ** (m + 1)
    assert sp.Poly(q_poly - 1, z).nth(first_degree) == leading
    trace_difference = sp.trace(first**first_degree) - sp.trace(second**first_degree)
    assert trace_difference == ell * first_degree * leading


def odd_prime_realization_audit() -> dict[str, object]:
    instances = ((3, 1), (3, 2), (5, 1))
    for ell, m in instances:
        _odd_prime_instance(ell, m)
    return {"instances": instances, "instances_checked": len(instances)}


def render_report() -> str:
    squarefree = squarefree_mahler_audit()
    collision = collision_jet_audit()
    odd_prime = odd_prime_realization_audit()
    return "\n".join(
        (
            "LINEAR COLLISION CLAIM VERIFICATION",
            f"Squarefree certificates checked: {squarefree['certificates_checked']}",
            f"Squarefree sharp cases checked: {squarefree['sharp_cases']}",
            f"Minimum squarefree-bound slack: {squarefree['minimum_slack']}",
            f"Positive rational collision cases checked: {collision['positive_rational_cases']}",
            f"Constructed collision cases checked: {collision['constructed_collision_cases']}",
            f"Odd-prime matrix instances checked: {odd_prime['instances_checked']}",
            "STATUS: PASS",
            "",
        )
    )


if __name__ == "__main__":
    print(render_report(), end="")
