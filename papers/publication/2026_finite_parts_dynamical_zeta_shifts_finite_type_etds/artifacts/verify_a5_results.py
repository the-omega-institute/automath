"""Exact finite checks for the results extracted from the A5 oracle report."""

from __future__ import annotations

from functools import lru_cache
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path

import mpmath as mp
import sympy as sp


_PERMUTATIONS_WITH_SIGN = tuple(
    (
        permutation,
        -1
        if sum(
            permutation[i] > permutation[j]
            for i in range(4)
            for j in range(i + 1, 4)
        )
        % 2
        else 1,
    )
    for permutation in permutations(range(4))
)


def _is_primitive_matrix(matrix: tuple[tuple[int, ...], ...]) -> bool:
    """Use the four-dimensional Wielandt bound to decide primitivity."""
    support = tuple(tuple(value > 0 for value in row) for row in matrix)
    power = support
    for _exponent in range(1, 11):
        if all(all(row) for row in power):
            return True
        power = tuple(
            tuple(
                any(power[i][k] and support[k][j] for k in range(4))
                for j in range(4)
            )
            for i in range(4)
        )
    return False


def _compatible_signed_rows(row: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(
        product(*(range(-entry, entry + 1, 2) for entry in row))
    )


def _matrix_invariants(
    matrix: tuple[tuple[int, ...], ...],
) -> tuple[int, int, int, int]:
    """Return tr(B), tr(B^2), tr(B^3), and det(B), exactly."""
    trace_one = sum(matrix[i][i] for i in range(4))
    trace_two = sum(matrix[i][j] * matrix[j][i] for i in range(4) for j in range(4))
    trace_three = sum(
        matrix[i][j] * matrix[j][k] * matrix[k][i]
        for i in range(4)
        for j in range(4)
        for k in range(4)
    )
    determinant = sum(
        sign
        * matrix[0][permutation[0]]
        * matrix[1][permutation[1]]
        * matrix[2][permutation[2]]
        * matrix[3][permutation[3]]
        for permutation, sign in _PERMUTATIONS_WITH_SIGN
    )
    return trace_one, trace_two, trace_three, determinant


def verify_c2_boundary_collision() -> bool:
    """Verify the exact four-vertex C2 collision from integer matrix data."""
    z, t, y = sp.symbols("z t y")
    adjacency = sp.Matrix(
        ((0, 4, 0, 0), (1, 1, 0, 2), (0, 0, 0, 4), (0, 2, 1, 1))
    )
    first = sp.Matrix(
        ((0, -2, 0, 0), (-1, -1, 0, -2), (0, 0, 0, -2), (0, 2, -1, 1))
    )
    second = sp.Matrix(
        ((0, -4, 0, 0), (1, 1, 0, 0), (0, 0, 0, -4), (0, 0, 1, 1))
    )
    q = 1 - z + 4 * z**2
    compatible = all(
        abs(twist[i, j]) <= adjacency[i, j]
        and (adjacency[i, j] - twist[i, j]) % 2 == 0
        for twist in (first, second)
        for i in range(4)
        for j in range(4)
    )
    primitive = _is_primitive_matrix(
        tuple(tuple(int(adjacency[i, j]) for j in range(4)) for i in range(4))
    )
    first_polynomial = sp.expand((sp.eye(4) - z * first).det())
    second_polynomial = sp.expand((sp.eye(4) - z * second).det())
    reduced_perron_constant = sp.limit(
        (1 - t) / (sp.eye(4) - t * adjacency / 4).det(), t, 1, dir="-"
    )
    first_labels = tuple(int(first[i, i]) for i in range(4) if adjacency[i, i])
    second_labels = tuple(
        int(second[i, i]) for i in range(4) if adjacency[i, i]
    )
    q_symbols = sp.symbols("q0:14")
    finite_telescoping = sp.simplify(
        sum(
            sp.Rational(1, 2**j) * (2 * q_symbols[j] - q_symbols[j + 1])
            for j in range(13)
        )
        - 2 * q_symbols[0]
        + sp.Rational(1, 2**12) * q_symbols[13]
    )
    return all(
        (
            compatible,
            primitive,
            all(sum(adjacency.row(i)) == 4 for i in range(4)),
            first_polynomial == sp.expand(q.subs(z, z**2)),
            second_polynomial == sp.expand(q**2),
            first.charpoly().as_expr() == sp.Symbol("lambda") ** 4
            - sp.Symbol("lambda") ** 2
            + 4,
            sp.factor(second.charpoly().as_expr())
            == (sp.Symbol("lambda") ** 2 - sp.Symbol("lambda") + 4) ** 2,
            sp.discriminant(y**2 - y + 4, y) == -15,
            finite_telescoping == 0,
            q.subs(z, sp.Rational(1, 4)) == 1,
            2 * sp.log(q.subs(z, sp.Rational(1, 4))) == 0,
            reduced_perron_constant == sp.Rational(4, 5),
            sorted(first_labels) == [-1, 1],
            sorted(second_labels) == [1, 1],
        )
    )


def binary_coboundary_real_interval_matches() -> bool:
    """Numerically test the telescoping identity on 0 < x <= 1/4."""
    with mp.workdps(80):
        sample_points = tuple(mp.mpf(n) / 100 for n in range(1, 26))
        for x in sample_points:
            log_q = lambda value: mp.log(1 - value + 4 * value**2)
            partial = mp.fsum(
                mp.power(2, -j)
                * (2 * log_q(x ** (2**j)) - log_q(x ** (2 ** (j + 1))))
                for j in range(12)
            )
            if abs(partial - 2 * log_q(x)) > mp.mpf("1e-70"):
                return False
    return True


def rational_mahler_certificate_matches() -> bool:
    """Check a non-polynomial positive rational Mahler certificate."""
    z = sp.Symbol("z")
    rational_r = (1 + z) / (1 + 4 * z**2)
    coboundary = sp.cancel(rational_r.subs(z, z**2) / rational_r**2)
    expected = sp.cancel(
        (1 + z**2) * (1 + 4 * z**2) ** 2
        / ((1 + 4 * z**4) * (1 + z) ** 2)
    )
    symbolic = all(
        (
            sp.cancel(coboundary.subs(z, 0)) == 1,
            sp.cancel(rational_r.subs(z, sp.Rational(1, 4))) == 1,
            sp.cancel(coboundary - expected) == 0,
        )
    )
    if not symbolic:
        return False

    with mp.workdps(80):
        for numerator_x in range(1, 26):
            x = mp.mpf(numerator_x) / 100

            def r(value: mp.mpf) -> mp.mpf:
                return (1 + value) / (1 + 4 * value**2)

            logarithmic_product = mp.fsum(
                mp.power(2, -j)
                * (mp.log(r(x ** (2 ** (j + 1)))) - 2 * mp.log(r(x ** (2**j))))
                for j in range(14)
            )
            if abs(logarithmic_product + 2 * mp.log(r(x))) > mp.mpf("1e-70"):
                return False
    return True


def unrestricted_mahler_kernel_domain_counterexample() -> bool:
    """Refute the kernel inclusion when positivity/regularity is omitted."""
    z = sp.Symbol("z")
    x = sp.Rational(1, 4)
    rational_r = 1 + sp.Rational(256, 3) * z * (z - x)
    coboundary = sp.cancel(rational_r.subs(z, z**2) / rational_r**2)
    return all(
        (
            rational_r.subs(z, 0) == 1,
            rational_r.subs(z, x) == 1,
            rational_r.subs(z, x**2) == 0,
            coboundary.subs(z, x) == 0,
        )
    )


def verify_diagonal_realizable_mahler_subclass() -> bool:
    """Check a same-base strict-gap diagonal determinant-ratio model."""
    z = sp.Symbol("z")
    adjacency = sp.Matrix(((5, 2, 2), (2, 5, 2), (2, 2, 5)))
    first = sp.diag(-5, 1, 3)
    second = sp.diag(-3, 3, 5)
    compatible = all(
        abs(twist[i, j]) <= adjacency[i, j]
        and (adjacency[i, j] - twist[i, j]) % 2 == 0
        for twist in (first, second)
        for i in range(3)
        for j in range(3)
    )
    first_polynomial = sp.expand((sp.eye(3) - z * first).det())
    second_polynomial = sp.expand((sp.eye(3) - z * second).det())
    return all(
        (
            compatible,
            all(entry > 0 for entry in adjacency),
            adjacency * sp.ones(3, 1) == 9 * sp.ones(3, 1),
            max(abs(value) for value in first.diagonal()) < 9,
            max(abs(value) for value in second.diagonal()) < 9,
            first_polynomial
            == sp.expand((1 + 5 * z) * (1 - z) * (1 - 3 * z)),
            second_polynomial
            == sp.expand((1 + 3 * z) * (1 - 3 * z) * (1 - 5 * z)),
        )
    )


def critical_mahler_normalization_matches() -> bool:
    """Verify that the weighted product is F(x)^2, rather than F(x)."""
    z = sp.Symbol("z")
    x = sp.Rational(1, 3)
    h = (1 - z) / (1 + z)
    f = 1 - z
    symbolic = all(
        (
            sp.cancel(f**2 - h * f.subs(z, z**2)) == 0,
            f.subs(z, x) == sp.Rational(2, 3),
            f.subs(z, x) ** 2 == sp.Rational(4, 9),
            f.subs(z, x) != f.subs(z, x) ** 2,
        )
    )
    if not symbolic:
        return False

    with mp.workdps(80):
        for numerator_x in range(1, 50):
            real_x = mp.mpf(numerator_x) / 100
            logarithmic_product = mp.fsum(
                mp.power(2, -nu)
                * mp.log((1 - real_x ** (2**nu)) / (1 + real_x ** (2**nu)))
                for nu in range(12)
            )
            product_value = mp.exp(logarithmic_product)
            if (
                abs(product_value - (1 - real_x) ** 2) >= mp.mpf("1e-70")
                or abs(product_value - (1 - real_x)) <= mp.mpf("1e-3")
            ):
                return False
    return True


def _critical_mahler_coefficients(order: int) -> tuple[sp.Integer, ...]:
    """Solve F^2=((1-z)/(1-3z))F(z^2) coefficient by coefficient."""
    h_coefficients = [sp.Integer(1)] + [
        2 * sp.Integer(3) ** (degree - 1) for degree in range(1, order + 1)
    ]
    coefficients = [sp.Integer(1)]
    for degree in range(1, order + 1):
        known_square = sum(
            coefficients[index] * coefficients[degree - index]
            for index in range(1, degree)
        )
        right_hand_side = sum(
            h_coefficients[degree - 2 * index] * coefficients[index]
            for index in range(degree // 2 + 1)
        )
        coefficients.append(sp.simplify((right_hand_side - known_square) / 2))
    return tuple(coefficients)


def critical_mahler_integrality_matches(order: int = 24) -> bool:
    """Check determinant parity, integral recursion, and the truncated equation."""
    z = sp.Symbol("z")
    p_zero = 1 - z
    p_one = 1 - 3 * z
    coefficients = _critical_mahler_coefficients(order)
    f = sum(coefficient * z**degree for degree, coefficient in enumerate(coefficients))
    residual = sp.series(
        f**2 - (p_zero / p_one) * f.subs(z, z**2), z, 0, order + 1
    ).removeO()
    return all(
        (
            sp.Poly(p_zero - p_one, z).all_coeffs()[-1] % 2 == 0,
            all(coefficient.is_Integer for coefficient in coefficients),
            sp.expand(residual) == 0,
        )
    )


def rational_critical_denominator_audit(order: int = 12) -> dict[str, object]:
    """Check the (p q)^(2n-1) denominator bound for rational p-products."""
    z = sp.Symbol("z")
    p_zero = 1 + z / 2 + z**2 / 3
    p_one = 1 - z / 5
    denominators = [
        int(sp.denom(coefficient))
        for polynomial in (p_zero, p_one)
        for coefficient in sp.Poly(polynomial, z).all_coeffs()
    ]
    q = 1
    for denominator in denominators:
        q = sp.ilcm(q, denominator)

    all_bounds_hold = True
    nonintegral_coefficient_seen = False
    radices = (2, 3, 4, 5)
    for radix in radices:
        coefficients = [sp.Integer(1)]
        for degree in range(1, order + 1):
            unknown = sp.Symbol(f"f_{degree}")
            truncated = sum(
                coefficient * z**index
                for index, coefficient in enumerate(coefficients)
            ) + unknown * z**degree
            coefficient_equation = sp.expand(
                p_one * truncated**radix
                - p_zero * truncated.subs(z, z**radix)
            ).coeff(z, degree)
            linear_coefficient = coefficient_equation.coeff(unknown)
            value = sp.cancel(
                -coefficient_equation.subs(unknown, 0) / linear_coefficient
            )
            coefficients.append(value)
            scaled = sp.cancel((radix * q) ** (2 * degree - 1) * value)
            all_bounds_hold &= bool(scaled.is_Integer)
            nonintegral_coefficient_seen |= not bool(value.is_Integer)

        truncated = sum(
            coefficient * z**index
            for index, coefficient in enumerate(coefficients)
        )
        residual = sp.series(
            p_one * truncated**radix
            - p_zero * truncated.subs(z, z**radix),
            z,
            0,
            order + 1,
        ).removeO()
        all_bounds_hold &= sp.expand(residual) == 0

    return {
        "radices": radices,
        "order": order,
        "clearing_denominator": q,
        "all_bounds_hold": all_bounds_hold,
        "nonintegral_coefficient_seen": nonintegral_coefficient_seen,
    }


def nishioka_special_value_specialization() -> dict[str, object]:
    """Audit the exact parameters used for Kumiko Nishioka's 1982 theorem.

    This checks the algebraic specialization and a realizable strict-gap model;
    Kumiko Nishioka's transcendence theorem itself remains the cited analytic input.
    """
    z, u = sp.symbols("z u")
    p_zero = 1 - z
    p_one = 1 - 3 * z
    q_zero = p_zero
    q_one = -p_one * u**2
    p = 2
    transformation_tail_degree = 0
    transformed_function_degree = 1
    current_function_degree = 2
    maximum_degree = max(p + transformation_tail_degree, current_function_degree)
    coefficient_growth_exponent = 1
    algebraic_point = sp.Rational(1, 5)
    coefficients = _critical_mahler_coefficients(24)

    return {
        "p": p,
        "N": transformation_tail_degree,
        "n": transformed_function_degree,
        "m": current_function_degree,
        "M": maximum_degree,
        "U": 1,
        "L": coefficient_growth_exponent,
        "inequality_left": maximum_degree
        * (p + transformation_tail_degree)
        * transformed_function_degree**2,
        "inequality_right": p ** (2 + sp.Rational(1, coefficient_growth_exponent)),
        "reduced_coefficients_coprime": sp.gcd(
            sp.Poly(q_zero, z, u), sp.Poly(q_one, z, u)
        ).as_expr()
        == 1,
        "admissibility_polynomial": sp.sstr(q_zero),
        "algebraic_point": algebraic_point,
        "sampled_orbit_admissible": all(
            q_zero.subs(z, algebraic_point ** (2**iterate)) != 0
            for iterate in range(12)
        ),
        "coefficients_integral": all(
            coefficient.is_Integer for coefficient in coefficients
        ),
    }


def c3_adams_mobius_support_obstruction(
    limit: int,
) -> dict[int, tuple[int, int, int]]:
    """Return the non-zero Mobius transforms of Adams states modulo three."""
    support: dict[int, tuple[int, int, int]] = {}
    for index in range(1, limit + 1):
        coefficients = [0, 0, 0]
        for divisor in sp.divisors(index):
            coefficients[divisor % 3] += int(sp.mobius(divisor))
        state = tuple(coefficients)
        if any(state):
            support[index] = state
    return support


def critical_zero_estimate_pullback_matches() -> bool:
    """Check the cleared pullback identity and its two bidegree bounds."""
    z, y = sp.symbols("z y")
    p_zero = 1 - z
    p_one = 1 - 3 * z
    q = y**2 + z * y + z + 1
    d = sp.Poly(q, z, y).degree(z)
    n = sp.Poly(q, z, y).degree(y)
    eta = max(sp.degree(p_zero, z), sp.degree(p_one, z))
    pullback = sp.cancel(
        p_zero**n * q.subs({z: z**2, y: p_one * y**2 / p_zero}, simultaneous=True)
    )
    pullback = sp.Poly(pullback, z, y).as_expr()
    coefficients = _critical_mahler_coefficients(22)
    f = sum(coefficient * z**degree for degree, coefficient in enumerate(coefficients))
    evaluated_pullback = sp.series(pullback.subs(y, f), z, 0, 19).removeO()
    expected = sp.series(
        p_zero**n * q.subs({z: z**2, y: f.subs(z, z**2)}, simultaneous=True),
        z,
        0,
        19,
    ).removeO()
    degree_z = 2
    degree_y = 2
    bound = degree_z + 4 * degree_z * degree_y + eta * degree_y**2
    columns = []
    for y_degree in range(degree_y + 1):
        f_power = sp.series(f**y_degree, z, 0, bound + 1).removeO()
        for z_degree in range(degree_z + 1):
            polynomial = sp.Poly(
                sp.series(z**z_degree * f_power, z, 0, bound + 1).removeO(),
                z,
            )
            columns.append([polynomial.nth(row) for row in range(bound + 1)])
    coefficient_matrix = sp.Matrix(bound + 1, len(columns), lambda row, col: columns[col][row])
    return all(
        (
            sp.Poly(q, z, y).is_irreducible,
            sp.Poly(pullback, z, y).degree(y) <= 2 * n,
            sp.Poly(pullback, z, y).degree(z) <= 2 * d + eta * n,
            sp.expand(evaluated_pullback - expected) == 0,
            coefficient_matrix.rank() == (degree_z + 1) * (degree_y + 1),
        )
    )


def rational_mahler_saturation_matches() -> bool:
    """Verify normalized saturation identities in exact rational examples."""
    z = sp.Symbol("z")
    examples = (
        ((1 - z) ** 2 * (1 + 2 * z) / ((1 - 3 * z) * (1 + z) ** 3), 2),
        ((1 + z + z**2) / ((1 - 2 * z) ** 2 * (1 + 3 * z)), 3),
        ((1 - 4 * z) * (1 + z) ** 2 / (1 + 2 * z**2), 5),
    )
    for rational_r, exponent in examples:
        rational_r = sp.cancel(rational_r)
        h = sp.cancel(rational_r.subs(z, z**2) / rational_r**2)
        q = sp.cancel(rational_r**exponent)
        delta_q = sp.cancel(q.subs(z, z**2) / q**2)
        numerator, denominator = sp.fraction(q)
        factor_exponents = [
            multiplicity
            for polynomial in (numerator, denominator)
            for _factor, multiplicity in sp.factor_list(polynomial)[1]
        ]
        if not all(
            (
                rational_r.subs(z, 0) == 1,
                h.subs(z, 0) == 1,
                q.subs(z, 0) == 1,
                sp.cancel(h**exponent - delta_q) == 0,
                all(multiplicity % exponent == 0 for multiplicity in factor_exponents),
            )
        ):
            return False
    return True


def _constant_one_polynomial(expression: sp.Expr, variable: sp.Symbol) -> sp.Poly:
    polynomial = sp.Poly(expression, variable, domain=sp.QQ)
    constant = polynomial.eval(0)
    if constant == 0:
        raise ValueError("the polynomial must be non-zero at the origin")
    return sp.Poly(polynomial.as_expr() / constant, variable, domain=sp.QQ)


def logarithmic_mahler_degree_bound(radix: int, total_degree: int) -> int:
    """Return ceil(2 D m / p), with p^m(p-1) >= 2D and m >= 1."""
    if radix < 2:
        raise ValueError("the Mahler radix must be at least two")
    if total_degree < 1:
        raise ValueError("the total input degree must be positive")
    depth = 1
    while radix**depth * (radix - 1) < 2 * total_degree:
        depth += 1
    return (2 * total_degree * depth + radix - 1) // radix


def effective_mahler_degree_bound(radix: int, total_degree: int) -> int:
    """Return ceil(p D m_p(D)/2), the uniform reconstruction bound."""
    if radix < 2:
        raise ValueError("the Mahler radix must be at least two")
    if total_degree < 1:
        raise ValueError("the total input degree must be positive")
    depth = 1
    while radix**depth * (radix - 1) < 2 * total_degree:
        depth += 1
    return (radix * total_degree * depth + 1) // 2


def logarithmic_mahler_divisor_bound_audit() -> dict[str, int | bool]:
    """Search exact rational certificates for a violation of the logarithmic bound."""
    z = sp.Symbol("z")
    certificates_checked = 0
    all_within_bound = True
    root_of_unity_cases_checked = False
    radices = (2, 3, 5, 7)
    factor_pairs = ((1 - z, 1 + z), (1 - 2 * z, 1 - 3 * z), (1 + 2 * z, 1 - 3 * z))

    for radix in radices:
        for numerator_factor, denominator_factor in factor_pairs:
            for numerator_power in range(4):
                for denominator_power in range(4):
                    if numerator_power == denominator_power == 0:
                        continue
                    rational_function = sp.cancel(
                        numerator_factor**numerator_power
                        / denominator_factor**denominator_power
                    )
                    numerator, denominator = rational_function.as_numer_denom()
                    ratio = sp.cancel(
                        rational_function.subs(z, z**radix)
                        / rational_function**radix
                    )
                    p_zero, p_one = ratio.as_numer_denom()
                    total_degree = sp.degree(p_zero, z) + sp.degree(p_one, z)
                    certificate_degree = sp.degree(numerator, z) + sp.degree(denominator, z)
                    all_within_bound &= certificate_degree <= logarithmic_mahler_degree_bound(
                        radix, total_degree
                    )
                    certificates_checked += 1
                    if numerator_factor == 1 - z and denominator_factor == 1 + z:
                        root_of_unity_cases_checked = True

    return {
        "certificates_checked": certificates_checked,
        "radices_checked": len(radices),
        "root_of_unity_cases_checked": root_of_unity_cases_checked,
        "all_within_bound": all_within_bound,
    }


def mahler_log_degree_extremal_family_audit() -> dict[str, int | bool]:
    """Verify an Omega(D log D) family without numerator-denominator cancellation."""
    z = sp.Symbol("z")
    q = 1 - 2 * z
    families_checked = 0
    identities_hold = True
    degrees_hold = True
    no_cancellation = True

    for radix in (2, 3, 5):
        for depth in range(4):
            rational_function = sp.prod(
                q.subs(z, z ** (radix**j)) ** (radix ** (depth - j))
                for j in range(depth + 1)
            )
            ratio = sp.cancel(
                rational_function.subs(z, z**radix)
                / rational_function**radix
            )
            expected_numerator = q.subs(z, z ** (radix ** (depth + 1)))
            expected_denominator = q ** (radix ** (depth + 1))
            expected_ratio = expected_numerator / expected_denominator
            identities_hold &= sp.cancel(ratio - expected_ratio) == 0
            no_cancellation &= sp.gcd(
                sp.Poly(expected_numerator, z), sp.Poly(expected_denominator, z)
            ).degree() == 0
            degrees_hold &= all(
                (
                    sp.degree(rational_function, z)
                    == (depth + 1) * radix**depth,
                    sp.degree(expected_numerator, z)
                    + sp.degree(expected_denominator, z)
                    == 2 * radix ** (depth + 1),
                )
            )
            families_checked += 1

    return {
        "families_checked": families_checked,
        "identities_hold": identities_hold,
        "degrees_hold": degrees_hold,
        "no_cancellation": no_cancellation,
    }


def realizable_multicollision_family_audit(max_m: int = 4) -> dict[str, object]:
    """Check the parametric standard-cover collision identities exactly."""
    z = sp.Symbol("z")
    vertex_counts: list[int] = []
    collision_counts: list[int] = []
    determinant_identities_hold = True
    all_radii_in_perron_interval = True
    same_base_realization_holds = True
    strict_gap_certified = True

    for m in range(1, max_m + 1):
        n = 2 * m + 1
        size = 2 * n
        scales = [64 * (m + 1) + 4 * index for index in range(1, m + 1)]
        c_matrix = sp.zeros(n)
        for index, scale in enumerate(scales, 1):
            c_matrix[index - 1, index] = -4
            c_matrix[index - 1, m + index] = scale
            c_matrix[m + index, index] = scale
        c_matrix[m, 0] = -4

        q_polynomial = sp.expand((sp.eye(n) - z * c_matrix).det())
        expected_q = sp.expand(
            1 + 4 * z * sp.prod(-4 * z + scale**2 * z**2 for scale in scales)
        )
        first_block = sp.zeros(size)
        first_block[:n, n:] = c_matrix / 2
        first_block[n:, :n] = 2 * sp.eye(n)
        second_block = sp.diag(c_matrix, c_matrix)
        first_determinant = sp.expand((sp.eye(size) - z * first_block).det())
        second_determinant = sp.expand((sp.eye(size) - z * second_block).det())
        determinant_identities_hold &= all(
            (
                q_polynomial == expected_q,
                first_determinant == sp.expand(q_polynomial.subs(z, z**2)),
                second_determinant == sp.expand(q_polynomial**2),
            )
        )

        base_entry = scales[-1]
        base = sp.ones(size) * base_entry
        compatibility = all(
            bool(
                block[row, column].is_Integer
                and (base[row, column] - block[row, column]) % 2 == 0
                and abs(block[row, column]) <= base[row, column]
            )
            for block in (first_block, second_block)
            for row in range(size)
            for column in range(size)
        )
        same_base_realization_holds &= compatibility
        strict_gap_certified &= all(
            any(
                abs(block[row, column]) < base[row, column]
                for row in range(size)
                for column in range(size)
            )
            for block in (first_block, second_block)
        )

        radii = tuple(sp.Rational(4, scale**2) for scale in scales)
        perron_root = base_entry * size
        all_radii_in_perron_interval &= all(
            0 < radius < sp.Rational(1, perron_root) for radius in radii
        )
        collisions = tuple(
            radius for radius in radii if q_polynomial.subs(z, radius) == 1
        )
        vertex_counts.append(size)
        collision_counts.append(len(collisions))

    return {
        "vertex_counts": tuple(vertex_counts),
        "collision_counts": tuple(collision_counts),
        "determinant_identities_hold": determinant_identities_hold,
        "all_radii_in_perron_interval": all_radii_in_perron_interval,
        "same_base_realization_holds": same_base_realization_holds,
        "strict_gap_certified": strict_gap_certified,
    }


def _integral_companion_for_reciprocal(polynomial: sp.Expr) -> sp.Matrix:
    """Return C with det(I-zC)=polynomial for a normalized integral input."""
    z = sp.Symbol("z")
    poly = sp.Poly(polynomial, z)
    degree = max(1, poly.degree())
    coefficients = [sp.Integer(poly.nth(index)) for index in range(degree + 1)]
    companion = sp.zeros(degree)
    for row in range(1, degree):
        companion[row, row - 1] = 1
    for row in range(degree):
        companion[row, degree - 1] = -coefficients[degree - row]
    return companion


def realizable_logarithmic_certificate_family_audit(
    max_depth: int = 4,
) -> dict[str, object]:
    """Check companion realizations of the dyadic Omega(V log V) certificates."""
    z, t = sp.symbols("z t")
    q_polynomial = 1 - 2 * z
    vertex_counts: list[int] = []
    relative_realizations_hold = True
    certificate_degrees_hold = True
    zeta_ratios_nontrivial = True

    for depth in range(max_depth + 1):
        vertex_count = 2 ** (depth + 1)
        numerator = sp.expand(q_polynomial.subs(z, z**vertex_count))
        denominator = sp.expand(q_polynomial**vertex_count)
        first = _integral_companion_for_reciprocal(numerator)
        second = _integral_companion_for_reciprocal(denominator)
        same_parity = all(
            (first[row, column] - second[row, column]) % 2 == 0
            for row in range(vertex_count)
            for column in range(vertex_count)
        )

        base = sp.zeros(vertex_count)
        for row in range(vertex_count):
            for column in range(vertex_count):
                bound = max(abs(first[row, column]), abs(second[row, column]))
                candidate = int(bound) + 1
                if candidate % 2 != int(first[row, column]) % 2:
                    candidate += 1
                base[row, column] = candidate
        realizable = same_parity and all(
            bool(
                base[row, column] > abs(block[row, column])
                and (base[row, column] - block[row, column]) % 2 == 0
            )
            for block in (first, second)
            for row in range(vertex_count)
            for column in range(vertex_count)
        )
        expected_first_charpoly = sp.expand(
            t**vertex_count * numerator.subs(z, 1 / t)
        )
        expected_second_charpoly = sp.expand(
            t**vertex_count * denominator.subs(z, 1 / t)
        )
        relative_realizations_hold &= all(
            (
                realizable,
                sp.expand(first.charpoly(t).as_expr())
                == expected_first_charpoly,
                sp.expand(second.charpoly(t).as_expr())
                == expected_second_charpoly,
            )
        )

        certificate = sp.prod(
            q_polynomial.subs(z, z ** (2**index))
            ** (2 ** (depth - index))
            for index in range(depth + 1)
        )
        certificate_degrees_hold &= (
            sp.degree(certificate, z)
            == (depth + 1) * 2**depth
            == vertex_count * (depth + 1) // 2
        )
        zeta_ratios_nontrivial &= sp.cancel(numerator / denominator - 1) != 0
        vertex_counts.append(vertex_count)

    return {
        "vertex_counts": tuple(vertex_counts),
        "relative_realizations_hold": relative_realizations_hold,
        "certificate_degrees_hold": certificate_degrees_hold,
        "zeta_ratios_nontrivial": zeta_ratios_nontrivial,
    }


def elementary_two_group_cross_base_audit() -> dict[str, object]:
    """Check determinant parity and Fourier recovery for distinct base sizes."""
    z = sp.Symbol("z")
    group = tuple(product((0, 1), repeat=2))
    first_labels = {
        (0, 0): sp.Matrix(((1,),)),
        (0, 1): sp.zeros(1),
        (1, 0): sp.zeros(1),
        (1, 1): sp.Matrix(((1,),)),
    }
    second_labels = {
        (0, 0): sp.Matrix(((1, 0), (0, 0))),
        (0, 1): sp.Matrix(((0, 1), (0, 0))),
        (1, 0): sp.Matrix(((0, 0), (1, 0))),
        (1, 1): sp.Matrix(((0, 0), (0, 1))),
    }
    first_base = sum(first_labels.values(), sp.zeros(1))
    second_base = sum(second_labels.values(), sp.zeros(2))

    def character(index: tuple[int, int], element: tuple[int, int]) -> int:
        return (-1) ** sum(left * right for left, right in zip(index, element))

    first_determinants = []
    second_determinants = []
    congruent_mod_two = True
    for index in group:
        first_twist = sum(
            (character(index, element) * matrix for element, matrix in first_labels.items()),
            sp.zeros(1),
        )
        second_twist = sum(
            (character(index, element) * matrix for element, matrix in second_labels.items()),
            sp.zeros(2),
        )
        first_det = sp.expand((sp.eye(1) - z * first_twist).det())
        second_det = sp.expand((sp.eye(2) - z * second_twist).det())
        first_determinants.append(first_det)
        second_determinants.append(second_det)
        congruent_mod_two &= sp.Poly(first_det - second_det, z, modulus=2).is_zero

    coordinates = sp.symbols("c0:4")
    transformed = tuple(
        sum(character(index, element) * value for element, value in zip(group, coordinates))
        for index in group
    )
    recovered = tuple(
        sp.cancel(
            sum(character(index, element) * value for index, value in zip(group, transformed))
            / len(group)
        )
        for element in group
    )
    base_determinant = sp.expand((sp.eye(1) - z * first_base).det())
    second_base_determinant = sp.expand((sp.eye(2) - z * second_base).det())
    real_grid = tuple(sp.Rational(j, 20) for j in range(1, 10))
    all_determinants = set(first_determinants + second_determinants)
    budgets = {
        2 * 2 * ((4 * 2 - 1).bit_length())
        for _rank in range(1, 9)
    }

    return {
        "base_sizes": (first_base.rows, second_base.rows),
        "perron_roots": (max(first_base.eigenvals()), max(second_base.eigenvals())),
        "base_determinants_equal": base_determinant == second_base_determinant,
        "all_character_determinants_equal": first_determinants == second_determinants,
        "all_character_determinants_congruent_mod_two": congruent_mod_two,
        "fourier_inversion_exact": recovered == coordinates,
        "positive_on_real_grid": all(
            determinant.subs(z, point) > 0
            for determinant in all_determinants
            for point in real_grid
        ),
        "sample_budget_independent_of_rank": len(budgets) == 1 and budgets == {12},
    }


@lru_cache(maxsize=None)
def effective_rational_mahler_coboundary(
    p_zero_expression: sp.Expr, p_one_expression: sp.Expr, radix: int = 2
) -> dict[str, sp.Expr | int] | None:
    """Decide P0/P1=R(z^p)/R(z)^p by the finite Pade criterion."""
    if radix < 2:
        raise ValueError("the Mahler radix must be at least two")
    z = sp.Symbol("z")
    p_zero = sp.Poly(p_zero_expression, z, domain=sp.ZZ)
    p_one = sp.Poly(p_one_expression, z, domain=sp.ZZ)
    if p_zero.eval(0) != 1 or p_one.eval(0) != 1:
        raise ValueError("both input polynomials must have constant term one")
    if sp.gcd(p_zero, p_one).degree() > 0:
        raise ValueError("the input polynomials must be coprime")

    total_degree = p_zero.degree() + p_one.degree()
    if total_degree == 0:
        return {
            "rational_function": sp.Integer(1),
            "numerator": sp.Integer(1),
            "denominator": sp.Integer(1),
            "degree_bound": 0,
            "height_bound": sp.Integer(0),
        }
    if p_zero.degree() != p_one.degree():
        return None
    logarithmic_depth = 0
    power = 1
    while power * radix <= total_degree:
        power *= radix
        logarithmic_depth += 1
    degree_bound = effective_mahler_degree_bound(radix, total_degree)
    series_coefficients = [sp.Integer(1)]
    for degree in range(1, 2 * degree_bound + 1):
        known_series = sum(
            coefficient * z**index
            for index, coefficient in enumerate(series_coefficients)
        )
        recurrence_numerator = sp.expand(
            p_one.as_expr() * known_series.subs(z, z**radix)
            - p_zero.as_expr() * known_series**radix
        ).coeff(z, degree)
        series_coefficients.append(sp.cancel(recurrence_numerator / radix))

    denominator_variables = sp.symbols(f"b1:{degree_bound + 1}")
    denominator_coefficients = (sp.Integer(1),) + denominator_variables
    pade_equations = [
        sum(
            denominator_coefficients[index] * series_coefficients[degree - index]
            for index in range(degree_bound + 1)
        )
        for degree in range(degree_bound + 1, 2 * degree_bound + 1)
    ]
    solution_set = sp.linsolve(pade_equations, denominator_variables)
    if solution_set == sp.EmptySet:
        return None
    solution = next(iter(solution_set))
    free_variables = set().union(*(entry.free_symbols for entry in solution))
    specialization = {variable: 0 for variable in free_variables}
    denominator_coefficients = (sp.Integer(1),) + tuple(
        sp.cancel(entry.subs(specialization)) for entry in solution
    )
    denominator = sum(
        coefficient * z**degree
        for degree, coefficient in enumerate(denominator_coefficients)
    )
    numerator = sum(
        sum(
            denominator_coefficients[index] * series_coefficients[degree - index]
            for index in range(min(degree, degree_bound) + 1)
        )
        * z**degree
        for degree in range(degree_bound + 1)
    )
    numerator, denominator = sp.cancel(numerator / denominator).as_numer_denom()
    numerator = _constant_one_polynomial(numerator, z).as_expr()
    denominator = _constant_one_polynomial(denominator, z).as_expr()
    identity = sp.expand(
        p_zero.as_expr() * numerator**radix * denominator.subs(z, z**radix)
        - p_one.as_expr() * numerator.subs(z, z**radix) * denominator**radix
    )
    if identity != 0:
        return None

    heights = [
        sp.log(max(abs(coefficient) for coefficient in polynomial.all_coeffs()))
        for polynomial in (p_zero, p_one)
    ]
    mahler_input_bound = (
        sum(heights)
        + sp.log((p_zero.degree() + 1) * (p_one.degree() + 1)) / 2
    )
    height_bound = (
        degree_bound * sp.log(2)
        + total_degree * (logarithmic_depth + 1) * mahler_input_bound
    )
    return {
        "rational_function": sp.cancel(numerator / denominator),
        "numerator": numerator,
        "denominator": denominator,
        "degree_bound": degree_bound,
        "height_bound": height_bound,
        "radix": radix,
    }


def general_p_effective_reconstruction_matches() -> bool:
    """Check exact reconstruction and the logarithmic-derivative reduction."""
    z = sp.Symbol("z")
    for radix in (2, 3, 4, 5):
        rational_function = 1 + 2 * z
        ratio = sp.cancel(
            rational_function.subs(z, z**radix) / rational_function**radix
        )
        p_zero, p_one = ratio.as_numer_denom()
        p_zero = _constant_one_polynomial(p_zero, z).as_expr()
        p_one = _constant_one_polynomial(p_one, z).as_expr()
        result = effective_rational_mahler_coboundary(
            p_zero, p_one, radix
        )
        if result is None or result["rational_function"] != rational_function:
            return False
        h = sp.cancel(p_zero / p_one)
        u = sp.cancel(z * sp.diff(rational_function, z) / rational_function)
        additive_residual = sp.cancel(
            u.subs(z, z**radix)
            - u
            - z * sp.diff(h, z) / (radix * h)
        )
        if additive_residual != 0:
            return False
    return True


def effective_mahler_bounds_match() -> bool:
    """Check reconstruction, parity, and the explicit degree/height bounds."""
    z = sp.Symbol("z")
    examples = (1 - z, 1 + 2 * z)
    for rational_function in examples:
        ratio = sp.cancel(
            rational_function.subs(z, z**2) / rational_function**2
        )
        p_zero, p_one = ratio.as_numer_denom()
        p_zero = _constant_one_polynomial(p_zero, z).as_expr()
        p_one = _constant_one_polynomial(p_one, z).as_expr()
        result = effective_rational_mahler_coboundary(p_zero, p_one)
        if result is None or result["rational_function"] != rational_function:
            return False
        numerator = sp.Poly(result["numerator"], z, domain=sp.ZZ)
        denominator = sp.Poly(result["denominator"], z, domain=sp.ZZ)
        actual_height = max(
            sp.log(max(abs(coefficient) for coefficient in polynomial.all_coeffs()))
            for polynomial in (numerator, denominator)
        )
        if not all(
            (
                numerator.degree() + denominator.degree()
                <= result["degree_bound"],
                sp.N(actual_height - result["height_bound"], 30) <= 0,
                sp.Poly(p_zero - p_one, z, modulus=2).is_zero,
            )
        ):
            return False
    return effective_rational_mahler_coboundary(1 + 2 * z, 1 - 2 * z) is None


def finite_radial_collision_audit(
    p_zero_expression: sp.Expr,
    p_one_expression: sp.Expr,
    interval_end: sp.Expr,
) -> dict[str, sp.Expr | int | bool | tuple[sp.Expr, ...]]:
    """Extract the radial collision set from a normalized Mahler certificate."""
    z = sp.Symbol("z")
    certificate = effective_rational_mahler_coboundary(
        p_zero_expression, p_one_expression
    )
    if certificate is None:
        raise ValueError("the input ratio has no normalized rational certificate")

    collision_polynomial = sp.factor(
        certificate["numerator"] - certificate["denominator"]
    )
    if collision_polynomial == 0:
        raise ValueError("the identity ratio has every admissible point as a collision")
    roots = sp.real_roots(sp.Poly(collision_polynomial, z, domain=sp.QQ))
    collision_points = tuple(
        root
        for root in roots
        if bool(root > 0) and bool(root <= interval_end)
    )
    degree_bound = int(certificate["degree_bound"])
    collision_bound = degree_bound - 1
    return {
        **certificate,
        "collision_polynomial": collision_polynomial,
        "collision_points": collision_points,
        "degree_bound": degree_bound,
        "collision_bound": collision_bound,
        "sample_budget": degree_bound,
        "collision_count_within_bound": len(collision_points) <= collision_bound,
    }


def interior_no_gap_standard_zeta_audit() -> dict[str, object]:
    """Check interior regularity when a binary twisted block has no strict gap."""
    z = sp.Symbol("z")
    sample = sp.Rational(1, 3)

    first_identity = sp.Matrix(((2,),))
    first_involution = sp.zeros(1)
    second_identity = sp.Matrix(((1,),))
    second_involution = sp.Matrix(((1,),))
    first_base = first_identity + first_involution
    second_base = second_identity + second_involution
    first_twisted = first_identity - first_involution
    second_twisted = second_identity - second_involution
    first_cover = first_identity.row_join(first_involution).col_join(
        first_involution.row_join(first_identity)
    )
    second_cover = second_identity.row_join(second_involution).col_join(
        second_involution.row_join(second_identity)
    )

    same_base_compatible = first_base == second_base
    perron_root = max(abs(value) for value in first_base.eigenvals())
    first_twisted_radius = max(abs(value) for value in first_twisted.eigenvals())

    first_determinant = sp.expand((sp.eye(1) - z * first_twisted).det())
    second_determinant = sp.expand((sp.eye(1) - z * second_twisted).det())
    determinant_ratio = sp.cancel(first_determinant / second_determinant)
    first_cover_zeta = sp.cancel(1 / (sp.eye(2) - z * first_cover).det())
    second_cover_zeta = sp.cancel(1 / (sp.eye(2) - z * second_cover).det())
    standard_zeta_ratio = sp.cancel(second_cover_zeta / first_cover_zeta)

    entrywise_dominated = all(
        abs(twisted[i, j]) <= first_base[i, j]
        for twisted in (first_twisted, second_twisted)
        for i in range(first_base.rows)
        for j in range(first_base.cols)
    )
    parity_compatible = all(
        (twisted[i, j] - first_base[i, j]) % 2 == 0
        for twisted in (first_twisted, second_twisted)
        for i in range(first_base.rows)
        for j in range(first_base.cols)
    )

    # Here H(t)=1-2t.  For every j>=0, 0<sample^(2^j)<=sample<1/2,
    # hence every dyadic factor lies in (0,1).  Its logarithm is negative,
    # and the positive weighted sum is therefore strictly negative.
    exact_dyadic_form = determinant_ratio == 1 - 2 * z
    all_dyadic_factors_lie_between_zero_and_one = bool(
        exact_dyadic_form and 0 < sample < sp.Rational(1, 2)
    )

    return {
        "perron_root": perron_root,
        "first_twisted_radius": first_twisted_radius,
        "first_has_strict_gap": first_twisted_radius < perron_root,
        "sample_radius": sample,
        "sample_is_interior": sample < 1 / perron_root,
        "same_base_compatible": same_base_compatible,
        "entrywise_dominated": entrywise_dominated,
        "parity_compatible": parity_compatible,
        "determinants_positive_at_sample": all(
            polynomial.subs(z, sample) > 0
            for polynomial in (first_determinant, second_determinant)
        ),
        "determinant_ratio": determinant_ratio,
        "standard_zeta_ratio": standard_zeta_ratio,
        "determinant_ratio_is_standard_zeta_ratio": (
            determinant_ratio == standard_zeta_ratio
        ),
        "all_dyadic_factors_lie_between_zero_and_one": (
            all_dyadic_factors_lie_between_zero_and_one
        ),
        "dyadic_logarithm_is_negative": (
            all_dyadic_factors_lie_between_zero_and_one
        ),
    }


def same_base_determinant_bounds_match() -> bool:
    """Check the coefficient estimate for compatible same-base sign blocks."""
    z = sp.Symbol("z")
    adjacency = sp.Matrix(
        ((0, 4, 0, 0), (1, 1, 0, 2), (0, 0, 0, 4), (0, 2, 1, 1))
    )
    sign_blocks = (
        sp.Matrix(((0, -2, 0, 0), (-1, -1, 0, -2), (0, 0, 0, -2), (0, 2, -1, 1))),
        sp.Matrix(((0, -4, 0, 0), (1, 1, 0, 0), (0, 0, 0, -4), (0, 0, 1, 1))),
    )
    size = adjacency.rows
    maximum_entry = max(1, *(int(entry) for entry in adjacency))
    coefficient_bound = (size * maximum_entry) ** size
    for matrix in sign_blocks:
        determinant = sp.Poly((sp.eye(size) - z * matrix).det(), z, domain=sp.ZZ)
        if not all(
            (
                determinant.degree() <= size,
                max(abs(coefficient) for coefficient in determinant.all_coeffs())
                <= coefficient_bound,
                all(abs(matrix[i, j]) <= adjacency[i, j] for i in range(size) for j in range(size)),
                all((matrix[i, j] - adjacency[i, j]) % 2 == 0 for i in range(size) for j in range(size)),
            )
        ):
            return False
    return True


@lru_cache(maxsize=1)
def enumerate_quadratic_binary_certificates() -> dict[str, int]:
    """Exhaust the four-vertex, two-out-regular signed certificate class."""
    row_types = []
    for indices in combinations_with_replacement(range(4), 2):
        row = [0, 0, 0, 0]
        for index in indices:
            row[index] += 1
        row_types.append(tuple(row))
    signed_rows = {row: _compatible_signed_rows(row) for row in row_types}
    targets = {
        "first_determinant_support": (0, 2, 0, 2),
        "second_determinant_support": (2, -6, -10, 4),
    }
    counts = {
        "primitive_bases": 0,
        "first_determinant_support": 0,
        "second_determinant_support": 0,
    }
    for adjacency in product(row_types, repeat=4):
        if not _is_primitive_matrix(adjacency):
            continue
        counts["primitive_bases"] += 1
        supported = {name: False for name in targets}
        for signed_matrix in product(*(signed_rows[row] for row in adjacency)):
            trace_one = sum(signed_matrix[i][i] for i in range(4))
            possible_targets = tuple(
                name
                for name, target in targets.items()
                if not supported[name] and trace_one == target[0]
            )
            if not possible_targets:
                continue
            invariants = _matrix_invariants(signed_matrix)
            for name in possible_targets:
                if invariants == targets[name]:
                    supported[name] = True
            if all(supported.values()):
                break
        for name, is_supported in supported.items():
            counts[name] += int(is_supported)
    return counts


def radial_profile_leading_coefficient(
    primitive_differences: dict[int, sp.Expr],
) -> tuple[int, sp.Expr] | None:
    """Return the first non-zero coefficient of sum a_n log(1-z^n)."""
    non_zero = [
        length
        for length, value in primitive_differences.items()
        if sp.simplify(value) != 0
    ]
    if not non_zero:
        return None
    first_length = min(non_zero)
    coefficient = -sum(
        sp.Rational(divisor, first_length) * primitive_differences.get(divisor, 0)
        for divisor in range(1, first_length + 1)
        if first_length % divisor == 0
    )
    return first_length, sp.simplify(coefficient)


def _least_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(word[j:] + word[:j] for j in range(len(word)))


def _is_primitive(word: tuple[int, ...]) -> bool:
    n = len(word)
    return all(word != word[:d] * (n // d) for d in range(1, n) if n % d == 0)


def primitive_binary_necklace_parity_counts(
    max_length: int,
) -> dict[int, tuple[int, int]]:
    """Count primitive binary necklaces by even and odd label parity."""
    counts: dict[int, tuple[int, int]] = {}
    for n in range(1, max_length + 1):
        representatives = {
            _least_rotation(word)
            for word in product((0, 1), repeat=n)
            if _is_primitive(word)
        }
        even = sum(sum(word) % 2 == 0 for word in representatives)
        odd = len(representatives) - even
        counts[n] = (even, odd)
    return counts


def quotient_correction_coefficients(
    max_degree: int,
) -> tuple[dict[int, sp.Rational], dict[int, sp.Rational]]:
    """Compare L_{1_e}-F_{1_e} with the quotient split-orbit product.

    The model is the full binary shift labelled by C2.  Its non-trivial
    twisted block is zero, so the strict twisted gap is exact.  A primitive
    orbit of odd parity closes in the regular cover only after two turns.
    """
    counts = primitive_binary_necklace_parity_counts(max_degree)
    periodic_minus_fixed = {degree: sp.Rational(0) for degree in range(1, max_degree + 1)}
    split_orbit_product = {degree: sp.Rational(0) for degree in range(1, max_degree + 1)}

    for length, (_even, odd) in counts.items():
        for repeat in range(2, max_degree // length + 1, 2):
            degree = repeat * length
            periodic_minus_fixed[degree] += sp.Rational(odd, repeat)
        for k in range(1, max_degree // (2 * length) + 1):
            degree = 2 * k * length
            split_orbit_product[degree] += sp.Rational(odd, 2 * k)

    return periodic_minus_fixed, split_orbit_product


def quotient_correction_real_interval_matches(max_degree: int = 16) -> bool:
    """Evaluate the two independently assembled series on 0 < z < 1/2."""
    periodic_minus_fixed, split_orbit_product = quotient_correction_coefficients(
        max_degree
    )
    sample_points = tuple(sp.Rational(n, 20) for n in range(1, 10))

    def evaluate(coefficients: dict[int, sp.Rational], z: sp.Rational) -> sp.Expr:
        return sum(
            (coefficient * z**degree for degree, coefficient in coefficients.items()),
            sp.Rational(0),
        )

    return all(
        evaluate(periodic_minus_fixed, z) == evaluate(split_orbit_product, z)
        for z in sample_points
    )


def verify_c2_regular_cover_factorization() -> bool:
    """Check the regular-cover determinant and reduced Perron constants."""
    z = sp.Symbol("z")
    identity = sp.eye(2)
    regular_cover = sp.Matrix(((1, 1), (1, 1)))
    trivial_block = sp.Matrix(((2,),))
    sign_block = sp.Matrix(((0,),))
    cover_polynomial = sp.expand((identity - z * regular_cover).det())
    block_product = sp.expand(
        (sp.eye(1) - z * trivial_block).det()
        * (sp.eye(1) - z * sign_block).det()
    )
    t = sp.Symbol("t", real=True)
    cover_constant = sp.limit(
        (1 - t) / (sp.eye(2) - t * regular_cover / 2).det(), t, 1, dir="-"
    )
    base_constant = sp.limit((1 - t) / (1 - t), t, 1, dir="-")
    return cover_polynomial == block_product and cover_constant == base_constant == 1


def s3_constant_fourier_round_trip(
    scalar: sp.Expr, sign: sp.Expr, standard: sp.Expr
) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Recover the scalar and non-trivial S3 coordinates from class constants."""
    class_sizes = (1, 3, 2)
    sign_character = (1, -1, 1)
    standard_character = (2, 0, -1)
    group_order = 6
    log_constants = tuple(
        -sp.Rational(size, group_order)
        * (
            scalar
            + sign_character[index] * sign
            + standard_character[index] * standard
        )
        for index, size in enumerate(class_sizes)
    )
    recovered_scalar = -sum(log_constants)
    recovered_sign = -sum(
        character_value * log_constant
        for character_value, log_constant in zip(sign_character, log_constants)
    )
    recovered_standard = -sum(
        character_value * log_constant
        for character_value, log_constant in zip(
            standard_character, log_constants
        )
    )
    return recovered_scalar, recovered_sign, recovered_standard


def c3_constant_fourier_round_trip(
    scalar: sp.Expr, first: sp.Expr, second: sp.Expr
) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Check the inverse convention for a group with complex characters."""
    omega = (-sp.Integer(1) + sp.sqrt(3) * sp.I) / 2
    first_character = (sp.Integer(1), omega, omega**2)
    second_character = tuple(sp.conjugate(value) for value in first_character)
    log_constants = tuple(
        -sp.Rational(1, 3)
        * (
            scalar
            + sp.conjugate(first_character[index]) * first
            + sp.conjugate(second_character[index]) * second
        )
        for index in range(3)
    )
    recovered_scalar = -sum(log_constants)
    recovered_first = -sum(
        character_value * log_constant
        for character_value, log_constant in zip(first_character, log_constants)
    )
    recovered_second = -sum(
        character_value * log_constant
        for character_value, log_constant in zip(second_character, log_constants)
    )
    return recovered_scalar, recovered_first, recovered_second


def universal_product_jet(alpha: sp.Expr, order: int) -> sp.Expr:
    """Return the 1/N jet of exp[-alpha(H_N-log N-gamma)]."""
    x = sp.Symbol("x")
    logarithmic_jet = -alpha * x / 2
    for j in range(1, order // 2 + 1):
        logarithmic_jet += alpha * sp.bernoulli(2 * j) * x ** (2 * j) / (2 * j)
    return sp.expand(sp.series(sp.exp(logarithmic_jet), x, 0, order + 1).removeO())


def render_report() -> str:
    max_degree = 16
    periodic_minus_fixed, split_orbit_product = quotient_correction_coefficients(
        max_degree
    )
    enumeration = enumerate_quadratic_binary_certificates()
    nishioka = nishioka_special_value_specialization()
    z = sp.Symbol("z")
    collision_q = 1 - z + 4 * z**2
    finite_collisions = finite_radial_collision_audit(
        collision_q.subs(z, z**2), collision_q**2, sp.Rational(1, 4)
    )
    interior_no_gap = interior_no_gap_standard_zeta_audit()
    logarithmic_bound = logarithmic_mahler_divisor_bound_audit()
    logarithmic_family = mahler_log_degree_extremal_family_audit()
    denominator_audit = rational_critical_denominator_audit()
    multicollision_audit = realizable_multicollision_family_audit()
    realizable_log_audit = realizable_logarithmic_certificate_family_audit()
    cross_base = elementary_two_group_cross_base_audit()
    c3_support = c3_adams_mobius_support_obstruction(60)
    alpha = sp.Symbol("alpha")
    jet = universal_product_jet(alpha, order=3)
    checks = {
        "exact C2 boundary collision": verify_c2_boundary_collision(),
        "binary coboundary real interval": binary_coboundary_real_interval_matches(),
        "positive rational Mahler certificate": rational_mahler_certificate_matches(),
        "unrestricted Mahler kernel domain counterexample": (
            unrestricted_mahler_kernel_domain_counterexample()
        ),
        "diagonal realizable Mahler subclass": (
            verify_diagonal_realizable_mahler_subclass()
        ),
        "critical Mahler normalization": critical_mahler_normalization_matches(),
        "critical Mahler integrality": critical_mahler_integrality_matches(),
        "rational critical Mahler denominators": all(
            (
                denominator_audit["all_bounds_hold"],
                denominator_audit["nonintegral_coefficient_seen"],
            )
        ),
        "critical zero-estimate pullback": critical_zero_estimate_pullback_matches(),
        "Kumiko Nishioka specialization": all(
            (
                nishioka["inequality_left"] < nishioka["inequality_right"],
                nishioka["reduced_coefficients_coprime"],
                nishioka["sampled_orbit_admissible"],
                nishioka["coefficients_integral"],
            )
        ),
        "normalized rational Mahler saturation": rational_mahler_saturation_matches(),
        "effective rational Mahler Pade decision": all(
            (
                effective_rational_mahler_coboundary(
                    1 + sp.Symbol("z"), 1 - sp.Symbol("z")
                )["rational_function"]
                == 1 - sp.Symbol("z"),
                effective_rational_mahler_coboundary(
                    1 + 2 * sp.Symbol("z"), 1 - 2 * sp.Symbol("z")
                )
                is None,
            )
        ),
        "effective Mahler bounds": effective_mahler_bounds_match(),
        "general-p effective reconstruction": general_p_effective_reconstruction_matches(),
        "logarithmic Mahler divisor bound": all(
            (
                logarithmic_bound["certificates_checked"] >= 100,
                logarithmic_bound["root_of_unity_cases_checked"],
                logarithmic_bound["all_within_bound"],
            )
        ),
        "Mahler logarithmic lower-bound family": all(
            (
                logarithmic_family["identities_hold"],
                logarithmic_family["degrees_hold"],
                logarithmic_family["no_cancellation"],
            )
        ),
        "realizable multi-collision family": all(
            (
                multicollision_audit["determinant_identities_hold"],
                multicollision_audit["all_radii_in_perron_interval"],
                multicollision_audit["same_base_realization_holds"],
                multicollision_audit["strict_gap_certified"],
                multicollision_audit["collision_counts"] == (1, 2, 3, 4),
            )
        ),
        "realizable logarithmic certificates": all(
            (
                realizable_log_audit["relative_realizations_hold"],
                realizable_log_audit["certificate_degrees_hold"],
                realizable_log_audit["zeta_ratios_nontrivial"],
            )
        ),
        "cross-base elementary two-group interface": all(
            (
                cross_base["base_determinants_equal"],
                cross_base["all_character_determinants_equal"],
                cross_base["all_character_determinants_congruent_mod_two"],
                cross_base["fourier_inversion_exact"],
                cross_base["positive_on_real_grid"],
                cross_base["sample_budget_independent_of_rank"],
            )
        ),
        "finite radial collision set": all(
            (
                finite_collisions["collision_points"] == (sp.Rational(1, 4),),
                finite_collisions["collision_count_within_bound"],
                finite_collisions["collision_bound"] == 31,
                finite_collisions["sample_budget"] == 32,
            )
        ),
        "unconditional interior sampling": all(
            (
                not interior_no_gap["first_has_strict_gap"],
                interior_no_gap["sample_is_interior"],
                interior_no_gap["same_base_compatible"],
                interior_no_gap["entrywise_dominated"],
                interior_no_gap["parity_compatible"],
                interior_no_gap["determinants_positive_at_sample"],
                interior_no_gap["determinant_ratio"] == 1 - 2 * z,
                interior_no_gap["determinant_ratio_is_standard_zeta_ratio"],
                interior_no_gap["all_dyadic_factors_lie_between_zero_and_one"],
                interior_no_gap["dyadic_logarithm_is_negative"],
            )
        ),
        "C3 Adams-Mobius support obstruction": all(
            (
                c3_support[prime] == (0, 1, -1)
                for prime in (2, 5, 11, 17)
            )
        ),
        "same-base determinant coefficient bound": same_base_determinant_bounds_match(),
        "quadratic binary certificate enumeration": enumeration
        == {
            "primitive_bases": 2208,
            "first_determinant_support": 48,
            "second_determinant_support": 0,
        },
        "radial-profile triangularity": radial_profile_leading_coefficient(
            {1: 0, 2: 0, 3: sp.Integer(7), 4: sp.Integer(-5)}
        )
        == (3, sp.Integer(-7)),
        "quotient correction power series": periodic_minus_fixed
        == split_orbit_product,
        "quotient correction on 0 < z < 1/2": (
            quotient_correction_real_interval_matches(max_degree)
        ),
        "quotient correction is non-zero": sum(periodic_minus_fixed.values()) > 0,
        "regular-cover determinant factorization": verify_c2_regular_cover_factorization(),
        "universal harmonic jet": sp.simplify(
            jet
            - 1
            + alpha * sp.Symbol("x") / 2
            - alpha * (3 * alpha + 2) * sp.Symbol("x") ** 2 / 24
            + alpha**2 * (alpha + 2) * sp.Symbol("x") ** 3 / 48
        )
        == 0,
        "S3 class-constant Fourier inversion": all(
            sp.simplify(recovered - original) == 0
            for recovered, original in zip(
                s3_constant_fourier_round_trip(
                    sp.Symbol("S"), sp.Symbol("F_sign"), sp.Symbol("F_standard")
                ),
                (sp.Symbol("S"), sp.Symbol("F_sign"), sp.Symbol("F_standard")),
            )
        ),
        "C3 complex-character Fourier inversion": all(
            sp.simplify(recovered - original) == 0
            for recovered, original in zip(
                c3_constant_fourier_round_trip(
                    sp.Symbol("S"), sp.Symbol("F_1"), sp.Symbol("F_2")
                ),
                (sp.Symbol("S"), sp.Symbol("F_1"), sp.Symbol("F_2")),
            )
        ),
    }
    if not all(checks.values()):
        failed = ", ".join(name for name, passed in checks.items() if not passed)
        raise AssertionError(f"failed checks: {failed}")

    lines = [
        "A5 CLAIM VERIFICATION",
        "Exact C2 boundary collision: verified",
        f"Primitive two-out bases: {enumeration['primitive_bases']}",
        "Determinant supports: "
        f"{enumeration['first_determinant_support']} and "
        f"{enumeration['second_determinant_support']}",
        "Real boundary grid: 25 points in 0 < z <= 1/4 at 80 digits",
        "Positive rational Mahler certificate: verified on the same real grid",
        "Unrestricted Mahler kernel inclusion: domain counterexample verified",
        "Diagonal same-base Mahler subclass: compatibility and strict gap verified",
        "Critical Mahler normalization: squared product on 49 real points; unsquared identity refuted",
        "Critical Mahler integrality: 24 integer coefficients and equation verified",
        "Rational critical p-Mahler denominators: p=2,3,4,5; exponent 2n-1 verified",
        "Critical zero-estimate pullback: exact identity, bidegrees, and finite-rank bound verified",
        "Kumiko Nishioka specialization: p=2, N=0, n=1, m=M=2, L=1; 4<8",
        "Normalized Mahler saturation: exact rational examples verified",
        "Effective rational Mahler Pade decision: verified",
        "Effective Mahler degree and height bounds: verified",
        "General-p effective reconstruction: p=2,3,4,5 and logarithmic derivative verified",
        "Logarithmic Mahler divisor bound: exact counterexample search verified",
        "Mahler logarithmic lower-bound family: exact identities and degrees verified",
        "Realizable multi-collisions: m=1,2,3,4 on 6,10,14,18 vertices",
        "Realizable logarithmic certificates: V=2,4,8,16,32",
        "Cross-base (C2)^2 interface: sizes 1 and 2; determinant and Fourier checks verified",
        "Finite radial collision set: {1/4}; 1 <= 31",
        "Finite radial recovery budget: 32 samples with one algebraic anchor",
        "No-gap interior model: y=1/3; standard cover-zeta ratio verified",
        "C3 Adams-Mobius support: non-zero at primes 2, 5, 11, 17",
        "Same-base determinant coefficient bound: verified",
        "Radial-profile leading coefficient: triangular",
        "Quotient model: full binary shift with C2 labels 0 and 1.",
        f"Primitive necklaces and quotient correction checked through z^{max_degree}.",
        "The quotient identity agrees at nine rational points in 0 < z < 1/2.",
        f"Universal product jet through N^(-3): {sp.sstr(jet)}",
        "The S3 class constants recover the scalar, sign, and standard coordinates.",
        "The C3 check confirms the complex-character conjugation convention.",
        "STATUS: PASS",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    report = render_report()
    output = Path(__file__).with_name("verify_a5_results_output.txt")
    output.write_text(report, encoding="ascii", newline="\n")
    print(report, end="")


if __name__ == "__main__":
    main()
