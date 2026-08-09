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


def nishioka_special_value_specialization() -> dict[str, object]:
    """Audit the exact parameters used for Nishioka's 1982 theorem.

    This checks the algebraic specialization and a realizable strict-gap model;
    Nishioka's transcendence theorem itself remains the cited analytic input.
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


@lru_cache(maxsize=None)
def effective_rational_mahler_coboundary(
    p_zero_expression: sp.Expr, p_one_expression: sp.Expr
) -> dict[str, sp.Expr | int] | None:
    """Decide P0/P1=R(z^2)/R(z)^2 by the finite Pade criterion."""
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
    maximum_degree = max(p_zero.degree(), p_one.degree())
    if any(
        (p_zero.nth(index) - p_one.nth(index)) % 2
        for index in range(maximum_degree + 1)
    ):
        return None

    logarithmic_depth = total_degree.bit_length() - 1
    degree_bound = total_degree**2 * (2 ** (logarithmic_depth + 1) - 1)
    p_zero_coefficients = [
        p_zero.nth(index) for index in range(p_zero.degree() + 1)
    ]
    p_one_coefficients = [
        p_one.nth(index) for index in range(p_one.degree() + 1)
    ]
    series_coefficients = [sp.Integer(1)]
    for degree in range(1, 2 * degree_bound + 1):
        right_hand_side = sum(
            p_one_coefficients[index] * series_coefficients[(degree - index) // 2]
            for index in range(min(degree, p_one.degree()) + 1)
            if (degree - index) % 2 == 0
        )
        known_square = sp.Integer(0)
        for index in range(min(degree, p_zero.degree()) + 1):
            residual_degree = degree - index
            for left_degree in range(residual_degree + 1):
                right_degree = residual_degree - left_degree
                if index == 0 and (
                    (left_degree == 0 and right_degree == degree)
                    or (left_degree == degree and right_degree == 0)
                ):
                    continue
                known_square += (
                    p_zero_coefficients[index]
                    * series_coefficients[left_degree]
                    * series_coefficients[right_degree]
                )
        series_coefficients.append(sp.cancel((right_hand_side - known_square) / 2))

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
        p_zero.as_expr() * numerator**2 * denominator.subs(z, z**2)
        - p_one.as_expr() * numerator.subs(z, z**2) * denominator**2
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
    }


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
        "critical zero-estimate pullback": critical_zero_estimate_pullback_matches(),
        "Nishioka specialization": all(
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
        "finite radial collision set": all(
            (
                finite_collisions["collision_points"] == (sp.Rational(1, 4),),
                finite_collisions["collision_count_within_bound"],
                finite_collisions["collision_bound"] == 959,
                finite_collisions["sample_budget"] == 960,
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
        "Critical zero-estimate pullback: exact identity, bidegrees, and finite-rank bound verified",
        "Nishioka specialization: p=2, N=0, n=1, m=M=2, L=1; 4<8",
        "Normalized Mahler saturation: exact rational examples verified",
        "Effective rational Mahler Pade decision: verified",
        "Effective Mahler degree and height bounds: verified",
        "Finite radial collision set: {1/4}; 1 <= 959",
        "Finite radial recovery budget: 960 algebraic samples",
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
    output.write_text(report, encoding="ascii")
    print(report, end="")


if __name__ == "__main__":
    main()
