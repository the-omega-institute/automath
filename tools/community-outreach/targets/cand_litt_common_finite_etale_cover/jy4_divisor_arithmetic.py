#!/usr/bin/env python3
"""Fermat-quartic J_Y[4] divisor-arithmetic scaffold over F_11^4.

Local provenance for this T-32/Litt #3 C4 layer:

    Y: X^4 + Y^4 + Z^4 = 0 over F_11
    F_11^4 = F_11[t] / (t^4 + 4*t^3 + 1)

These conventions are canonical in the target-local artifacts
``claude_worker_jy4_F11_4_*`` and in
``claude_worker_jy4_F11_4_4division_missing6_exhaustive_E3_output.json``.
They give genus(Y)=3, P_Y(T)=(1+11*T^2)^3, #JY[4]=4096, and
#Y(F_11^4)=13916.

This module deliberately does not fabricate the missing Pic^0(Y) engine.  The
nontrivial group-law step for a non-hyperelliptic genus-3 plane quartic is not
Mumford arithmetic; it requires a geometric reduction algorithm, for example
Khuri-Makdisi linear algebra or a flex/secant/Volcheck-style plane-quartic
algorithm.  The latest local hard-wall audit records that the previous attempt
failed exactly at ``reduce/add-and-reduce``.  Therefore this module provides:

* complete pure-Python arithmetic for F_11^4;
* the canonical Fermat quartic representation and finite-point enumeration;
* a ``ReducedDivisor`` API with honest blockers for nontrivial reduction,
  addition, doubling, and halving.

The concrete next sub-target is to implement a real K1/K2
Khuri-Makdisi/Volcheck reducer over this field, then use it to materialize a
non-hyperflex order-4 class D with 2D outside 2H and a function f_L satisfying
div(f_L)=4D.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Iterable, Iterator, Sequence

P = 11
DEGREE = 4
MODULUS = (1, 0, 0, 4, 1)  # 1 + 4*t^3 + t^4
Y_EQUATION = "X^4 + Y^4 + Z^4 = 0"
BASE_FIELD = "F_11[t]/(t^4 + 4*t^3 + 1)"
GENUS = 3
EXPECTED_JY4_ORDER = 4096
EXPECTED_HYPERFLEX_ORDER = 2048
EXPECTED_Y_F11_4_POINTS = 13916


class ArithmeticBlocker(NotImplementedError):
    """Raised when a requested Picard operation needs the missing reducer."""

    def __init__(self, substep: str, reason: str):
        super().__init__(f"{substep}: {reason}")
        self.substep = substep
        self.reason = reason


def _coerce_coeffs(value: object) -> tuple[int, int, int, int]:
    if isinstance(value, Fq):
        return value.coeffs
    if isinstance(value, int):
        return (value % P, 0, 0, 0)
    if isinstance(value, Sequence):
        coeffs = [int(c) % P for c in value[:DEGREE]]  # type: ignore[index]
        coeffs.extend([0] * (DEGREE - len(coeffs)))
        return tuple(coeffs[:DEGREE])  # type: ignore[return-value]
    raise TypeError(f"cannot coerce {value!r} to Fq")


@dataclass(frozen=True, order=True)
class Fq:
    """Element of F_11^4 in the basis 1,t,t^2,t^3."""

    coeffs: tuple[int, int, int, int] = (0, 0, 0, 0)

    def __init__(self, coeffs: object = 0):
        object.__setattr__(self, "coeffs", _coerce_coeffs(coeffs))

    def __add__(self, other: object) -> "Fq":
        rhs = Fq(other)
        return Fq(tuple((a + b) % P for a, b in zip(self.coeffs, rhs.coeffs)))

    def __radd__(self, other: object) -> "Fq":
        return self + other

    def __neg__(self) -> "Fq":
        return Fq(tuple((-a) % P for a in self.coeffs))

    def __sub__(self, other: object) -> "Fq":
        return self + (-Fq(other))

    def __rsub__(self, other: object) -> "Fq":
        return Fq(other) - self

    def __mul__(self, other: object) -> "Fq":
        rhs = Fq(other)
        prod = [0] * (2 * DEGREE - 1)
        for i, a in enumerate(self.coeffs):
            if not a:
                continue
            for j, b in enumerate(rhs.coeffs):
                if b:
                    prod[i + j] = (prod[i + j] + a * b) % P
        for k in range(len(prod) - 1, DEGREE - 1, -1):
            c = prod[k] % P
            if not c:
                continue
            # t^4 = -4*t^3 - 1 in this quotient.
            for j in range(DEGREE):
                prod[k - DEGREE + j] = (prod[k - DEGREE + j] - c * MODULUS[j]) % P
        return Fq(tuple(prod[:DEGREE]))

    def __rmul__(self, other: object) -> "Fq":
        return self * other

    def __pow__(self, exponent: int) -> "Fq":
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result = ONE
        base = self
        e = exponent
        while e:
            if e & 1:
                result *= base
            base *= base
            e >>= 1
        return result

    def __truediv__(self, other: object) -> "Fq":
        return self * Fq(other).inverse()

    def __rtruediv__(self, other: object) -> "Fq":
        return Fq(other) / self

    def __bool__(self) -> bool:
        return self.coeffs != (0, 0, 0, 0)

    def __repr__(self) -> str:
        return f"Fq{self.coeffs}"

    def inverse(self) -> "Fq":
        if not self:
            raise ZeroDivisionError("0 has no inverse in F_11^4")
        return self ** (P**DEGREE - 2)

    def frobenius(self, power: int = 1) -> "Fq":
        return self ** (P**power)

    def to_json(self) -> list[int]:
        return list(self.coeffs)


ZERO = Fq(0)
ONE = Fq(1)
MINUS_ONE = Fq(-1)
T = Fq((0, 1, 0, 0))

Point = tuple[Fq, Fq, Fq]
Line = tuple[Fq, Fq, Fq]
Vector = tuple[Fq, ...]


def field_elements() -> Iterator[Fq]:
    for a0 in range(P):
        for a1 in range(P):
            for a2 in range(P):
                for a3 in range(P):
                    yield Fq((a0, a1, a2, a3))


def normalize_projective(point: Point) -> Point:
    for coord in point:
        if coord:
            inv = coord.inverse()
            return tuple(c * inv for c in point)  # type: ignore[return-value]
    raise ValueError("zero projective point")


def point_to_json(point: Point) -> list[list[int]]:
    return [coord.to_json() for coord in point]


def point_from_json(data: Sequence[Sequence[int]]) -> Point:
    if len(data) != 3:
        raise ValueError("projective point needs three coordinates")
    return normalize_projective(tuple(Fq(coord) for coord in data))  # type: ignore[return-value]


def curve_value(point: Point) -> Fq:
    x, y, z = point
    return x**4 + y**4 + z**4


def on_curve(point: Point) -> bool:
    return curve_value(point) == ZERO


def partials(point: Point) -> Point:
    x, y, z = point
    return (Fq(4) * x**3, Fq(4) * y**3, Fq(4) * z**3)


def is_singular_point(point: Point) -> bool:
    return on_curve(point) and all(coord == ZERO for coord in partials(point))


def fourth_roots_by_value() -> dict[Fq, list[Fq]]:
    roots: dict[Fq, list[Fq]] = {}
    for a in field_elements():
        roots.setdefault(a**4, []).append(a)
    return roots


def enumerate_curve_points() -> list[Point]:
    """Enumerate Y(F_11^4), normalized with Z=1 plus points at infinity."""

    roots = fourth_roots_by_value()
    points: set[Point] = set()
    for x in field_elements():
        target = MINUS_ONE - x**4
        for y in roots.get(target, []):
            points.add(normalize_projective((x, y, ONE)))
    for x in roots.get(MINUS_ONE, []):
        points.add(normalize_projective((x, ONE, ZERO)))
    return sorted(points)


def count_curve_points_fast() -> int:
    counts = Counter(a**4 for a in field_elements())
    affine = 0
    for x4, multiplicity in counts.items():
        affine += multiplicity * counts[MINUS_ONE - x4]
    infinity = counts[MINUS_ONE]
    return affine + infinity


def frobenius_point(point: Point, power: int = 1) -> Point:
    return normalize_projective(tuple(coord.frobenius(power) for coord in point))  # type: ignore[return-value]


def tangent_line(point: Point) -> Line:
    x, y, z = point
    return (x**3, y**3, z**3)


def eval_line(line: Line, point: Point) -> Fq:
    a, b, c = line
    x, y, z = point
    return a * x + b * y + c * z


def line_divisor(line: Line, points: Iterable[Point] | None = None) -> dict[Point, int]:
    """Return the split F_11^4 zero divisor of a line, if all zeros are split."""

    divisor: dict[Point, int] = {}
    search_points = enumerate_curve_points() if points is None else points
    for point in search_points:
        if eval_line(line, point) == ZERO:
            divisor[point] = divisor.get(point, 0) + 1
    return divisor


def verify_smooth_over_f11_4(points: Iterable[Point] | None = None) -> bool:
    search_points = enumerate_curve_points() if points is None else list(points)
    return all(not is_singular_point(point) for point in search_points)


def hyperflex_points() -> list[Point]:
    """Return the 12 coordinate-axis hyperflex points over F_11^4."""

    roots = fourth_roots_by_value()
    out: set[Point] = set()
    for root in roots[MINUS_ONE]:
        out.add(normalize_projective((ZERO, ONE, root)))
        out.add(normalize_projective((ONE, ZERO, root)))
        out.add(normalize_projective((ONE, root, ZERO)))
    return sorted(out)


def compute_fermat_flex_points() -> list[Point]:
    """Return the 12 Fermat-quartic flexes over F_11^4.

    For X^4+Y^4+Z^4=0 in characteristic 11 the Hessian is a nonzero scalar
    times X^2Y^2Z^2, so the flexes are exactly the coordinate-axis points.
    The ordering is chosen so the first two points support the direct K1
    construction for [Q-P]: flexes[0] lies in D0=div(XZ), while flexes[1]
    is a Y=0 flex outside D0.
    """

    roots = fourth_roots_by_value()[MINUS_ONE]
    x_axis = sorted(normalize_projective((ZERO, ONE, root)) for root in roots)
    y_axis = sorted(normalize_projective((ONE, ZERO, root)) for root in roots)
    z_axis = sorted(normalize_projective((ONE, root, ZERO)) for root in roots)
    flexes = [x_axis[0], y_axis[0], *x_axis[1:], *y_axis[1:], *z_axis]
    if len(set(flexes)) != 12 or any(not on_curve(point) for point in flexes):
        raise ArithmeticBlocker(
            "flex/enumeration",
            "coordinate-axis Hessian enumeration did not produce 12 distinct curve points",
        )
    return flexes


def divisor_degree(divisor: dict[Point, int]) -> int:
    return sum(divisor.values())


def normalize_divisor_dict(divisor: dict[Point, int]) -> dict[Point, int]:
    return {point: coeff for point, coeff in divisor.items() if coeff}


def divisor_to_json(divisor: dict[Point, int]) -> list[dict[str, object]]:
    return [
        {"coefficient": coeff, "point": point_to_json(point)}
        for point, coeff in sorted(divisor.items())
        if coeff
    ]


def degree_monomials(degree: int) -> list[tuple[int, int, int]]:
    """Canonical monomial basis for H^0(Y,O_Y(degree)).

    We use the Fermat relation with leading term X^4:

        X^4 = -Y^4 - Z^4.

    Thus the quotient basis consists of degree-n monomials X^aY^bZ^c with
    a < 4.  The count is 1 for n=0, then
    sum_{a=0..min(3,n)} (n-a+1): 3 for n=1 and 4n-2 for n>=2,
    as expected for a plane quartic.
    """

    if degree < 0:
        return []
    return [
        (a, b, degree - a - b)
        for a in range(min(3, degree) + 1)
        for b in range(degree - a + 1)
    ]


def h0_dimension(degree: int) -> int:
    return len(degree_monomials(degree))


def count_canonical_reps_at_degree(degree: int) -> int:
    return len(degree_monomials(degree))


def _reduce_monomial(
    exponent: tuple[int, int, int], coeff: Fq, out: dict[tuple[int, int, int], Fq]
) -> None:
    stack = [(exponent, coeff)]
    while stack:
        (a, b, c), value = stack.pop()
        if not value:
            continue
        if a < 4:
            out[(a, b, c)] = out.get((a, b, c), ZERO) + value
            continue
        # X^aY^bZ^c = X^(a-4)Y^bZ^c * X^4
        #            = -X^(a-4)Y^(b+4)Z^c - X^(a-4)Y^bZ^(c+4)
        stack.append(((a - 4, b + 4, c), -value))
        stack.append(((a - 4, b, c + 4), -value))


@dataclass(frozen=True)
class HomogPoly:
    """Homogeneous coordinate-ring element on the Fermat quartic."""

    degree: int
    terms: tuple[tuple[tuple[int, int, int], Fq], ...] = ()

    def __init__(
        self,
        degree: int,
        terms: dict[tuple[int, int, int], object] | Iterable[tuple[tuple[int, int, int], object]] = (),
    ):
        if degree < 0:
            raise ValueError("homogeneous degree must be nonnegative")
        raw = dict(terms) if not isinstance(terms, dict) else terms
        reduced: dict[tuple[int, int, int], Fq] = {}
        for exponent, coeff in raw.items():
            if sum(exponent) != degree:
                raise ValueError(f"monomial {exponent!r} is not homogeneous of degree {degree}")
            _reduce_monomial(exponent, Fq(coeff), reduced)
        canonical = tuple(sorted((exp, val) for exp, val in reduced.items() if val))
        object.__setattr__(self, "degree", degree)
        object.__setattr__(self, "terms", canonical)

    @classmethod
    def monomial(cls, exponent: tuple[int, int, int], coeff: object = ONE) -> "HomogPoly":
        return cls(sum(exponent), {exponent: coeff})

    @classmethod
    def from_vector(cls, degree: int, vector: Sequence[object]) -> "HomogPoly":
        basis = degree_monomials(degree)
        if len(vector) != len(basis):
            raise ValueError(f"expected vector of length {len(basis)}, got {len(vector)}")
        return cls(degree, {exp: Fq(coeff) for exp, coeff in zip(basis, vector) if Fq(coeff)})

    def to_vector(self) -> Vector:
        index = {exp: i for i, exp in enumerate(degree_monomials(self.degree))}
        vec = [ZERO] * len(index)
        for exp, coeff in self.terms:
            vec[index[exp]] = coeff
        return tuple(vec)

    def reduce_fermat(self) -> "HomogPoly":
        """Return the canonical representative modulo X^4 + Y^4 + Z^4."""

        if self.degree < 4:
            return HomogPoly(self.degree, dict(self.terms))
        out_terms: dict[tuple[int, int, int], Fq] = {}
        pending = dict(self.terms)
        while pending:
            next_pending: dict[tuple[int, int, int], Fq] = {}
            for (a, b, c), coeff in pending.items():
                if a < 4:
                    out_terms[(a, b, c)] = out_terms.get((a, b, c), ZERO) + coeff
                    continue
                neg = -coeff
                for exp in ((a - 4, b + 4, c), (a - 4, b, c + 4)):
                    next_pending[exp] = next_pending.get(exp, ZERO) + neg
            pending = next_pending
        return HomogPoly(
            self.degree,
            {exp: coeff for exp, coeff in out_terms.items() if coeff},
        )

    def __add__(self, other: object) -> "HomogPoly":
        rhs = other if isinstance(other, HomogPoly) else HomogPoly(self.degree, {})
        if not isinstance(rhs, HomogPoly):
            return NotImplemented  # type: ignore[return-value]
        if self.degree != rhs.degree:
            raise ValueError("cannot add homogeneous polynomials of different degrees")
        terms: dict[tuple[int, int, int], Fq] = defaultdict(lambda: ZERO)
        for exp, coeff in self.terms:
            terms[exp] += coeff
        for exp, coeff in rhs.terms:
            terms[exp] += coeff
        return HomogPoly(self.degree, terms)

    def __neg__(self) -> "HomogPoly":
        return HomogPoly(self.degree, {exp: -coeff for exp, coeff in self.terms})

    def __sub__(self, other: object) -> "HomogPoly":
        if not isinstance(other, HomogPoly):
            return NotImplemented  # type: ignore[return-value]
        return self + (-other)

    def __mul__(self, other: object) -> "HomogPoly":
        if not isinstance(other, HomogPoly):
            scalar = Fq(other)
            return HomogPoly(self.degree, {exp: scalar * coeff for exp, coeff in self.terms})
        terms: dict[tuple[int, int, int], Fq] = defaultdict(lambda: ZERO)
        for (a1, b1, c1), coeff1 in self.terms:
            for (a2, b2, c2), coeff2 in other.terms:
                terms[(a1 + a2, b1 + b2, c1 + c2)] += coeff1 * coeff2
        return HomogPoly(self.degree + other.degree, terms)

    def __rmul__(self, other: object) -> "HomogPoly":
        return self * other

    def evaluate(self, point: Point) -> Fq:
        x, y, z = point
        total = ZERO
        for (a, b, c), coeff in self.terms:
            total += coeff * (x**a) * (y**b) * (z**c)
        return total

    def to_json(self) -> list[dict[str, object]]:
        return [
            {"monomial": list(exp), "coefficient": coeff.to_json()}
            for exp, coeff in self.terms
        ]


def rref_rows(rows: Iterable[Sequence[object]], ncols: int | None = None) -> tuple[list[Vector], tuple[int, ...]]:
    matrix = [list(Fq(x) for x in row) for row in rows]
    if ncols is None:
        ncols = max((len(row) for row in matrix), default=0)
    for row in matrix:
        if len(row) != ncols:
            raise ValueError("all rows must have the same width")

    pivots: list[int] = []
    r = 0
    for c in range(ncols):
        pivot = next((i for i in range(r, len(matrix)) if matrix[i][c]), None)
        if pivot is None:
            continue
        matrix[r], matrix[pivot] = matrix[pivot], matrix[r]
        inv = matrix[r][c].inverse()
        matrix[r] = [value * inv for value in matrix[r]]
        for i in range(len(matrix)):
            if i == r or not matrix[i][c]:
                continue
            factor = matrix[i][c]
            matrix[i] = [a - factor * b for a, b in zip(matrix[i], matrix[r])]
        pivots.append(c)
        r += 1
        if r == len(matrix):
            break

    nonzero = [tuple(row) for row in matrix if any(row)]
    return nonzero, tuple(pivots)


def matrix_rank(rows: Iterable[Sequence[object]], ncols: int | None = None) -> int:
    return len(rref_rows(rows, ncols)[0])


def nullspace(rows: Iterable[Sequence[object]], ncols: int) -> list[Vector]:
    rref, pivots = rref_rows(rows, ncols)
    pivot_set = set(pivots)
    free_cols = [c for c in range(ncols) if c not in pivot_set]
    basis: list[Vector] = []
    for free in free_cols:
        vec = [ZERO] * ncols
        vec[free] = ONE
        for row_index, pivot in enumerate(pivots):
            vec[pivot] = -rref[row_index][free]
        basis.append(tuple(vec))
    return basis


def _linear_combination(coeffs: Sequence[Fq], rows: Sequence[Vector], ncols: int) -> Vector:
    out = [ZERO] * ncols
    for coeff, row in zip(coeffs, rows):
        if not coeff:
            continue
        out = [a + coeff * b for a, b in zip(out, row)]
    return tuple(out)


@dataclass(frozen=True)
class Subspace:
    """Row-space subspace of F_q^n, stored in canonical RREF."""

    ambient_dim: int
    rows: tuple[Vector, ...] = ()
    pivots: tuple[int, ...] = ()

    def __init__(self, rows: Iterable[Sequence[object]], ambient_dim: int):
        rref, pivots = rref_rows(rows, ambient_dim)
        object.__setattr__(self, "ambient_dim", ambient_dim)
        object.__setattr__(self, "rows", tuple(rref))
        object.__setattr__(self, "pivots", pivots)

    @property
    def dimension(self) -> int:
        return len(self.rows)

    @property
    def rank(self) -> int:
        return self.dimension

    @classmethod
    def zero(cls, ambient_dim: int) -> "Subspace":
        return cls([], ambient_dim)

    @classmethod
    def full(cls, ambient_dim: int) -> "Subspace":
        return cls(
            [
                [ONE if i == j else ZERO for j in range(ambient_dim)]
                for i in range(ambient_dim)
            ],
            ambient_dim,
        )

    def contains(self, vector: Sequence[object]) -> bool:
        if len(vector) != self.ambient_dim:
            raise ValueError("vector length does not match ambient dimension")
        return matrix_rank([*self.rows, tuple(Fq(x) for x in vector)], self.ambient_dim) == self.dimension

    def span(self, other: "Subspace") -> "Subspace":
        self._check_same_ambient(other)
        return Subspace([*self.rows, *other.rows], self.ambient_dim)

    def intersection(self, other: "Subspace") -> "Subspace":
        self._check_same_ambient(other)
        r = self.dimension
        s = other.dimension
        equations: list[list[Fq]] = []
        for col in range(self.ambient_dim):
            equations.append(
                [self.rows[i][col] for i in range(r)]
                + [-other.rows[j][col] for j in range(s)]
            )
        ker = nullspace(equations, r + s)
        vectors = [_linear_combination(vec[:r], self.rows, self.ambient_dim) for vec in ker]
        return Subspace(vectors, self.ambient_dim)

    def _check_same_ambient(self, other: "Subspace") -> None:
        if self.ambient_dim != other.ambient_dim:
            raise ValueError("subspaces have different ambient dimensions")

    def to_json(self) -> list[list[list[int]]]:
        return [[entry.to_json() for entry in row] for row in self.rows]


def evaluation_matrix(points: Sequence[Point], degree: int) -> list[Vector]:
    basis = [HomogPoly.monomial(exp) for exp in degree_monomials(degree)]
    return [tuple(poly.evaluate(point) for poly in basis) for point in points]


def vanishing_subspace(points: Sequence[Point], degree: int) -> Subspace:
    """Return H^0(Y,O(degree)) sections vanishing on the given split points."""

    ambient = h0_dimension(degree)
    equations = evaluation_matrix(points, degree)
    return Subspace(nullspace(equations, ambient), ambient)


def _degree_from_ambient_dim(ambient_dim: int) -> int:
    for degree in range(max(0, ambient_dim + 1)):
        if h0_dimension(degree) == ambient_dim:
            return degree
    raise ValueError(f"ambient dimension {ambient_dim} is not a Fermat-quartic H0 dimension")


def multiply_subspaces(W_A: Subspace, W_B: Subspace, target_degree: int) -> Subspace:
    degree_a = _degree_from_ambient_dim(W_A.ambient_dim)
    degree_b = _degree_from_ambient_dim(W_B.ambient_dim)
    if degree_a + degree_b != target_degree:
        raise ValueError(
            "target_degree must equal the sum of the source homogeneous degrees "
            f"({degree_a} + {degree_b} != {target_degree})"
        )

    target_ambient = h0_dimension(target_degree)
    product_rows: list[Vector] = []
    for row_a in W_A.rows:
        poly_a = HomogPoly.from_vector(degree_a, row_a)
        for row_b in W_B.rows:
            poly_b = HomogPoly.from_vector(degree_b, row_b)
            product_rows.append((poly_a * poly_b).reduce_fermat().to_vector())
    return Subspace(product_rows, target_ambient)


def _quotient_coordinates_mod_subspace(vector: Sequence[object], subspace: Subspace) -> Vector:
    if len(vector) != subspace.ambient_dim:
        raise ValueError("vector length does not match quotient ambient dimension")
    reduced = [Fq(x) for x in vector]
    pivot_set = set(subspace.pivots)
    nonpivots = [col for col in range(subspace.ambient_dim) if col not in pivot_set]
    for row, pivot in zip(subspace.rows, subspace.pivots):
        factor = reduced[pivot]
        if not factor:
            continue
        reduced = [value - factor * row_value for value, row_value in zip(reduced, row)]
    return tuple(reduced[col] for col in nonpivots)


def divide_subspaces(
    W_A: Subspace,
    W_C: Subspace,
    source_degree_a: int,
    source_degree_c: int,
) -> Subspace:
    """Khuri-Makdisi ideal quotient: return W_{A/C} in H^0(O_Y((a-c)D_0)).

    The quotient is the subspace of sections t such that t * W_C is contained
    in W_A.  Coordinates are taken in the canonical Fermat basis at each
    homogeneous degree.
    """

    if source_degree_a <= source_degree_c:
        raise ValueError("source_degree_a must be greater than source_degree_c")
    if W_A.ambient_dim != h0_dimension(source_degree_a):
        raise ValueError("W_A ambient dimension does not match source_degree_a")
    if W_C.ambient_dim != h0_dimension(source_degree_c):
        raise ValueError("W_C ambient dimension does not match source_degree_c")

    target_degree = source_degree_a - source_degree_c
    target_ambient = h0_dimension(target_degree)
    quotient_dim = W_A.ambient_dim - W_A.dimension
    if quotient_dim == 0 or W_C.dimension == 0:
        return Subspace.full(target_ambient)

    target_basis = [HomogPoly.monomial(exp) for exp in degree_monomials(target_degree)]
    constraint_rows: list[Vector] = []
    for row_c in W_C.rows:
        poly_c = HomogPoly.from_vector(source_degree_c, row_c)
        quotient_columns = [
            _quotient_coordinates_mod_subspace(
                (poly_t * poly_c).reduce_fermat().to_vector(),
                W_A,
            )
            for poly_t in target_basis
        ]
        for quotient_coord in range(quotient_dim):
            constraint_rows.append(
                tuple(column[quotient_coord] for column in quotient_columns)
            )

    return Subspace(nullspace(constraint_rows, target_ambient), target_ambient)


def saturate_to_smaller_ambient(
    W_prod: Subspace,
    search_degree: int,
    multiplier_degree: int = 2,
) -> Subspace:
    """Khuri-Makdisi step 3 saturation/lift-to-lower-degree.

    Return the subspace

        U = {s in H^0(O_Y(search_degree)) :
             s * H^0(O_Y(multiplier_degree)) is contained in W_prod}.

    In the present Fermat-quartic K1 scaffold, a degree-4 K1 representative
    multiplied by another degree-4 representative lands in degree 8.  The
    divisor-support component is recovered in degree 6 by testing products
    against the full degree-2 ambient, i.e. search_degree=6 and
    multiplier_degree=2.  Coordinates use the canonical Fermat quotient basis.
    """

    product_degree = _degree_from_ambient_dim(W_prod.ambient_dim)
    if search_degree < 0 or multiplier_degree < 0:
        raise ValueError("search_degree and multiplier_degree must be nonnegative")
    if search_degree + multiplier_degree != product_degree:
        raise ValueError(
            "search_degree + multiplier_degree must equal W_prod's homogeneous degree "
            f"({search_degree} + {multiplier_degree} != {product_degree})"
        )

    search_ambient = h0_dimension(search_degree)
    quotient_dim = W_prod.ambient_dim - W_prod.dimension
    if quotient_dim == 0:
        return Subspace.full(search_ambient)

    search_basis = [HomogPoly.monomial(exp) for exp in degree_monomials(search_degree)]
    multiplier_basis = [
        HomogPoly.monomial(exp) for exp in degree_monomials(multiplier_degree)
    ]
    constraint_rows: list[Vector] = []

    for poly_t in multiplier_basis:
        quotient_columns = [
            _quotient_coordinates_mod_subspace(
                (poly_s * poly_t).reduce_fermat().to_vector(),
                W_prod,
            )
            for poly_s in search_basis
        ]
        for quotient_coord in range(quotient_dim):
            constraint_rows.append(
                tuple(column[quotient_coord] for column in quotient_columns)
            )

    return Subspace(nullspace(constraint_rows, search_ambient), search_ambient)


def _multiply_subspace_by_base_conic_power(
    W: Subspace,
    source_degree: int,
    power: int,
) -> Subspace:
    if power < 0:
        raise ValueError("power must be nonnegative")
    if W.ambient_dim != h0_dimension(source_degree):
        raise ValueError("subspace ambient does not match source_degree")
    if power == 0:
        return W

    base_conic_poly = HomogPoly.monomial((1, 0, 1))
    multiplier = base_conic_poly
    for _ in range(power - 1):
        multiplier = multiplier * base_conic_poly
    target_degree = source_degree + 2 * power
    return Subspace(
        [
            (HomogPoly.from_vector(source_degree, row) * multiplier)
            .reduce_fermat()
            .to_vector()
            for row in W.rows
        ],
        h0_dimension(target_degree),
    )


def _multiply_subspace_by_poly(W: Subspace, source_degree: int, poly: HomogPoly) -> Subspace:
    if W.ambient_dim != h0_dimension(source_degree):
        raise ValueError("subspace ambient does not match source_degree")
    return Subspace(
        [
            (HomogPoly.from_vector(source_degree, row) * poly)
            .reduce_fermat()
            .to_vector()
            for row in W.rows
        ],
        h0_dimension(source_degree + poly.degree),
    )


def _principal_zero_factor(W: Subspace, source_degree: int) -> HomogPoly | None:
    """Return f when W = f * H^0(O_Y(2)), else None.

    In this K1 degree convention a representative of the zero Picard class in
    degree n is not unique: the fixed base representative is Q0^(...) times
    H^0(O_Y(2)), but a principal relation may naturally produce f*H^0(O_Y(2))
    for another nonzero section f.  Detecting that common factor is the
    canonical-reduction check needed by negation.
    """

    if source_degree < 2 or W.ambient_dim != h0_dimension(source_degree):
        return None
    if W.dimension != h0_dimension(2):
        return None

    full_h2 = Subspace.full(h0_dimension(2))
    try:
        factors = divide_subspaces(W, full_h2, source_degree, 2)
    except ValueError:
        return None
    for row in factors.rows:
        factor = HomogPoly.from_vector(source_degree - 2, row)
        if _multiply_subspace_by_poly(full_h2, 2, factor) == W:
            return factor
    return None


KM_STEP_2_BLOCKER = (
    "KM step 2 blocker: ideal quotient (W_prod : H⁰(O_Y((n₁+n₂)·D₀))) — "
    "division step to extract effective divisor support"
)
KM_STEP_3_BLOCKER = (
    "KM step 3 blocker: saturation + reduction back to canonical degree-4 representative"
)


@dataclass(frozen=True)
class K1Divisor:
    """Partial Khuri-Makdisi K1 divisor-class representation.

    The base divisor is D0 = div(Q0) for the conic Q0 = X*Z, so
    deg(D0)=8 and H^0(2D0)=H^0(O_Y(4)) has dimension 14.  A generic class
    [E-D0] is represented by W_E = H^0(O_Y(4)(-E)), a six-dimensional
    subspace by Riemann-Roch.  Construction from split points and equality are
    implemented.
    Addition/negation/halving still require the KM reduction/division
    subroutine and therefore raise ArithmeticBlocker instead of fabricating a
    group law.
    """

    W: Subspace
    support: tuple[Point, ...] = ()
    d0: int = 8
    section_degree: int = 4

    @property
    def W_E(self) -> Subspace:
        return self.W

    @property
    def degree(self) -> int:
        return self.section_degree

    @classmethod
    def zero(cls) -> "K1Divisor":
        return cls.from_effective_divisor(base_divisor_points())

    @classmethod
    def from_effective_divisor(cls, points: Sequence[Point]) -> "K1Divisor":
        normalized = tuple(normalize_projective(point) for point in points)
        if len(normalized) != 8:
            raise ValueError("K1 representation expects an effective divisor of degree 8")
        for point in normalized:
            if not on_curve(point):
                raise ValueError(f"point is not on {Y_EQUATION}: {point!r}")
        W = vanishing_subspace(normalized, 4)
        return cls(W=W, support=normalized)

    @classmethod
    def from_points(cls, P_point: Point, Q_point: Point) -> "K1Divisor":
        """Construct the K1 representative of the degree-zero class [Q-P].

        In this scaffold's convention a K1 representative is [E-D0] with
        E effective of degree 8.  Therefore [Q-P] is represented directly
        when E = D0 + Q - P is effective, i.e. when P is in the split base
        divisor D0 and Q is not.  This is enough for explicit Fermat-flex
        witnesses using a base-axis flex P and a Y=0 flex Q.
        """

        P_norm = normalize_projective(P_point)
        Q_norm = normalize_projective(Q_point)
        if not on_curve(P_norm) or not on_curve(Q_norm):
            raise ValueError("from_points expects points on the Fermat quartic")
        if P_norm == Q_norm:
            return cls.zero()

        base = base_divisor_points()
        base_set = set(base)
        if P_norm not in base_set:
            raise ArithmeticBlocker(
                "k1/from_points/base_support",
                (
                    "direct construction of [Q-P] requires P in D0 so that "
                    "D0 + Q - P is an effective degree-8 divisor"
                ),
            )
        if Q_norm in base_set:
            raise ArithmeticBlocker(
                "k1/from_points/base_support",
                (
                    "direct construction of [Q-P] requires Q outside D0; "
                    "otherwise D0 + Q - P has a repeated/base cancellation "
                    "case not implemented by this partial K1 constructor"
                ),
            )
        E = [point for point in base if point != P_norm]
        E.append(Q_norm)
        return cls.from_effective_divisor(E)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, K1Divisor):
            return NotImplemented
        return self.equals(other)

    def equals(self, other: "K1Divisor") -> bool:
        if not isinstance(other, K1Divisor):
            return False
        if self.section_degree == other.section_degree:
            if self.W == other.W:
                return True
            return (
                _principal_zero_factor(self.W, self.section_degree) is not None
                and _principal_zero_factor(other.W, other.section_degree) is not None
            )
        if (self.section_degree - other.section_degree) % 2:
            return False
        if self.section_degree < other.section_degree:
            lifted = _multiply_subspace_by_base_conic_power(
                self.W,
                self.section_degree,
                (other.section_degree - self.section_degree) // 2,
            )
            if lifted == other.W:
                return True
            return (
                _principal_zero_factor(lifted, other.section_degree) is not None
                and _principal_zero_factor(other.W, other.section_degree) is not None
            )
        lifted = _multiply_subspace_by_base_conic_power(
            other.W,
            other.section_degree,
            (self.section_degree - other.section_degree) // 2,
        )
        if self.W == lifted:
            return True
        return (
            _principal_zero_factor(self.W, self.section_degree) is not None
            and _principal_zero_factor(other.W, other.section_degree) is not None
        )

    def _expected_k1_dimension(self) -> int:
        return self.d0 + 1 - GENUS

    def _check_k1_shape(self) -> None:
        if self.W.ambient_dim != h0_dimension(self.section_degree):
            raise ValueError("K1 divisor W ambient does not match section_degree")
        if self.W.dimension != self._expected_k1_dimension():
            raise ArithmeticBlocker(
                "k1/subspace_shape",
                (
                    f"expected K1 subspace dimension {self._expected_k1_dimension()}, "
                    f"got {self.W.dimension} in H^0(O_Y({self.section_degree}))"
                ),
            )

    def add(self, other: "K1Divisor") -> "K1Divisor":
        if not isinstance(other, K1Divisor):
            return NotImplemented  # type: ignore[return-value]
        self._check_k1_shape()
        other._check_k1_shape()
        W_prod = multiply_subspaces(
            self.W_E,
            other.W_E,
            target_degree=self.degree + other.degree,
        )
        # KM step 3 in the actual degree convention of this scaffold:
        # degree-m and degree-n representatives multiply to degree m+n; the
        # saturated representative is searched in degree m+n-2 and tested by
        # multiplication with H^0(O_Y(2)), the base-conic degree.
        saturated_degree = self.degree + other.degree - 2
        W_sat = saturate_to_smaller_ambient(
            W_prod,
            search_degree=saturated_degree,
            multiplier_degree=2,
        )
        if W_sat.dimension != self._expected_k1_dimension():
            raise ArithmeticBlocker(
                "k1/add_km_step_3_saturation_bad_dimension",
                (
                    "computed W_prod = W_E1 * W_E2 in "
                    f"H^0(O_Y({self.degree + other.degree})) with dimension "
                    f"{W_prod.dimension}; saturated in H^0(O_Y({saturated_degree})) "
                    f"with dimension {W_sat.dimension}, expected "
                    f"{self._expected_k1_dimension()}"
                ),
            )
        return K1Divisor(
            W=W_sat,
            support=(),
            d0=self.d0,
            section_degree=saturated_degree,
        )

    def neg(self) -> "K1Divisor":
        self._check_k1_shape()
        if not self.W.rows:
            raise ArithmeticBlocker(
                "k1/neg_empty_subspace",
                "cannot form residual complement from an empty K1 subspace",
            )

        section = HomogPoly.from_vector(self.degree, self.W.rows[0])
        full_same_degree = Subspace.full(h0_dimension(self.degree))
        principal_product = _multiply_subspace_by_poly(
            full_same_degree,
            self.degree,
            section,
        )
        W_neg = divide_subspaces(
            principal_product,
            self.W_E,
            source_degree_a=2 * self.degree,
            source_degree_c=self.degree,
        )
        if W_neg.dimension != self._expected_k1_dimension():
            raise ArithmeticBlocker(
                "k1/neg_residual_bad_dimension",
                (
                    "residual ideal quotient produced dimension "
                    f"{W_neg.dimension} in H^0(O_Y({self.degree})); expected "
                    f"{self._expected_k1_dimension()}"
                ),
            )
        return K1Divisor(
            W=W_neg,
            support=(),
            d0=self.d0,
            section_degree=self.degree,
        )

    def double(self) -> "K1Divisor":
        return self.add(self)

    def __add__(self, other: "K1Divisor") -> "K1Divisor":
        return self.add(other)

    def __rmul__(self, scalar: int) -> "K1Divisor":
        if not isinstance(scalar, int):
            return NotImplemented  # type: ignore[return-value]
        if scalar < 0:
            return (-scalar) * self.neg()
        result = K1Divisor.zero()
        addend = self
        n = scalar
        while n:
            if n & 1:
                result = result.add(addend)
            n >>= 1
            if n:
                addend = addend.double()
        return result

    def __mul__(self, scalar: int) -> "K1Divisor":
        return self.__rmul__(scalar)

    def order(self, bound: int | None = None) -> int:
        raise ArithmeticBlocker(
            "k1/order_requires_group_law",
            "order computation needs completed add/double/reduce operations",
        )

    @staticmethod
    def halve(T_class: "K1Divisor") -> list["K1Divisor"]:
        raise ArithmeticBlocker(
            "k1/halve_requires_4096_enumeration",
            "halving requires a completed JY[4] group law or an exact 4096-class K1 enumeration",
        )

    def to_json(self) -> dict[str, object]:
        return {
            "d0": self.d0,
            "section_degree": self.section_degree,
            "support": [point_to_json(point) for point in self.support],
            "W_dimension": self.W.dimension,
            "W": self.W.to_json(),
        }


def explicit_flex_pair_witness(flexes: Sequence[Point] | None = None) -> tuple[Point, Point, K1Divisor]:
    """Return the direct K1 flex-pair witness (P,Q,[Q-P])."""

    selected = list(compute_fermat_flex_points() if flexes is None else flexes)
    if len(selected) < 2:
        raise ValueError("need at least two flex points")
    P_point, Q_point = selected[0], selected[1]
    return P_point, Q_point, K1Divisor.from_points(P_point, Q_point)


def find_2torsion_and_halver(flexes: Sequence[Point] | None = None) -> tuple[K1Divisor, K1Divisor]:
    """Return a K1 two-torsion class T and an explicit flex-pair halver D.

    This is intentionally not a 4096-class enumeration.  It uses the explicit
    flex-pair D=[Q-P] from ``explicit_flex_pair_witness`` and sets T=2D.  The
    caller can verify 2T=0 by computing 4D=0 in the K1 engine.
    """

    _, _, D_L = explicit_flex_pair_witness(flexes)
    return 2 * D_L, D_L


def find_witness_with_flexes(
    flexes: Sequence[Point] | None = None,
) -> tuple[K1Divisor, K1Divisor, Point, Point]:
    selected = list(compute_fermat_flex_points() if flexes is None else flexes)
    P_point, Q_point, D_L = explicit_flex_pair_witness(selected)
    T_class = 2 * D_L
    # D_L = [Q-P], while div(T_Q/T_P)=4Q-4P.  Return the tangent-ratio
    # arguments in the order that matches 4D_L.
    return T_class, D_L, Q_point, P_point


@dataclass(frozen=True)
class TangentRatio:
    """Rational function T_P/T_Q on the Fermat quartic for flexes P,Q."""

    numerator_flex: Point
    denominator_flex: Point
    numerator_line: Line
    denominator_line: Line

    def formal_divisor(self) -> dict[Point, int]:
        """Return the formal divisor div(T_P/T_Q)=4P-4Q."""

        P_point = normalize_projective(self.numerator_flex)
        Q_point = normalize_projective(self.denominator_flex)
        if P_point == Q_point:
            return {}
        return {P_point: 4, Q_point: -4}

    def divisor(self) -> K1Divisor:
        """Return the Picard-class image of the principal divisor, namely zero."""

        return K1Divisor.zero()

    def to_json(self) -> dict[str, object]:
        return {
            "function": "T_P/T_Q",
            "P": point_to_json(self.numerator_flex),
            "Q": point_to_json(self.denominator_flex),
            "numerator_line": [coord.to_json() for coord in self.numerator_line],
            "denominator_line": [coord.to_json() for coord in self.denominator_line],
            "formal_divisor": divisor_to_json(self.formal_divisor()),
        }


def construct_tangent_ratio(P_point: Point, Q_point: Point) -> TangentRatio:
    P_norm = normalize_projective(P_point)
    Q_norm = normalize_projective(Q_point)
    if P_norm == Q_norm:
        raise ValueError("tangent ratio needs two distinct flex points")
    flex_set = set(compute_fermat_flex_points())
    if P_norm not in flex_set or Q_norm not in flex_set:
        raise ValueError("tangent ratio is only implemented for Fermat flex points")
    return TangentRatio(
        numerator_flex=P_norm,
        denominator_flex=Q_norm,
        numerator_line=partials(P_norm),
        denominator_line=partials(Q_norm),
    )


def base_conic(point: Point) -> Fq:
    x, y, z = point
    return x * z


def base_divisor_points(points: Iterable[Point] | None = None) -> list[Point]:
    """Split support of D0 = div(X*Z).

    The two coordinate lines X=0 and Z=0 each contribute four distinct
    F_11^4-points and their supports are disjoint on the Fermat quartic.
    """

    search_points = enumerate_curve_points() if points is None else list(points)
    out = [point for point in search_points if base_conic(point) == ZERO]
    if len(out) != 8:
        raise ArithmeticBlocker(
            "k1/base_divisor_selection",
            f"expected split degree-8 base conic divisor, found {len(out)} points",
        )
    return sorted(out)


def random_effective_divisor(seed: int, degree: int = 8) -> list[Point]:
    """Deterministic pseudo-random split effective divisor for validator smoke tests."""

    points = enumerate_curve_points()
    if degree > len(points):
        raise ValueError("degree exceeds available split points")
    # LCG over indices; deterministic and stdlib-free.
    state = seed % (2**31 - 1) or 1
    chosen: list[Point] = []
    used: set[int] = set()
    while len(chosen) < degree:
        state = (1103515245 * state + 12345) % (2**31 - 1)
        idx = state % len(points)
        if idx in used:
            continue
        used.add(idx)
        chosen.append(points[idx])
    return chosen


def materialize_function(D: K1Divisor, multiplier: int) -> HomogPoly:
    raise ArithmeticBlocker(
        "k1/materialize_function_principal_relation",
        "constructing f with div(f)=mD needs completed KM principality/division machinery",
    )


class ReducedDivisor:
    """Degree-zero divisor class placeholder for Pic^0(Y).

    The class stores a normalized formal divisor.  It can canonicalize the zero
    divisor and already-reduced effective placeholders of degree <=3, but it
    intentionally blocks nontrivial Picard reduction.  This is the exact
    missing substep from the current local audit.
    """

    def __init__(
        self,
        points: Iterable[Point] | None = None,
        divisor: dict[Point, int] | None = None,
        mumford: object | None = None,
    ):
        if mumford is not None:
            raise ArithmeticBlocker(
                "init/mumford_nonhyperelliptic",
                "Mumford representation is not native for a smooth plane quartic genus-3 curve",
            )
        data: dict[Point, int] = {}
        if divisor:
            for point, coeff in divisor.items():
                if not on_curve(point):
                    raise ValueError(f"point is not on {Y_EQUATION}: {point!r}")
                data[normalize_projective(point)] = data.get(normalize_projective(point), 0) + coeff
        if points:
            for point in points:
                if not on_curve(point):
                    raise ValueError(f"point is not on {Y_EQUATION}: {point!r}")
                npt = normalize_projective(point)
                data[npt] = data.get(npt, 0) + 1
        self.divisor = normalize_divisor_dict(data)
        self._canonical = self._canonical_form_or_block()

    @classmethod
    def zero(cls) -> "ReducedDivisor":
        return cls(divisor={})

    def _canonical_form_or_block(self) -> tuple[tuple[Point, int], ...]:
        if not self.divisor:
            return ()
        if divisor_degree(self.divisor) == 0 and all(coeff == 0 for coeff in self.divisor.values()):
            return ()
        raise ArithmeticBlocker(
            "reduce/nonhyperelliptic_plane_quartic",
            "nontrivial Pic^0 reduction needs Khuri-Makdisi/Volcheck flex-secant arithmetic",
        )

    def reduce(self) -> "ReducedDivisor":
        self._canonical_form_or_block()
        return self

    def add(self, other: "ReducedDivisor") -> "ReducedDivisor":
        if not self.divisor:
            return other
        if not other.divisor:
            return self
        combined = dict(self.divisor)
        for point, coeff in other.divisor.items():
            combined[point] = combined.get(point, 0) + coeff
        raise ArithmeticBlocker(
            "add/reduce",
            "formal divisor addition reached the missing non-hyperelliptic reduction step",
        )

    def double(self) -> "ReducedDivisor":
        return self.add(self)

    @staticmethod
    def halve(T_class: "ReducedDivisor") -> "ReducedDivisor":
        raise ArithmeticBlocker(
            "halve/outside_2H",
            "no full JY[4] group law is available to solve 2D=T outside 2H",
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ReducedDivisor):
            return NotImplemented
        return self._canonical == other._canonical

    def __repr__(self) -> str:
        return f"ReducedDivisor({divisor_to_json(self.divisor)!r})"


def self_test() -> dict[str, object]:
    a = T + Fq((3, 0, 2, 1))
    inv_ok = a * a.inverse() == ONE
    frob_ok = a.frobenius(4) == a and a.frobenius(1) != a
    count_ok = count_curve_points_fast() == EXPECTED_Y_F11_4_POINTS
    zero_ok = ReducedDivisor.zero().add(ReducedDivisor.zero()) == ReducedDivisor.zero()
    blockers: list[str] = []
    try:
        ReducedDivisor(mumford=("u", "v"))
    except ArithmeticBlocker as exc:
        blockers.append(exc.substep)
    hpts = hyperflex_points()
    nonzero_blocked = False
    try:
        ReducedDivisor(divisor={hpts[0]: 1, hpts[1]: -1})
    except ArithmeticBlocker as exc:
        nonzero_blocked = exc.substep == "reduce/nonhyperelliptic_plane_quartic"
        blockers.append(exc.substep)
    return {
        "field_inverse": inv_ok,
        "frobenius_order_4": frob_ok,
        "curve_point_count": count_ok,
        "zero_divisor_addition": zero_ok,
        "nontrivial_reduction_blocked": nonzero_blocked,
        "blockers": blockers,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(self_test(), indent=2, sort_keys=True))
