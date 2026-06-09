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

from collections import Counter
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
