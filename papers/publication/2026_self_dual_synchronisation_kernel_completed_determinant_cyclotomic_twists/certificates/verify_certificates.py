#!/usr/bin/env sage -python
"""Exact certificate runner for the self-dual kernel paper.

Run from the repository root with

    sage -python certificates/verify_certificates.py

The script prints deterministic exact outputs for the determinant,
completion, quotient, smoothness, Galois specialisations, endpoint
recursion, and finite branch-selection checks cited in the appendix.
It intentionally uses only SageMath's exact rings except for the final
small-m numerical root display.
"""

import hashlib
import json
import platform
from pathlib import Path

from sage.all import (
    ComplexField,
    GF,
    QQ,
    QuadraticField,
    PolynomialRing,
    LaurentPolynomialRing,
    SR,
    cos,
    gcd,
    identity_matrix,
    matrix,
    pi,
    sage_version,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = {}


def record(key, value):
    OUT[key] = str(value)
    print(f"{key}: {value}")


def sha256(path):
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def _variations(signs):
    nz = [s for s in signs if s != 0]
    return sum(1 for a, b in zip(nz, nz[1:]) if a * b < 0)


def _sign(value):
    if value > 0:
        return 1
    if value < 0:
        return -1
    return 0


def sturm_count(poly, left, right):
    """Count real roots in (left,right) for a QQ univariate polynomial."""
    if poly.is_zero():
        raise ValueError("zero polynomial has no finite Sturm count")
    f = poly.squarefree_part()
    seq = f.sturm_sequence()
    left_signs = [_sign(p(left)) for p in seq]
    right_signs = [_sign(p(right)) for p in seq]
    return _variations(left_signs) - _variations(right_signs)


def circle_crossing_polynomial(radius):
    """Return a QQ[s] polynomial whose zeros contain circle crossings.

    For real s, a root of H(w,s) on |w|=radius gives a real parameter t
    under w = radius*((1-t^2)+2*i*t)/(1+t^2). Eliminating t from the
    real and imaginary parts gives the crossing polynomial.
    """
    K = QuadraticField(-1, names=("ii",))
    ii = K.gen()
    P = PolynomialRing(K, names=("s", "t"))
    ss, tt = P.gens()
    rr = K(radius)
    ww = rr * ((1 - tt**2) + 2 * ii * tt) / (1 + tt**2)
    expr = (
        1 - ss * ww - 5 * ww**2 + 3 * ss * ww**3
        + (5 - ss**2) * ww**4 + (ss**3 - 6 * ss) * ww**5
        + (ss**2 - 1) * ww**6
    ) * (1 + tt**2) ** 6
    expr = P(expr)
    real = P.zero()
    imag = P.zero()
    for mon, coeff in expr.dict().items():
        real += QQ(coeff[0]) * ss**mon[0] * tt**mon[1]
        imag += QQ(coeff[1]) * ss**mon[0] * tt**mon[1]
    res = real.resultant(imag, tt)
    Q = PolynomialRing(QQ, names=("s",))
    return Q(res)


def no_circle_crossings(radius, left, right):
    Q = PolynomialRing(QQ, names=("s",))
    ss = Q.gen()
    cross = circle_crossing_polynomial(radius)
    endpoint_plus = (
        1 - ss * radius - 5 * radius**2 + 3 * ss * radius**3
        + (5 - ss**2) * radius**4 + (ss**3 - 6 * ss) * radius**5
        + (ss**2 - 1) * radius**6
    )
    endpoint_minus = (
        1 + ss * radius - 5 * radius**2 - 3 * ss * radius**3
        + (5 - ss**2) * radius**4 - (ss**3 - 6 * ss) * radius**5
        + (ss**2 - 1) * radius**6
    )
    return (
        sturm_count(cross, left, right) == 0
        and sturm_count(endpoint_plus, left, right) == 0
        and sturm_count(endpoint_minus, left, right) == 0
    )


def polynomial_negative_on(poly, left, right):
    crit = poly.derivative()
    points = [left, right]
    roots = crit.roots(QQ, multiplicities=False)
    points.extend(root for root in roots if left < root < right)
    return all(poly(point) < 0 for point in points)


def main():
    print("sage_version:", sage_version)
    print("python_version:", platform.python_version())
    for rel in [
        "main.tex",
        "sec_introduction.tex",
        "sec_preliminaries.tex",
        "sec_kernel.tex",
        "sec_conclusion.tex",
        "references.bib",
        "certificates/verify_certificates.py",
    ]:
        p = ROOT / rel
        if p.exists():
            print(f"sha256 {rel}: {sha256(p)}")

    R = PolynomialRing(QQ, names=("u", "z"))
    u, z = R.gens()
    B = matrix(R, [
        [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
        [u, u, 0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 1, 1, u, 0, 0, 0],
        [u, u, u, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, u, u, u, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
        [0, 0, 0, u, u, 0, 0, 0, u, 0],
        [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
        [0, u, u, 0, 0, 0, 0, u, 0, 0],
    ])
    Delta = (identity_matrix(R, 10) - z * B).det().expand()
    Delta_closed = (
        1 - (1 + u) * z - 5 * u * z**2 + 3 * u * (1 + u) * z**3
        - u * (u**2 - 3 * u + 1) * z**4
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * z**5
        + u**2 * (u**2 + u + 1) * z**6
    )
    record("determinant_difference", (Delta - Delta_closed).expand())
    record("determinant_at_u_1", Delta_closed.subs(u=1).factor())

    L = LaurentPolynomialRing(QQ, names=("u", "z"))
    ul, zl = L.gens()
    DeltaL = L(str(Delta_closed))
    dual = DeltaL(ul * zl, 1 / ul)
    record("self_duality_difference", (dual - DeltaL).expand())

    S = PolynomialRing(QQ, names=("w", "s"))
    w, s = S.gens()
    H = (
        1 - s * w - 5 * w**2 + 3 * s * w**3
        + (5 - s**2) * w**4 + (s**3 - 6 * s) * w**5
        + (s**2 - 1) * w**6
    )
    record("completed_determinant", H)

    T = PolynomialRing(QQ, names=("x", "y"))
    x, y = T.gens()
    F = (
        1 - y - 5 * x + 3 * x * y + 5 * x**2 - x * y**2
        + x * y**3 - 6 * x**2 * y + x**2 * y**2 - x**3
    )
    record("quotient_identity", S(F(w**2, s * w)) - H)
    record("affine_smoothness_groebner", T.ideal(F, F.derivative(x), F.derivative(y)).groebner_basis())

    D = H.discriminant(w)
    record("discriminant_degree_leading", (D.degree(), D.leading_coefficient()))

    R7 = PolynomialRing(GF(7), names=("w",))
    w7 = R7.gen()
    f37 = R7(H(s=3))
    record("mod7_s3_gcd_factor", (gcd(f37, f37.derivative()), f37.factor()))
    f27 = R7(H(s=2))
    record("mod7_s2_gcd_factor", (gcd(f27, f27.derivative()), f27.factor()))

    R19 = PolynomialRing(GF(19), names=("w",))
    f319 = R19(H(s=3))
    record("mod19_s3_gcd_factor", (gcd(f319, f319.derivative()), f319.factor()))

    U = PolynomialRing(QQ, names=("t", "a1", "a2", "a3", "a4", "a5", "a6"))
    t, a1, a2, a3, a4, a5, a6 = U.gens()
    HU = U(str(H))
    ws = QQ(1) / 3 + a1 * t + a2 * t**2 + a3 * t**3 + a4 * t**4 + a5 * t**5 + a6 * t**6
    series = HU(w=ws, s=2 + t)
    coeffs = [series.monomial_coefficient(t**n) for n in range(1, 7)]
    sol = {}
    solved = []
    for n, a in enumerate([a1, a2, a3, a4, a5, a6], start=1):
        eq = U(coeffs[n - 1].subs(sol))
        c0 = eq.subs({a: 0})
        c1 = eq.subs({a: 1}) - c0
        val = -QQ(c0) / QQ(c1)
        sol[a] = val
        solved.append((str(a), str(val), str(eq)))
    record("endpoint_a_coefficients", json.dumps(solved))

    V = PolynomialRing(QQ, names=("t",))
    tv = V.gen()
    wv = QQ(1) / 3
    for j, (_, val, _) in enumerate(solved, start=1):
        wv += QQ(val) * tv**j
    rho_series = (1 / wv).power_series(V, 7).truncate(7)
    record("rho_series_in_t", rho_series)
    record("rho_series_in_delta", rho_series(-tv))

    CC = ComplexField(100)

    def H_symbolic(alpha):
        Rw = PolynomialRing(SR, names=("w",))
        ww = Rw.gen()
        return (
            1 - alpha * ww - 5 * ww**2 + 3 * alpha * ww**3
            + (5 - alpha**2) * ww**4
            + (alpha**3 - 6 * alpha) * ww**5
            + (alpha**2 - 1) * ww**6
        )

    small = {}
    finite_selection_ok = True
    for m in [4, 6, 8, 10]:
        reps = []
        for a in range(1, 2 * m):
            if gcd(a, 2 * m) == 1 and a <= m:
                alpha = 2 * cos(pi * a / m)
                roots = H_symbolic(alpha).change_ring(CC).roots(multiplicities=False)
                reps.append((a, str(alpha), str(min(abs(root) for root in roots))))
        small[m] = reps
    record("small_m_lambda_checks", json.dumps(small, indent=2))

    for m in range(4, 32):
        vals = []
        sm = 2 * cos(pi / m)
        for a in range(1, 2 * m):
            if gcd(a, 2 * m) == 1:
                alpha = 2 * cos(pi * a / m)
                roots = H_symbolic(alpha).change_ring(CC).roots(multiplicities=False)
                vals.append((a, alpha, min(abs(root) for root in roots)))
        best = min(vals, key=lambda row: row[2])
        if abs(abs(best[1].n(80)) - sm.n(80)) > CC("1e-60"):
            finite_selection_ok = False
    record("finite_m_branch_selection_4_to_31", finite_selection_ok)

    Q = PolynomialRing(QQ, names=("s",))
    sq = Q.gen()
    endpoint_radius = QQ(1) / 2
    separation_radius = QQ(101) / 300
    endpoint_left = QQ(199) / 100
    endpoint_right = QQ(2)
    central_left = -endpoint_left
    central_right = endpoint_left
    H_at_separation_radius = Q(
        H(w=separation_radius, s=sq)
    )

    endpoint_ok = (
        no_circle_crossings(endpoint_radius, endpoint_left, endpoint_right)
        and no_circle_crossings(separation_radius, endpoint_left, endpoint_right)
        and polynomial_negative_on(
            H_at_separation_radius, endpoint_left, endpoint_right
        )
    )
    central_ok = no_circle_crossings(
        separation_radius, central_left, central_right
    )
    record("m0_endpoint_threshold", 2 * cos(pi / 32).n(80) > QQ(199) / 100)
    record("endpoint_interval_certificate", endpoint_ok)
    record("central_interval_certificate", central_ok)


if __name__ == "__main__":
    main()
