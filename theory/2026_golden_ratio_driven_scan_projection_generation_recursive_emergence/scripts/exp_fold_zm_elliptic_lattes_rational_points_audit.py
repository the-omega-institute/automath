#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Lattès doubling, y-quadratic extension, and rational point denominator law
on the Fold weight elliptic curve

  E:  Y^2 = X^3 - X + 1/4.

This script is English-only by repository convention.

We verify:
  - Lattès map on x-coordinate induced by [2]:
      Phi(X) = x([2]P) = (X^4 + 2 X^2 - 2 X + 1) / (4 X^3 - 4 X + 1).
  - 2-division polynomial square pullback under Phi:
      D(Phi(X)) = C(X)^2 / D(X)^3, where D(X)=4X^3-4X+1 and
      C(X)=2X^6-10X^4+10X^3-10X^2+2X+1.
  - Critical polynomial of Phi:
      Phi'(X)=0  <=>  2X^6 - 10X^4 + 10X^3 - 10X^2 + 2X + 1 = 0.
  - y-coordinate doubling uses the same critical sextic:
      Y([2]P) = C(X) / (16 Y^3) in Q(E).
  - Arithmetic closure of the critical sextic:
      Disc(C) = -2^8 * 37^5, and Gal(Split(C)/Q) has order 48 (octahedral type S4 x C2).
  - Weight pullback under doubling is linear in y with critical coefficient:
      [2]^*(y) = (C(X) y + B(X)) / (4X^3 - 4X + 1)^2,
    for an explicit B(X) in Q[X].
  - An integral coupling of special rational points on E(Q):
      R=(0,1/2), Q0=(1,-1/2), Q0'=(-1,1/2), P=(2,-5/2) satisfy
      [2]R=(1,1/2)=-Q0, [3]R=(-1,-1/2)=-Q0', [4]R=(2,-5/2)=P.
  - Quadratic minimal polynomial of the physical weight parameter
      y = X^2 + Y - 1/2
    over Q(X), with discriminant 4X^3 - 4X + 1 = 4Y^2.
  - Torsion triviality via gcd of #E(F_p) over several good primes p.
  - For the physical point P = (2, -5/2), the denominator law:
      if x(nP) = u_n / v_n^2 in lowest terms with v_n>0, then
      den(y(nP)) = v_n^4,
    and we reproduce the first six terms.
  - Bad prime 37 stable reduction degree-drop of Phi:
      mod 37, numerator and denominator share (X-5)^2 and the reduced map has degree 2.
  - Bad prime 37 Chebyshev conjugacy and cycle spectrum on P^1(F_37):
      M o overline{Phi} o M^{-1} = (X^2 - 2) and the full cycle decomposition
      consists of one 9-cycle, one 3-cycle, and three fixed points {5,22,∞}.

Outputs:
  - artifacts/export/fold_zm_elliptic_lattes_rational_points_audit.json
  - sections/generated/eq_fold_zm_elliptic_lattes_rational_points_audit.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


Point = Optional[Tuple[sp.Rational, sp.Rational]]  # None denotes the point at infinity O


def _add(P: Point, Q: Point, *, a: sp.Rational) -> Point:
    """Group law on short Weierstrass: Y^2 = X^3 + aX + b (b unused for formulas)."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q

    if x1 == x2 and y1 == -y2:
        return None

    if x1 == x2 and y1 == y2:
        # doubling
        m = sp.simplify((3 * x1 * x1 + a) / (2 * y1))
    else:
        m = sp.simplify((y2 - y1) / (x2 - x1))

    x3 = sp.together(m * m - x1 - x2)
    y3 = sp.together(m * (x1 - x3) - y1)
    # With rational inputs, SymPy keeps exact rationals (avoid nsimplify here).
    return (sp.simplify(x3), sp.simplify(y3))


def _mul(n: int, P: Point, *, a: sp.Rational) -> Point:
    if n < 0:
        if P is None:
            return None
        x, y = P
        return _mul(-n, (x, -y), a=a)
    if n == 0:
        return None
    if n == 1:
        return P
    # double-and-add
    Q: Point = None
    R: Point = P
    k = n
    while k > 0:
        if k & 1:
            Q = _add(Q, R, a=a)
        R = _add(R, R, a=a)
        k >>= 1
    return Q


def _fraction_to_uv2(x: sp.Rational) -> Tuple[int, int, int, bool]:
    """Return (u, v, den, is_square_den) for x = u / den, and try den = v^2."""
    num, den = sp.fraction(sp.together(x))
    num_i = int(num)
    den_i = int(den)
    v, exact = sp.integer_nthroot(den_i, 2)
    return num_i, int(v), den_i, bool(exact)


def _denominator(q: sp.Rational) -> int:
    return int(sp.denom(sp.together(q)))


def _count_points_mod_p(p: int) -> int:
    """
    Count #E(F_p) for the model y^2 = 4x^3 - 4x + 1.

    For odd p, this is F_p-isomorphic to Y^2 = X^3 - X + 1/4 (map y=2Y).
    """
    if p == 2:
        raise ValueError("Use odd primes only.")
    cnt = 1  # point at infinity
    for x in range(p):
        rhs = (4 * x * x * x - 4 * x + 1) % p
        # count solutions y^2 = rhs
        if rhs == 0:
            cnt += 1
        else:
            # Legendre symbol via Euler criterion
            ls = pow(rhs, (p - 1) // 2, p)
            if ls == 1:
                cnt += 2
            # ls == p-1 => nonresidue, add 0
    return int(cnt)


@dataclass(frozen=True)
class TableRow:
    n: int
    x: str
    u_n: int
    v_n: int
    x_den: int
    x_den_is_square: bool
    y_weight: str
    den_y: int
    v_n_pow4: int
    den_law_ok: bool


@dataclass(frozen=True)
class Payload:
    phi_formula_ok: bool
    phi_2division_pullback_square_ok: bool
    phi_mod37_degree_drop_ok: bool
    phi_mod37_gcd: str
    phi_mod37_reduced_map: str
    g_mod37_factor_ok: bool
    phi_prime_critical_poly_ok: bool
    phi_critval_resultant_ok: bool
    phi_fiber_square_splitting_ok: bool
    critical_sextic_quadratic_factor_ok: bool
    norm_3a2_minus1_ok: bool
    norm_3a2_minus1: str
    phi_Y_doubling_ok: bool
    critical_poly_disc: int
    critical_poly_disc_factorization: Dict[str, int]
    critical_poly_galois_degree: int
    critical_poly_galois_order: int
    critical_poly_galois_is_transitive: bool
    critical_poly_galois_center_order: int
    critical_poly_galois_derived_order: int
    critical_poly_galois_derived_order_hist: Dict[str, int]
    y_doubling_pullback_linear_ok: bool
    y_doubling_pullback_cubic_fraction_ok: bool
    y_minpoly_ok: bool
    y_discriminant_ok: bool
    torsion_primes: List[int]
    torsion_group_orders: List[int]
    torsion_gcd: int
    torsion_trivial: bool
    base_point: Dict[str, str]
    mw_anchor_points: Dict[str, str]
    mw_anchor_relations_ok: bool
    table_first6: List[TableRow]
    phi_mod37_chebyshev_conjugacy_ok: bool
    phi_mod37_cycle_spectrum_ok: bool
    phi_mod37_cycles_p1: List[List[int]]


def main() -> None:
    t0 = time.time()
    print("[fold-zm-elliptic-lattes] start", flush=True)

    X = sp.Symbol("X")
    Y = sp.Symbol("Y")

    # Curve: Y^2 = X^3 - X + 1/4.
    a = sp.Integer(-1)
    b = sp.Rational(1, 4)

    # --- Lattès doubling map on x ---
    Phi = sp.simplify(((3 * X**2 + a) / (2 * Y)) ** 2 - 2 * X)
    Phi = sp.simplify(Phi.subs({Y**2: X**3 + a * X + b}))
    Phi = sp.together(Phi)
    N, D = Phi.as_numer_denom()
    N = sp.factor(N)
    D = sp.factor(D)

    Phi_expected = sp.together((X**4 + 2 * X**2 - 2 * X + 1) / (4 * X**3 - 4 * X + 1))
    phi_ok = bool(sp.factor(Phi - Phi_expected) == 0)

    # --- Bad prime 37: stable reduction degree-drop of Phi ---
    p_bad = 37
    num_phi = X**4 + 2 * X**2 - 2 * X + 1
    den_phi = 4 * X**3 - 4 * X + 1
    num_phi_mod_expected = (X - 5) ** 2 * (X**2 + 10 * X + 3)
    den_phi_mod_expected = (X - 5) ** 2 * (4 * X + 3)
    num_mod_ok = bool(sp.Poly(num_phi - num_phi_mod_expected, X, modulus=p_bad).is_zero)
    den_mod_ok = bool(sp.Poly(den_phi - den_phi_mod_expected, X, modulus=p_bad).is_zero)
    num_poly_mod = sp.Poly(num_phi, X, modulus=p_bad)
    den_poly_mod = sp.Poly(den_phi, X, modulus=p_bad)
    gcd_mod = sp.gcd(num_poly_mod, den_poly_mod)
    gcd_mod = sp.Poly(gcd_mod, X, modulus=p_bad).monic()
    num_red = num_poly_mod.quo(gcd_mod)
    den_red = den_poly_mod.quo(gcd_mod)
    num_red_expected = sp.Poly(X**2 + 10 * X + 3, X, modulus=p_bad)
    den_red_expected = sp.Poly(4 * X + 3, X, modulus=p_bad)
    phi_mod37_degree_drop_ok = bool(num_mod_ok and den_mod_ok and num_red == num_red_expected and den_red == den_red_expected)
    phi_mod37_gcd = gcd_mod.as_expr()
    phi_mod37_reduced_map = sp.together(num_red.as_expr() / den_red.as_expr())

    # --- Bad prime 37: Chebyshev conjugacy and cycle spectrum on P^1(F_37) ---
    def _inv_mod(a: int, p: int) -> int:
        a %= p
        if a == 0:
            raise ZeroDivisionError("inverse of 0")
        return pow(a, p - 2, p)

    def _overphi_p1(x: int | None, p: int) -> int | None:
        # overline{Phi}(x) = (x^2+10x+3)/(4x+3), with infinity represented by None
        if x is None:
            return None
        num = (x * x + 10 * x + 3) % p
        den = (4 * x + 3) % p
        if den == 0:
            return None
        return (num * _inv_mod(den, p)) % p

    def _mobius_M(x: int | None, p: int) -> int | None:
        # M(x) = (2x+13)/(x-5)
        if x is None:
            return 2 % p
        den = (x - 5) % p
        if den == 0:
            return None
        num = (2 * x + 13) % p
        return (num * _inv_mod(den, p)) % p

    def _mobius_Minv(x: int | None, p: int) -> int | None:
        # M^{-1}(x) = (5x+13)/(x-2)
        if x is None:
            return 5 % p
        den = (x - 2) % p
        if den == 0:
            return None
        num = (5 * x + 13) % p
        return (num * _inv_mod(den, p)) % p

    def _T2(x: int | None, p: int) -> int | None:
        if x is None:
            return None
        return (x * x - 2) % p

    pts_p1 = [None] + list(range(p_bad))
    phi_mod37_chebyshev_conjugacy_ok = True
    for x in pts_p1:
        lhs = _mobius_M(_overphi_p1(_mobius_Minv(x, p_bad), p_bad), p_bad)
        rhs = _T2(x, p_bad)
        if lhs != rhs:
            phi_mod37_chebyshev_conjugacy_ok = False
            break

    # Cycle decomposition (record each cycle once; ignore preperiodic tails).
    seen: set[int | None] = set()
    cycles: List[List[int | None]] = []
    for x in pts_p1:
        if x in seen:
            continue
        seq: List[int | None] = []
        cur = x
        while cur not in seen and cur not in seq:
            seq.append(cur)
            cur = _overphi_p1(cur, p_bad)
        if cur in seen:
            for u in seq:
                seen.add(u)
            continue
        # New cycle: cur repeats inside seq.
        i0 = seq.index(cur)
        cycles.append(seq[i0:])
        for u in seq:
            seen.add(u)

    # Normalize cycles for stable JSON comparisons: rotate to the minimal element (∞ last), sort by length.
    def _key(u: int | None) -> Tuple[int, int]:
        return (1, 0) if u is None else (0, int(u))

    def _rot_min(cyc: List[int | None]) -> List[int | None]:
        ks = [_key(u) for u in cyc]
        j = min(range(len(cyc)), key=lambda i: ks[i])
        return cyc[j:] + cyc[:j]

    cycles_norm = [_rot_min(c) for c in cycles]
    cycles_norm.sort(key=lambda c: (len(c), [_key(u) for u in c]))
    cycles_json: List[List[int]] = [[-1 if u is None else int(u) for u in c] for c in cycles_norm]
    phi_mod37_cycle_spectrum_ok = bool(
        cycles_json
        == [
            [5],
            [22],
            [-1],
            [3, 25, 29],
            [1, 2, 26, 15, 6, 16, 30, 17, 31],
        ]
    )

    # --- Bad prime 37: cubic g(X)=16X^3-9X^2+1 double-root collapse ---
    g_cubic = 16 * X**3 - 9 * X**2 + 1
    g_cubic_mod_expected = 16 * (X - 16) * (X - 5) ** 2
    g_mod37_factor_ok = bool(sp.Poly(g_cubic - g_cubic_mod_expected, X, modulus=p_bad).is_zero)

    # --- Critical polynomial for Phi'(X)=0 (affine chart) ---
    Phi_prime = sp.diff(Phi_expected, X)
    nump, denp = sp.together(Phi_prime).as_numer_denom()
    nump = sp.factor(nump)
    crit_expected = 2 * X**6 - 10 * X**4 + 10 * X**3 - 10 * X**2 + 2 * X + 1
    # Normalize by removing content (overall integer factor).
    poly_nump = sp.Poly(nump, X, domain="ZZ")
    _, prim_nump = poly_nump.primitive()
    nump_prim = sp.factor(prim_nump.as_expr())
    crit_ok = bool(sp.factor(nump_prim - crit_expected) == 0 or sp.factor(nump_prim + crit_expected) == 0)

    # --- Critical value elimination via resultant (PCF portrait certificate) ---
    T = sp.Symbol("T")
    res_critval = sp.factor(sp.resultant(crit_expected, N - T * D, X))
    res_critval_expected = (37**3) * (4 * T**3 - 4 * T + 1) ** 2
    phi_critval_resultant_ok = bool(sp.factor(res_critval - res_critval_expected) == 0)

    # --- Fiber square splitting over the 2-division cubic ---
    A = sp.Symbol("A")
    qA = X**2 - 2 * A * X - 2 * A**2 + 1
    fiber_diff = sp.expand((X**4 + 2 * X**2 - 2 * X + 1) - A * (4 * X**3 - 4 * X + 1) - qA**2)
    D_A = 4 * A**3 - 4 * A + 1
    # Equivalent form: fiber_diff = -(A+2X) * D_A, hence vanishes on D_A=0.
    phi_fiber_square_splitting_ok = bool(sp.factor(fiber_diff + (A + 2 * X) * D_A) == 0)

    # --- Critical sextic quadratic factorization and a norm identity in Q(A) ---
    fA = A**3 - A + sp.Rational(1, 4)
    res_quad = sp.factor(sp.resultant(fA, qA, A))
    critical_sextic_quadratic_factor_ok = bool(sp.factor(2 * res_quad - crit_expected) == 0)
    norm_3a2_minus1 = sp.resultant(fA, 3 * A**2 - 1, A)
    norm_3a2_minus1_ok = bool(sp.factor(norm_3a2_minus1 + sp.Rational(37, 16)) == 0)

    # --- 2-division polynomial square pullback under Phi ---
    D_poly = 4 * X**3 - 4 * X + 1
    D_at_Phi = sp.together(4 * Phi_expected**3 - 4 * Phi_expected + 1)
    D_pullback_expected = sp.together(crit_expected**2 / D_poly**3)
    phi_2division_pullback_square_ok = bool(sp.factor(sp.together(D_at_Phi - D_pullback_expected)) == 0)

    # --- Discriminant and Galois group of the critical sextic ---
    crit_disc = int(sp.discriminant(crit_expected, X))
    crit_disc_fac = sp.factorint(crit_disc)
    G, _meta = sp.Poly(crit_expected, X, domain=sp.QQ).galois_group()
    G_order = int(G.order())
    G_degree = int(G.degree)
    G_trans = bool(G.is_transitive())
    Z = G.center()
    Dsub = G.derived_subgroup()
    # Derived subgroup histogram (should match A4: 1, three 2s, eight 3s).
    from collections import Counter

    hist = Counter()
    for g in list(Dsub.generate_schreier_sims()):
        hist[g.order()] += 1
    hist_json = {str(int(k)): int(v) for k, v in sorted(hist.items())}

    # --- y quadratic minimal polynomial over Q(X) ---
    y = sp.Symbol("y")
    y_def = X**2 + Y - sp.Rational(1, 2)
    # Eliminate Y using Y = y - X^2 + 1/2.
    elim = sp.expand((y - X**2 + sp.Rational(1, 2)) ** 2 - (X**3 + a * X + b))
    minpoly = sp.factor(elim)
    minpoly_expected = y**2 - (2 * X**2 - 1) * y + X * (X - 1) ** 2 * (X + 1)
    y_minpoly_ok = bool(sp.factor(minpoly - minpoly_expected) == 0)

    disc = sp.factor(sp.discriminant(minpoly_expected, y))
    disc_expected = 4 * X**3 - 4 * X + 1
    y_disc_ok = bool(sp.factor(disc - disc_expected) == 0)

    # --- [2]^*(y) is linear in y with critical coefficient ---
    # Work in Q(X,Y) first, reduce modulo Y^2-(X^3+aX+b), then eliminate Y using Y=y-X^2+1/2
    # and reduce modulo the quartic certificate F(X,y)=0.
    a = sp.Integer(-1)
    b = sp.Rational(1, 4)
    fX = X**3 + a * X + b

    m = sp.together((3 * X**2 + a) / (2 * Y))
    X2 = sp.together(m * m - 2 * X)
    Y2 = sp.together(m * (X - X2) - Y)
    y2 = sp.together(X2**2 + Y2 - sp.Rational(1, 2))
    num_y2, den_y2 = y2.as_numer_denom()

    modY = sp.Poly(Y**2 - fX, Y)
    num_y2_red = sp.rem(sp.Poly(sp.expand(num_y2), Y), modY).as_expr()
    den_y2_red = sp.rem(sp.Poly(sp.expand(den_y2), Y), modY).as_expr()

    # --- Y-coordinate of [2]P uses the same critical sextic ---
    target_Y2 = sp.together(crit_expected / (16 * Y**3))
    diff_Y2 = sp.together(Y2 - target_Y2)
    num_diff_Y2, _den_diff_Y2 = diff_Y2.as_numer_denom()
    num_diff_Y2_red = sp.rem(sp.Poly(sp.expand(num_diff_Y2), Y), modY).as_expr()
    phi_Y_doubling_ok = bool(sp.simplify(num_diff_Y2_red) == 0)

    Y_sub = y - X**2 + sp.Rational(1, 2)
    expr_xy = sp.together(num_y2_red.subs({Y: Y_sub}) / den_y2_red.subs({Y: Y_sub}))
    num_xy, den_xy = expr_xy.as_numer_denom()

    F = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)
    Pnum = sp.Poly(sp.expand(num_xy), y, domain=sp.QQ[X])
    Pmod = sp.Poly(sp.expand(F), y, domain=sp.QQ[X])
    rem = sp.rem(Pnum, Pmod).as_expr()

    Bpoly = -X**8 + 7 * X**6 - 14 * X**5 + 27 * X**4 - 9 * X**3 - 6 * X**2 + X + 1
    D2 = (4 * X**3 - 4 * X + 1) ** 2
    rhs = sp.together((crit_expected * y + Bpoly) / D2)
    diff = sp.together(expr_xy - rhs)
    nd, _dd = diff.as_numer_denom()
    Pnd = sp.Poly(sp.expand(nd), y, domain=sp.QQ[X])
    nd_rem = sp.rem(Pnd, Pmod).as_expr()
    y_pullback_ok = bool(sp.simplify(nd_rem) == 0)

    # --- Cubic/cubic representation in Q(y)(X)/(F): verify the manuscript form ---
    N_cubic = (
        (-2 * y**2 - 10 * y + 1) * X**3
        + (2 * y**3 - 6 * y**2 + 34 * y + 27) * X**2
        + (2 * y**3 + 10 * y**2 + 12 * y - 23) * X
        - (y**4 + 23 * y**2 + 23 * y - 1)
    )
    D_cubic = (
        (64 * y + 8) * X**3
        + (48 * y**2 + 16 * y) * X**2
        - (16 * y**2 + 48 * y + 8) * X
        - (32 * y**3 + 32 * y**2 - 1)
    )
    diff_cubic = sp.together(expr_xy - sp.together(N_cubic / D_cubic))
    nd2, _dd2 = diff_cubic.as_numer_denom()
    Pnd2 = sp.Poly(sp.expand(nd2), y, domain=sp.QQ[X])
    nd2_rem = sp.rem(Pnd2, Pmod).as_expr()
    y_pullback_cubic_ok = bool(sp.simplify(nd2_rem) == 0)

    # --- Torsion audit via reduction mod p ---
    primes = [3, 5, 7, 11, 13, 17, 19]
    good_primes = [p for p in primes if p not in (2, 37)]
    orders = [_count_points_mod_p(p) for p in good_primes]
    g = 0
    for n in orders:
        g = math.gcd(g, n)
    torsion_trivial = bool(g == 1)

    # --- Rational point orbit and denominator law ---
    P: Point = (sp.Integer(2), -sp.Rational(5, 2))
    # sanity check P on curve
    if sp.simplify(P[1] ** 2 - (P[0] ** 3 + a * P[0] + b)) != 0:
        raise RuntimeError("Base point P is not on the curve.")

    # --- Mordell–Weil anchoring: special points and integral relations ---
    R: Point = (sp.Integer(0), sp.Rational(1, 2))
    Q0: Point = (sp.Integer(1), -sp.Rational(1, 2))
    Q0p: Point = (-sp.Integer(1), sp.Rational(1, 2))
    twoR = _mul(2, R, a=a)
    threeR = _mul(3, R, a=a)
    fourR = _mul(4, R, a=a)
    mw_ok = bool(
        twoR == (sp.Integer(1), sp.Rational(1, 2))
        and twoR == (Q0[0], -Q0[1])
        and threeR == (-sp.Integer(1), -sp.Rational(1, 2))
        and threeR == (Q0p[0], -Q0p[1])
        and fourR == (sp.Integer(2), -sp.Rational(5, 2))
        and fourR == P
    )

    def y_weight(pt: Point) -> sp.Rational:
        if pt is None:
            raise ValueError("y(weight) undefined at O.")
        xpt, ypt = pt
        return sp.together(xpt**2 + ypt - sp.Rational(1, 2))

    rows: List[TableRow] = []
    for n in range(1, 7):
        pt = _mul(n, P, a=a)
        if pt is None:
            raise RuntimeError("Unexpected: nP hit O for small n (would contradict torsion triviality).")
        xpt, ypt = pt
        u_n, v_n, x_den, den_is_square = _fraction_to_uv2(sp.together(xpt))
        yw = sp.together(y_weight(pt))
        den_y = _denominator(yw)
        v4 = int(v_n) ** 4
        ok = bool(den_is_square and den_y == v4)
        rows.append(
            TableRow(
                n=n,
                x=sp.sstr(sp.Rational(xpt)),
                u_n=int(u_n),
                v_n=int(v_n),
                x_den=int(x_den),
                x_den_is_square=bool(den_is_square),
                y_weight=sp.sstr(yw),
                den_y=int(den_y),
                v_n_pow4=int(v4),
                den_law_ok=bool(ok),
            )
        )

    payload = Payload(
        phi_formula_ok=bool(phi_ok),
        phi_2division_pullback_square_ok=bool(phi_2division_pullback_square_ok),
        phi_mod37_degree_drop_ok=bool(phi_mod37_degree_drop_ok),
        phi_mod37_gcd=sp.sstr(phi_mod37_gcd),
        phi_mod37_reduced_map=sp.sstr(phi_mod37_reduced_map),
        g_mod37_factor_ok=bool(g_mod37_factor_ok),
        phi_prime_critical_poly_ok=bool(crit_ok),
        phi_critval_resultant_ok=bool(phi_critval_resultant_ok),
        phi_fiber_square_splitting_ok=bool(phi_fiber_square_splitting_ok),
        critical_sextic_quadratic_factor_ok=bool(critical_sextic_quadratic_factor_ok),
        norm_3a2_minus1_ok=bool(norm_3a2_minus1_ok),
        norm_3a2_minus1=sp.sstr(norm_3a2_minus1),
        phi_Y_doubling_ok=bool(phi_Y_doubling_ok),
        critical_poly_disc=int(crit_disc),
        critical_poly_disc_factorization={str(int(p)): int(e) for p, e in crit_disc_fac.items()},
        critical_poly_galois_degree=G_degree,
        critical_poly_galois_order=G_order,
        critical_poly_galois_is_transitive=G_trans,
        critical_poly_galois_center_order=int(Z.order()),
        critical_poly_galois_derived_order=int(Dsub.order()),
        critical_poly_galois_derived_order_hist=hist_json,
        y_doubling_pullback_linear_ok=bool(y_pullback_ok),
        y_doubling_pullback_cubic_fraction_ok=bool(y_pullback_cubic_ok),
        y_minpoly_ok=bool(y_minpoly_ok),
        y_discriminant_ok=bool(y_disc_ok),
        torsion_primes=[int(p) for p in good_primes],
        torsion_group_orders=[int(n) for n in orders],
        torsion_gcd=int(g),
        torsion_trivial=bool(torsion_trivial),
        base_point={"P": "(2,-5/2)", "minus_P": "(2,5/2)", "y(P)": sp.sstr(y_weight(P))},
        mw_anchor_points={
            "R": "(0,1/2)",
            "Q0": "(1,-1/2)",
            "Q0_prime": "(-1,1/2)",
            "P": "(2,-5/2)",
            "2R": sp.sstr(twoR),
            "3R": sp.sstr(threeR),
            "4R": sp.sstr(fourR),
        },
        mw_anchor_relations_ok=bool(mw_ok),
        table_first6=rows,
        phi_mod37_chebyshev_conjugacy_ok=bool(phi_mod37_chebyshev_conjugacy_ok),
        phi_mod37_cycle_spectrum_ok=bool(phi_mod37_cycle_spectrum_ok),
        phi_mod37_cycles_p1=cycles_json,
    )

    out_json = export_dir() / "fold_zm_elliptic_lattes_rational_points_audit.json"
    _write_json(out_json, asdict(payload))

    # TeX snippet (keep it short; full table is in JSON).
    tex_lines: List[str] = [
        "% Auto-generated by scripts/exp_fold_zm_elliptic_lattes_rational_points_audit.py",
        "\\[",
        "\\Phi(X)=\\frac{X^{4}+2X^{2}-2X+1}{4X^{3}-4X+1},\\qquad \\Phi'(X)=0\\iff 2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1=0.",
        "\\]",
        "\\[",
        "D(\\Phi(X))=\\frac{(2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1)^{2}}{(4X^{3}-4X+1)^{3}},\\qquad Y([2]P)=\\frac{2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1}{16Y^{3}}.",
        "\\]",
        "\\[",
        "\\mathrm{Res}_{X}\\bigl(2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1,\\ (X^{4}+2X^{2}-2X+1)-T(4X^{3}-4X+1)\\bigr)=37^{3}(4T^{3}-4T+1)^{2}.",
        "\\]",
        "\\[",
        "\\operatorname{N}_{\\mathbb{Q}(\\alpha)/\\mathbb{Q}}(3\\alpha^{2}-1)=-\\frac{37}{16}\\ \\text{for }4\\alpha^{3}-4\\alpha+1=0.",
        "\\]",
        "\\[",
        "X^{4}+2X^{2}-2X+1\\equiv (X-5)^{2}(X^{2}+10X+3),\\quad 4X^{3}-4X+1\\equiv (X-5)^{2}(4X+3)\\ (\\mathrm{mod}\\ 37),\\quad \\overline{\\Phi}(X)=\\frac{X^{2}+10X+3}{4X+3}.",
        "\\]",
        "\\[",
        "[2]^*(y)=\\frac{(2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1)\\,y+(-X^{8}+7X^{6}-14X^{5}+27X^{4}-9X^{3}-6X^{2}+X+1)}{(4X^{3}-4X+1)^{2}}.",
        "\\]",
        "\\[",
        "\\mathrm{Disc}(2X^{6}-10X^{4}+10X^{3}-10X^{2}+2X+1)=-2^{8}\\cdot 37^{5},\\qquad |\\mathrm{Gal}|=48.",
        "\\]",
        "\\[",
        "y:=X^{2}+Y-\\frac12,\\qquad y^{2}-(2X^{2}-1)y+X(X-1)^{2}(X+1)=0,\\qquad \\Delta=4X^{3}-4X+1=4Y^{2}.",
        "\\]",
        "\\[",
        "E(\\mathbb{Q})_{\\mathrm{tors}}=\\{O\\}\\ \\text{(gcd of }\\#E(\\mathbb{F}_p)\\text{ over small good primes equals }1).",
        "\\]",
        "\\[",
        "R:=(0,\\tfrac12),\\ Q_0:=(1,-\\tfrac12),\\ Q_0':=(-1,\\tfrac12),\\ P:=(2,-\\tfrac52),\\ "
        "[2]R=(1,\\tfrac12)=-Q_0,\\ [3]R=(-1,-\\tfrac12)=-Q_0',\\ [4]R=(2,-\\tfrac52)=P.",
        "\\]",
        "",
    ]
    out_tex = generated_dir() / "eq_fold_zm_elliptic_lattes_rational_points_audit.tex"
    _write_text(out_tex, "\n".join(tex_lines))

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-lattes] checks:"
        f" phi={phi_ok} Dpull={phi_2division_pullback_square_ok} Ydbl={phi_Y_doubling_ok}"
        f" mod37degdrop={phi_mod37_degree_drop_ok} gmod37={g_mod37_factor_ok}"
        f" crit={crit_ok} res={phi_critval_resultant_ok} fibsq={phi_fiber_square_splitting_ok}"
        f" quadfac={critical_sextic_quadratic_factor_ok} norm={norm_3a2_minus1_ok}"
        f" galois48={(G_order == 48)} y2lin={y_pullback_ok} y2cubic={y_pullback_cubic_ok}"
        f" mw={mw_ok} minpoly={y_minpoly_ok} disc={y_disc_ok} tors_gcd={g} denlaw={all(r.den_law_ok for r in rows)}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print(f"[fold-zm-elliptic-lattes] wrote {out_json}", flush=True)
    print(f"[fold-zm-elliptic-lattes] wrote {out_tex}", flush=True)
    print("[fold-zm-elliptic-lattes] done", flush=True)


if __name__ == "__main__":
    main()

