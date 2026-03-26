#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the ramification geometry of the y-projection on the elliptic normalization
of the Fold fiber-weight spectral curve Pi(lambda,y)=0.

This script is English-only by repository convention.

We verify (symbolically, with SymPy):
  - On E: Y^2 = X^3 - X + 1/4, for y = X^2 + Y - 1/2 and omega = dX/(2Y),
      dy = (4 X Y + 3 X^2 - 1) * omega.
  - Abel–Jacobi algebraic ODE: with du=omega and p=dy/du, eliminating X yields
      p^4 + (8y-3)p^3 + (2y^2-34y-4)p^2 - y(y-1)P_LY(y) = 0.
  - Self-reflexive discriminant factorization of the above quartic:
      Disc_p(F(p;y)) = -y(y-1)P_LY(y) * Q5(y)^2,
    and Disc(Q5) = -2^28*3^9*11^2*31^3*727.
  - Finite ramification points satisfy 4XY + 3X^2 - 1 = 0; eliminating Y yields
      (X-1)(X+1)(16X^3 - 9X^2 + 1) = 0.
  - The nontrivial ramification images satisfy the Lee–Yang cubic
      P_LY(y) = 256 y^3 + 411 y^2 + 165 y + 32
    via a pure elimination certificate (resultant), with the exact constant:
      Res_X(16X^3-9X^2+1, 4Xy-(4X^3-3X^2-2X+1)) = -64 * P_LY(y).
  - Norm / different bridge: for F(X,y)=X^4-X^3-(2y+1)X^2+X+y(y+1) and
      delta = 4Xy - (4X^3 - 3X^2 - 2X + 1) = -dF/dX,
    we have Res_X(F, delta) = -y(y-1)P_LY(y).
  - 2-division norm square compression:
      Res_X(F, 4X^3-4X+1) = (16y^3 - 8y^2 - 4y + 1)^2,
      Res_X(F, 2y-2X^2+1) = -(16y^3 - 8y^2 - 4y + 1).
  - Cubic-field generator mapping: if alpha solves 16X^3-9X^2+1=0, then
      beta=(4alpha^3-3alpha^2-2alpha+1)/(4alpha) solves P_LY(beta)=0,
    and Disc(16X^3-9X^2+1)=-2^2*3^3*37.
  - Puiseux expansions at y=0,1 (checked to O(t^4)), and the general formula
      c0^2 = -2 F_y / F_xx = (2/3)*(3alpha^2-1)/(alpha^2-1)
    at the Lee–Yang branch points.
  - Puiseux expansion at y=infty in the t-uniformizer with y=t^(-4), matching the
    manuscript coefficients up to O(t^4).
  - The next Puiseux jet coefficient on the Lee–Yang branch points:
      beta = -F_xy/F_xx + (F_xxx*F_y)/(3 F_xx^2),
    reduced to a closed rational function of the critical eigenvalue.
  - The next (t^3) Puiseux jet coefficient on the Lee–Yang branch points:
      gamma = G(alpha) / c0, i.e. gamma * c0 is a closed rational function of alpha.
  - Riemann–Hurwitz genus numbers for the S4 splitting cover and its A4/V4 quotients.

Outputs:
  - artifacts/export/fold_zm_elliptic_leyang_cover_geometry_audit.json

We also audit the bad prime p=37 semistable degeneration of the discriminant ridge
hyperelliptic curve C_LY: W^2 = -y(y-1)P_LY(y):
  - The special fiber has a nonsplit node at y=6.
  - The normalization is the elliptic curve E_14: Z^2 = 3 y(y-1)(y-14).
  - Point counts satisfy #C(F_{37^n}) = #E_14(F_{37^n}) + (-1)^{n+1} for n=1,2.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_constant_in(expr: sp.Expr, sym: sp.Symbol) -> bool:
    expr = sp.together(sp.simplify(expr))
    num, den = expr.as_numer_denom()
    try:
        deg_num = sp.Poly(num, sym, domain=sp.QQ).degree()
        deg_den = sp.Poly(den, sym, domain=sp.QQ).degree()
    except Exception:
        return False
    return deg_num == 0 and deg_den == 0


def _series_order_at_least(expr: sp.Expr, t: sp.Symbol, order: int) -> bool:
    """Return True iff expr = O(t^order) at t=0."""
    s = sp.series(expr, t, 0, order).removeO()
    return bool(sp.simplify(s) == 0)


def _reduce_mod(poly_expr: sp.Expr, var: sp.Symbol, modulus: sp.Expr) -> sp.Expr:
    """Polynomial remainder of poly_expr modulo modulus in QQ[var]."""
    P = sp.Poly(sp.expand(poly_expr), var, domain=sp.QQ)
    M = sp.Poly(sp.expand(modulus), var, domain=sp.QQ)
    return sp.rem(P, M).as_expr()


@dataclass(frozen=True)
class Payload:
    dy_identity_ok: bool
    abel_jacobi_ode_ok: bool
    abel_jacobi_ode_constant: str
    abel_jacobi_ode_exact_ok: bool
    delta_quartic_y2_irreducible_ok: bool
    delta_quartic_disc_factor_ok: bool
    disc_q5: int
    disc_q5_factorization: Dict[str, int]
    critical_x_factor_ok: bool
    resy_F_Fx_factor_ok: bool
    resy_F_Fx_constant: str
    res_F_cubicx_factor_ok: bool
    res_F_cubicx_constant: str
    leyang_resultant_ok: bool
    leyang_resultant_constant: int
    leyang_resultant_exact_ok: bool
    norm_identity_ok: bool
    norm_2division_ok: bool
    norm_2Y_ok: bool
    disc_ctrl_cubic_y: int
    disc_ctrl_cubic_y_factorization: Dict[str, int]
    disc_conj_cubic_y: int
    disc_conj_cubic_y_factorization: Dict[str, int]
    mod37_ctrl_cubic_y: str
    mod37_leyang_cubic_y: str
    mod37_conj_cubic_y: str
    y_of_minus_P: int
    disc_cubic_x: int
    disc_cubic_x_factorization: Dict[str, int]
    disc_leyang: int
    puiseux_y0_0_ok: bool
    puiseux_y0_1_ok: bool
    puiseux_infty_ok: bool
    puiseux_infty_branches_ok: bool
    c0_sq_formula_ok: bool
    beta_formula_ok: bool
    gamma_formula_ok: bool
    genus_s4_splitting: int
    genus_sign_quadratic: int
    genus_v4_quotient: int
    badprime_37_C_Fp: int
    badprime_37_E14_Fp: int
    badprime_37_C_minus_E14_Fp: int
    badprime_37_C_Fp2: int
    badprime_37_E14_Fp2: int
    badprime_37_C_minus_E14_Fp2: int
    badprime_37_E14_trace_a: int
    badprime_37_nonsplit_node_ok: bool


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit ramification geometry for the elliptic y-cover (Fold Z_m).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-leyang-cover-geom] start", flush=True)

    X, Y, y, p, t = sp.symbols("X Y y p t")

    # Elliptic curve E and weight function y(X,Y)
    E = Y**2 - (X**3 - X + sp.Rational(1, 4))
    y_map = X**2 + Y - sp.Rational(1, 2)

    # Differential identity: dy = (4XY + 3X^2 - 1) * (dX/(2Y))
    dy_dx = sp.simplify(2 * X + (3 * X**2 - 1) / (2 * Y))
    dy_identity_ok = bool(sp.simplify(dy_dx - (4 * X * Y + 3 * X**2 - 1) / (2 * Y)) == 0)

    # Critical locus in affine chart: 4XY + 3X^2 - 1 = 0
    crit = 4 * X * Y + 3 * X**2 - 1
    res_X = sp.factor(sp.resultant(E, crit, Y))
    target_X = (X - 1) * (X + 1) * (16 * X**3 - 9 * X**2 + 1)
    q = sp.together(res_X / target_X)
    critical_x_factor_ok = _is_constant_in(q, X)

    # Lee–Yang cubic from elimination: Res_X(16X^3-9X^2+1, 4Xy-(4X^3-3X^2-2X+1)) ∝ P_LY(y)
    cubicX = 16 * X**3 - 9 * X**2 + 1
    rel = 4 * X * y - (4 * X**3 - 3 * X**2 - 2 * X + 1)
    res_y = sp.factor(sp.resultant(cubicX, rel, X))
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    q2 = sp.together(res_y / P_LY)
    leyang_resultant_ok = _is_constant_in(q2, y)
    leyang_resultant_constant = int(sp.factor(q2))
    leyang_resultant_exact_ok = bool(sp.factor(res_y - leyang_resultant_constant * P_LY) == 0)

    # Norm identity via resultant of F and delta=-dF/dX
    F = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)
    delta = 4 * X * y - (4 * X**3 - 3 * X**2 - 2 * X + 1)
    if sp.simplify(delta + sp.diff(F, X)) != 0:
        raise RuntimeError("Expected delta = -dF/dX identity failed (internal).")
    Res_norm = sp.factor(sp.resultant(F, delta, X))
    norm_expected = -y * (y - 1) * P_LY
    norm_identity_ok = bool(sp.factor(Res_norm - norm_expected) == 0)

    # 2-division norm square compression.
    D2 = 4 * X**3 - 4 * X + 1
    Res_D2 = sp.factor(sp.resultant(F, D2, X))
    ctrl = 16 * y**3 - 8 * y**2 - 4 * y + 1
    norm_2division_ok = bool(sp.factor(Res_D2 - ctrl**2) == 0)

    twoY = 2 * y - 2 * X**2 + 1  # since Y = y - X^2 + 1/2
    Res_twoY = sp.factor(sp.resultant(F, twoY, X))
    norm_2Y_ok = bool(sp.factor(Res_twoY + ctrl) == 0)

    # Abel–Jacobi ODE closure in (y,p): with du = dX/(2Y) and p = dy/du.
    # Since dy = (4XY+3X^2-1) * (dX/(2Y)), we have p = 4XY + 3X^2 - 1.
    # Eliminating Y via Y = y - X^2 + 1/2 yields a cubic constraint in X:
    #   4X^3 - 3X^2 - (4y+2)X + (1+p) = 0.
    cubic_p = 4 * X**3 - 3 * X**2 - (4 * y + 2) * X + (1 + p)
    Res_ode = sp.factor(sp.resultant(F, cubic_p, X))
    ode_expected = (
        p**4
        + (8 * y - 3) * p**3
        + (2 * y**2 - 34 * y - 4) * p**2
        - y * (y - 1) * P_LY
    )
    q_ode = sp.together(Res_ode / ode_expected)
    abel_jacobi_ode_ok = _is_constant_in(q_ode, y) and _is_constant_in(q_ode, p)
    abel_jacobi_ode_constant = str(sp.factor(q_ode)) if abel_jacobi_ode_ok else "nan"
    abel_jacobi_ode_exact_ok = (
        bool(sp.factor(Res_ode - sp.factor(q_ode) * ode_expected) == 0) if abel_jacobi_ode_ok else False
    )

    # Irreducibility certificate (specialization): y=2 gives a quartic irreducible over QQ.
    ode_y2 = sp.Poly(ode_expected.subs(y, sp.Integer(2)), p, domain=sp.QQ).as_expr()
    _, ode_y2_factors = sp.factor_list(ode_y2, p)
    delta_quartic_y2_irreducible_ok = bool(len(ode_y2_factors) == 1 and ode_y2_factors[0][1] == 1)

    # Discriminant factorization of the (y,p)-quartic.
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80
    disc_p = sp.factor(sp.discriminant(ode_expected, p))
    disc_expected = -y * (y - 1) * P_LY * Q5**2
    delta_quartic_disc_factor_ok = bool(sp.factor(disc_p - disc_expected) == 0)

    disc_q5 = int(sp.discriminant(Q5, y))
    disc_q5_fac = sp.factorint(disc_q5)

    # Discriminants
    disc_cubic_x = int(sp.discriminant(cubicX, X))
    disc_cubic_x_fac = sp.factorint(disc_cubic_x)
    disc_leyang = int(sp.discriminant(P_LY, y))

    # --- Additional eliminations used in the manuscript text ---
    # 1) Ramification in the (X,y)-plane quartic model: Res_y(F, dF/dX).
    Fx = sp.diff(F, X)
    resy_F_Fx = sp.factor(sp.resultant(F, Fx, y))
    target_resy = -(X - 1) * (X + 1) * cubicX
    q_resy = sp.together(resy_F_Fx / target_resy)
    resy_F_Fx_factor_ok = _is_constant_in(q_resy, X)
    resy_F_Fx_constant = str(sp.factor(q_resy)) if resy_F_Fx_factor_ok else "nan"

    # 2) Conjugate cubic factor from eliminating X between F and cubicX.
    res_F_cubicx = sp.factor(sp.resultant(F, cubicX, X))
    Q_LY = 256 * y**3 + 195 * y**2 + 93 * y - 48
    target_res_F = P_LY * Q_LY
    q_res_F = sp.together(res_F_cubicx / target_res_F)
    res_F_cubicx_factor_ok = _is_constant_in(q_res_F, y)
    res_F_cubicx_constant = str(sp.factor(q_res_F)) if res_F_cubicx_factor_ok else "nan"

    # Discriminants and mod-37 factorizations for the three cubic controls.
    ctrl_cubic_y = 16 * y**3 - 8 * y**2 - 4 * y + 1
    disc_ctrl_cubic_y = int(sp.discriminant(ctrl_cubic_y, y))
    disc_ctrl_cubic_y_fac = sp.factorint(disc_ctrl_cubic_y)

    disc_conj_cubic_y = int(sp.discriminant(Q_LY, y))
    disc_conj_cubic_y_fac = sp.factorint(disc_conj_cubic_y)

    def _factor_mod(expr: sp.Expr, modulus: int) -> str:
        Pm = sp.Poly(sp.expand(expr), y, modulus=modulus)
        return str(sp.factor(Pm.as_expr(), modulus=modulus))

    mod37_ctrl = _factor_mod(ctrl_cubic_y, 37)
    mod37_leyang = _factor_mod(P_LY, 37)
    mod37_conj = _factor_mod(Q_LY, 37)

    # Special rational point label: y(-P)=6 for P=(2,-5/2).
    y_of_minus_P = int(sp.together(y_map.subs({X: sp.Integer(2), Y: sp.Rational(5, 2)})))

    # Puiseux checks near y0=0 and y0=1 (to O(t^4))
    X_series_0_plus = (
        1
        + (1 / sp.sqrt(2)) * t
        + sp.Rational(5, 8) * t**2
        - sp.Rational(43, 64) * (1 / sp.sqrt(2)) * t**3
    )
    X_series_0_minus = (
        1
        - (1 / sp.sqrt(2)) * t
        + sp.Rational(5, 8) * t**2
        + sp.Rational(43, 64) * (1 / sp.sqrt(2)) * t**3
    )
    expr0p = sp.expand(F.subs({X: X_series_0_plus, y: t**2}))
    expr0m = sp.expand(F.subs({X: X_series_0_minus, y: t**2}))
    puiseux_y0_0_ok = _series_order_at_least(expr0p, t, 4) and _series_order_at_least(expr0m, t, 4)

    X_series_1_plus = (
        -1
        + (1 / sp.sqrt(6)) * t
        + sp.Rational(29, 72) * t**2
        + sp.Rational(245, 1728) * (1 / sp.sqrt(6)) * t**3
    )
    X_series_1_minus = (
        -1
        - (1 / sp.sqrt(6)) * t
        + sp.Rational(29, 72) * t**2
        - sp.Rational(245, 1728) * (1 / sp.sqrt(6)) * t**3
    )
    expr1p = sp.expand(F.subs({X: X_series_1_plus, y: 1 - t**2}))
    expr1m = sp.expand(F.subs({X: X_series_1_minus, y: 1 - t**2}))
    puiseux_y0_1_ok = _series_order_at_least(expr1p, t, 4) and _series_order_at_least(expr1m, t, 4)

    # Puiseux check near y=infty: set y=t^(-4) and solve for the x-branch lambda(t).
    # We validate the manuscript jet by checking F(lambda(t), t^(-4)) * t^8 = O(t^8).
    lam_infty = (
        t ** (-2)
        + sp.Rational(1, 2) * t ** (-1)
        + sp.Rational(1, 4)
        + sp.Rational(7, 64) * t
        + sp.Rational(37, 128) * t**2
        - sp.Rational(729, 4096) * t**3
    )
    expr_inf = sp.expand(F.subs({X: lam_infty, y: t ** (-4)}) * t**8)
    puiseux_infty_ok = _series_order_at_least(expr_inf, t, 8)
    puiseux_infty_branches_ok = True
    for k in range(4):
        lam_k = sp.expand(lam_infty.subs(t, (sp.I**k) * t))
        expr_k = sp.expand(F.subs({X: lam_k, y: t ** (-4)}) * t**8)
        puiseux_infty_branches_ok = puiseux_infty_branches_ok and _series_order_at_least(expr_k, t, 8)

    # General coefficient formula at Lee–Yang branch points.
    a = sp.Symbol("a")
    ycrit_a = (4 * a**3 - 3 * a**2 - 2 * a + 1) / (4 * a)
    Fy = sp.diff(F, y).subs({X: a, y: ycrit_a})
    Fxx = sp.diff(F, X, 2).subs({X: a, y: ycrit_a})
    c0_sq = sp.simplify(-2 * Fy / Fxx)
    expected_c0_sq = sp.Rational(2, 3) * (3 * a**2 - 1) / (a**2 - 1)
    diff_c = sp.together(c0_sq - expected_c0_sq)
    num_c, den_c = diff_c.as_numer_denom()
    # Reduce numerator modulo the cubic certificate (valid on the LY branch points).
    num_red = _reduce_mod(num_c, a, 16 * a**3 - 9 * a**2 + 1)
    c0_sq_formula_ok = bool(sp.simplify(num_red) == 0)

    # Next Puiseux jet coefficient (linear term in y-y0): beta = -F_xy/F_xx + (F_xxx*F_y)/(3 F_xx^2).
    Fxy = sp.diff(F, X, y).subs({X: a, y: ycrit_a})
    Fxxx = sp.diff(F, X, 3).subs({X: a, y: ycrit_a})
    beta_coeff = sp.simplify(-Fxy / Fxx + sp.Rational(1, 3) * (Fxxx * Fy) / (Fxx**2))
    expected_beta = -a * (3 * a**2 + 16 * a + 5) / (18 * (a**2 - 1) ** 2)
    diff_b = sp.together(beta_coeff - expected_beta)
    num_b, den_b = diff_b.as_numer_denom()
    num_b_red = _reduce_mod(num_b, a, 16 * a**3 - 9 * a**2 + 1)
    beta_formula_ok = bool(sp.simplify(num_b_red) == 0)

    # Next Puiseux jet coefficient (t^3 term): gamma = G(a)/c0 so that gamma*c0 is rational in a.
    k2 = c0_sq
    Fyy = sp.diff(F, y, 2).subs({X: a, y: ycrit_a})
    Fxxy = sp.diff(F, X, 2, y).subs({X: a, y: ycrit_a})
    Fxxxx = sp.diff(F, X, 4).subs({X: a, y: ycrit_a})
    bracket = sp.simplify(
        sp.Rational(1, 2) * Fxx * beta_coeff**2
        + Fxy * beta_coeff
        + sp.Rational(1, 2) * Fxxx * k2 * beta_coeff
        + sp.Rational(1, 2) * Fyy
        + sp.Rational(1, 2) * Fxxy * k2
        + sp.Rational(1, 24) * Fxxxx * (k2**2)
    )
    gamma_times_c0 = sp.simplify(-bracket / Fxx)
    expected_gamma_times_c0 = -a**2 * (
        1152 * a**7
        - 1152 * a**6
        - 280 * a**5
        + 723 * a**4
        - 312 * a**3
        + 30 * a**2
        + 16 * a
        - 5
    ) / (2 * (8 * a**3 - 3 * a**2 - 1) ** 4)
    diff_g = sp.together(gamma_times_c0 - expected_gamma_times_c0)
    num_g, den_g = diff_g.as_numer_denom()
    num_g_red = _reduce_mod(num_g, a, 16 * a**3 - 9 * a**2 + 1)
    gamma_formula_ok = bool(sp.simplify(num_g_red) == 0)

    # Genus computations by Riemann–Hurwitz (pure integers).
    # S4-splitting cover: degree 24, branch e = [4,2,2,2,2,2].
    n_s4 = 24
    e_list = [4, 2, 2, 2, 2, 2]
    ram = sum(n_s4 * (1 - sp.Rational(1, e)) for e in e_list)
    genus_s4 = int(((-2) * n_s4 + ram + 2) / 2)

    # Sign quadratic quotient: degree 2, 6 branch points (odd degree 5 polynomial => infinity branches).
    n2 = 2
    e_list2 = [2, 2, 2, 2, 2, 2]
    ram2 = sum(n2 * (1 - sp.Rational(1, e)) for e in e_list2)
    genus2 = int(((-2) * n2 + ram2 + 2) / 2)

    # V4 quotient (S3-cover): degree 6, 6 branch points all of index 2.
    n6 = 6
    e_list6 = [2, 2, 2, 2, 2, 2]
    ram6 = sum(n6 * (1 - sp.Rational(1, e)) for e in e_list6)
    genus6 = int(((-2) * n6 + ram6 + 2) / 2)

    # --- Bad prime 37: discriminant ridge degeneration point counts ---
    p_bad = 37

    def _legendre(a: int, p0: int) -> int:
        a %= p0
        if a == 0:
            return 0
        return 1 if pow(a, (p0 - 1) // 2, p0) == 1 else -1

    def _count_hyperelliptic_fp(rhs_fn, deg: int, p0: int) -> int:
        cnt = 1  # point at infinity (deg odd)
        for yy in range(p0):
            rhs = int(rhs_fn(yy)) % p0
            if rhs == 0:
                cnt += 1
            else:
                if _legendre(rhs, p0) == 1:
                    cnt += 2
        if deg % 2 != 1:
            raise RuntimeError("Expected odd degree for a single point at infinity.")
        return int(cnt)

    def _rhs_C37(yy: int) -> int:
        yy %= p_bad
        return (3 * yy * (yy - 1) * (yy - 14) * (yy - 6) * (yy - 6)) % p_bad

    def _rhs_E14(yy: int) -> int:
        yy %= p_bad
        return (3 * yy * (yy - 1) * (yy - 14)) % p_bad

    C_Fp = _count_hyperelliptic_fp(_rhs_C37, 5, p_bad)
    E14_Fp = _count_hyperelliptic_fp(_rhs_E14, 3, p_bad)

    # Count over F_{p^2} using the quadratic character in F_{p^2}=F_p[alpha]/(alpha^2-d).
    def _find_nonsquare(p0: int) -> int:
        for d0 in range(2, p0):
            if pow(d0, (p0 - 1) // 2, p0) == p0 - 1:
                return int(d0)
        raise RuntimeError("No nonsquare found (unexpected).")

    d_ns = _find_nonsquare(p_bad)
    q_bad = p_bad * p_bad
    Fp2 = Tuple[int, int]  # a + b*alpha

    def _fp2_add(u: Fp2, v: Fp2) -> Fp2:
        return ((u[0] + v[0]) % p_bad, (u[1] + v[1]) % p_bad)

    def _fp2_sub(u: Fp2, v: Fp2) -> Fp2:
        return ((u[0] - v[0]) % p_bad, (u[1] - v[1]) % p_bad)

    def _fp2_mul(u: Fp2, v: Fp2) -> Fp2:
        a0, b0 = u
        c0, e0 = v
        return ((a0 * c0 + b0 * e0 * d_ns) % p_bad, (a0 * e0 + b0 * c0) % p_bad)

    def _fp2_sqr(u: Fp2) -> Fp2:
        return _fp2_mul(u, u)

    def _fp2_pow(u: Fp2, n: int) -> Fp2:
        r: Fp2 = (1, 0)
        a0 = u
        k = int(n)
        while k > 0:
            if k & 1:
                r = _fp2_mul(r, a0)
            a0 = _fp2_mul(a0, a0)
            k >>= 1
        return r

    def _fp2_is_zero(u: Fp2) -> bool:
        return (u[0] % p_bad == 0) and (u[1] % p_bad == 0)

    def _quad_char_fp2(u: Fp2) -> int:
        if _fp2_is_zero(u):
            return 0
        t = _fp2_pow(u, (q_bad - 1) // 2)
        if t == (1, 0):
            return 1
        if t == (p_bad - 1, 0):
            return -1
        raise RuntimeError(f"Unexpected quadratic character in F_{p_bad**2}: {t}")

    def _rhs_C37_fp2(yy: Fp2) -> Fp2:
        y0 = yy
        term = _fp2_mul(y0, _fp2_sub(y0, (1, 0)))
        term = _fp2_mul(term, _fp2_sub(y0, (14, 0)))
        t = _fp2_sub(y0, (6, 0))
        term = _fp2_mul(term, _fp2_sqr(t))
        return _fp2_mul((3, 0), term)

    def _rhs_E14_fp2(yy: Fp2) -> Fp2:
        y0 = yy
        term = _fp2_mul(y0, _fp2_sub(y0, (1, 0)))
        term = _fp2_mul(term, _fp2_sub(y0, (14, 0)))
        return _fp2_mul((3, 0), term)

    def _count_hyperelliptic_fp2(rhs_fn, deg: int) -> int:
        cnt = 1  # point at infinity
        for a0 in range(p_bad):
            for b0 in range(p_bad):
                yy = (a0, b0)
                rhs = rhs_fn(yy)
                if _fp2_is_zero(rhs):
                    cnt += 1
                else:
                    if _quad_char_fp2(rhs) == 1:
                        cnt += 2
        if deg % 2 != 1:
            raise RuntimeError("Expected odd degree for a single point at infinity.")
        return int(cnt)

    C_Fp2 = _count_hyperelliptic_fp2(_rhs_C37_fp2, 5)
    E14_Fp2 = _count_hyperelliptic_fp2(_rhs_E14_fp2, 3)
    a_E14 = int(p_bad + 1 - E14_Fp)
    nonsplit_ok = bool((C_Fp - E14_Fp == 1) and (C_Fp2 - E14_Fp2 == -1) and (a_E14 == 2))

    payload = Payload(
        dy_identity_ok=dy_identity_ok,
        abel_jacobi_ode_ok=abel_jacobi_ode_ok,
        abel_jacobi_ode_constant=abel_jacobi_ode_constant,
        abel_jacobi_ode_exact_ok=abel_jacobi_ode_exact_ok,
        delta_quartic_y2_irreducible_ok=delta_quartic_y2_irreducible_ok,
        delta_quartic_disc_factor_ok=delta_quartic_disc_factor_ok,
        disc_q5=disc_q5,
        disc_q5_factorization={str(int(p)): int(e) for p, e in disc_q5_fac.items()},
        critical_x_factor_ok=critical_x_factor_ok,
        resy_F_Fx_factor_ok=resy_F_Fx_factor_ok,
        resy_F_Fx_constant=resy_F_Fx_constant,
        res_F_cubicx_factor_ok=res_F_cubicx_factor_ok,
        res_F_cubicx_constant=res_F_cubicx_constant,
        leyang_resultant_ok=leyang_resultant_ok,
        leyang_resultant_constant=leyang_resultant_constant,
        leyang_resultant_exact_ok=leyang_resultant_exact_ok,
        norm_identity_ok=norm_identity_ok,
        norm_2division_ok=norm_2division_ok,
        norm_2Y_ok=norm_2Y_ok,
        disc_ctrl_cubic_y=disc_ctrl_cubic_y,
        disc_ctrl_cubic_y_factorization={str(int(p)): int(e) for p, e in disc_ctrl_cubic_y_fac.items()},
        disc_conj_cubic_y=disc_conj_cubic_y,
        disc_conj_cubic_y_factorization={str(int(p)): int(e) for p, e in disc_conj_cubic_y_fac.items()},
        mod37_ctrl_cubic_y=mod37_ctrl,
        mod37_leyang_cubic_y=mod37_leyang,
        mod37_conj_cubic_y=mod37_conj,
        y_of_minus_P=y_of_minus_P,
        disc_cubic_x=int(disc_cubic_x),
        disc_cubic_x_factorization={str(int(p)): int(e) for p, e in disc_cubic_x_fac.items()},
        disc_leyang=int(disc_leyang),
        puiseux_y0_0_ok=puiseux_y0_0_ok,
        puiseux_y0_1_ok=puiseux_y0_1_ok,
        puiseux_infty_ok=puiseux_infty_ok,
        puiseux_infty_branches_ok=puiseux_infty_branches_ok,
        c0_sq_formula_ok=c0_sq_formula_ok,
        beta_formula_ok=beta_formula_ok,
        gamma_formula_ok=gamma_formula_ok,
        genus_s4_splitting=genus_s4,
        genus_sign_quadratic=genus2,
        genus_v4_quotient=genus6,
        badprime_37_C_Fp=int(C_Fp),
        badprime_37_E14_Fp=int(E14_Fp),
        badprime_37_C_minus_E14_Fp=int(C_Fp - E14_Fp),
        badprime_37_C_Fp2=int(C_Fp2),
        badprime_37_E14_Fp2=int(E14_Fp2),
        badprime_37_C_minus_E14_Fp2=int(C_Fp2 - E14_Fp2),
        badprime_37_E14_trace_a=int(a_E14),
        badprime_37_nonsplit_node_ok=bool(nonsplit_ok),
    )

    if not args.no_output:
        out = export_dir() / "fold_zm_elliptic_leyang_cover_geometry_audit.json"
        _write_json(out, asdict(payload))
        print(f"[fold-zm-elliptic-leyang-cover-geom] wrote {out}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-leyang-cover-geom] checks:"
        f" dy={dy_identity_ok} ajode={abel_jacobi_ode_ok} ajode_c={abel_jacobi_ode_constant}"
        f" ajode_exact={abel_jacobi_ode_exact_ok} critX={critical_x_factor_ok} leyang_res={leyang_resultant_ok}"
        f" leyang_c={leyang_resultant_constant} leyang_exact={leyang_resultant_exact_ok}"
        f" y2_irr={delta_quartic_y2_irreducible_ok} disc={delta_quartic_disc_factor_ok} discQ5={disc_q5}"
        f" norm={norm_identity_ok} norm2div={norm_2division_ok} norm2Y={norm_2Y_ok}"
        f" resy={resy_F_Fx_factor_ok} resFg={res_F_cubicx_factor_ok} y(-P)={y_of_minus_P}"
        f" puiseux0={puiseux_y0_0_ok} puiseux1={puiseux_y0_1_ok}"
        f" puiseuxInf={puiseux_infty_ok} puiseuxInf4={puiseux_infty_branches_ok}"
        f" c0sq={c0_sq_formula_ok} beta={beta_formula_ok} gamma={gamma_formula_ok}"
        f" genusS4={genus_s4} genus2={genus2} genus6={genus6} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-leyang-cover-geom] done", flush=True)


if __name__ == "__main__":
    main()

