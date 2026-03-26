#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the elliptic-curve uniformization identities for Pi(lambda,y) and Z_m(y).

This script is English-only by repository convention.

We verify, by exact symbolic algebra in Q[...]:
  - The short Weierstrass model E: Y^2 = lam^3 - lam + 1/4 has discriminant 37.
  - The integral scaling model E': y'^2 = x'^3 - 16 x' + 16 has discriminant 2^12*37
    and #E'(F_3)=7, #E'(F_5)=8 (torsion-triviality certificate).
  - The Lattès doubling map on the x-line:
      Phi(lam) = (lam^4 + 2 lam^2 - 2 lam + 1) / (4 lam^3 - 4 lam + 1),
    and its critical sextic; and that the sextic equals psi_4/(2Y).
  - The weight coordinate y = lam^2 + Y - 1/2 satisfies:
      y^2 - (2 lam^2 - 1) y + lam(lam-1)^2(lam+1) = 0,
    with discriminant 4 lam^3 - 4 lam + 1 = 4 Y^2,
    and the equivalent quartic Pi(lam,y)=0.
  - The ramification eliminations leading to g(lam)=16 lam^3 - 9 lam^2 + 1
    and the Lee–Yang cubic P_LY(y)=256 y^3 + 411 y^2 + 165 y + 32,
    with resultant certificate.
  - The resolvent cubic R(z,y) discriminant identity:
      Disc_z(R) = Disc_lam(Pi) = -y(y-1) P_LY(y).
  - An equivalent integral-scaled resolvent cubic R_std(z,y) has
      Disc_z(R_std) = 2^24 * Disc_lam(Pi).
  - A field-trace representation of Z_m(y) over K=Q(y)(lam)/Q(y) with denominators
    supported only at y*P_LY(y)=0, plus the cleared-denominator polynomial identity.
  - The residue / partial-fraction construction of the trace weight u(lam) modulo Pi.
  - Discriminants/resultants showing the forced appearance of the prime 37, and
    small-prime factorizations modulo 3, 31, 37.

Outputs (default):
  - artifacts/export/fold_zm_elliptic_audit.json
  - sections/generated/eq_fold_zm_elliptic_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _poly_int_string(p: sp.Expr, var: sp.Symbol) -> str:
    """Pretty string for a polynomial with integer coefficients."""
    P = sp.Poly(sp.expand(p), var, domain=sp.ZZ)
    return str(P.as_expr())


def _factor_mod(p: sp.Expr, var: sp.Symbol, modulus: int) -> str:
    P = sp.Poly(sp.expand(p), var, modulus=modulus)
    return str(sp.factor(P.as_expr(), modulus=modulus))


def _groebner_is_unit(gb: sp.GroebnerBasis) -> bool:
    # In SymPy, a Groebner basis contains 1 iff the ideal is the whole ring.
    return any(p.as_expr() == 1 for p in gb.polys)


def _count_points_short_weierstrass(p: int, a: int, b: int) -> int:
    """Count points on y^2 = x^3 + a x + b over F_p (including O)."""
    a %= p
    b %= p
    cnt = 1  # point at infinity
    for x in range(p):
        rhs = (x * x * x + a * x + b) % p
        for yy in range(p):
            if (yy * yy - rhs) % p == 0:
                cnt += 1
    return cnt


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit elliptic uniformization identities for Pi(lambda,y) and Z_m(y)")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    lam, Y, y = sp.symbols("lam Y y")

    # --- Curve data and discriminant ---
    a = sp.Integer(-1)
    b = sp.Rational(1, 4)
    disc_E = sp.simplify(-16 * (4 * a**3 + 27 * b**2))  # short Weierstrass discriminant
    disc_E_ok = disc_E == 37

    # --- Torsion triviality certificate via good reduction counts ---
    # Integral model via x'=4x, y'=8y:  y'^2 = x'^3 - 16 x' + 16.
    disc_Eprime = -16 * (4 * (-16) ** 3 + 27 * (16) ** 2)
    disc_Eprime_ok = disc_Eprime == 2**12 * 37
    Eprime_F3 = _count_points_short_weierstrass(3, -16, 16)
    Eprime_F5 = _count_points_short_weierstrass(5, -16, 16)
    torsion_gcd_3_5 = math.gcd(Eprime_F3, Eprime_F5)
    torsion_trivial_ok = torsion_gcd_3_5 == 1

    # --- Lattès doubling map on x-line ---
    # General duplication formula in short Weierstrass: y^2 = x^3 + ax + b
    x2_general = (lam**4 - 2 * a * lam**2 - 8 * b * lam + a**2) / (4 * lam**3 + 4 * a * lam + 4 * b)
    Phi = sp.simplify(x2_general.subs({a: -1, b: sp.Rational(1, 4)}))
    Phi_expected = (lam**4 + 2 * lam**2 - 2 * lam + 1) / (4 * lam**3 - 4 * lam + 1)
    Phi_ok = sp.factor(Phi - Phi_expected) == 0

    denom_2div = 4 * lam**3 - 4 * lam + 1

    # Derivative critical sextic
    Phi_simpl = sp.together(Phi_expected)
    Phi_prime = sp.diff(Phi_simpl, lam)
    Phi_prime_num = sp.factor(sp.together(Phi_prime).as_numer_denom()[0])
    # Remove any gcd factors that are not relevant for critical locus in P^1
    Phi_prime_num_sqfree = sp.factor(sp.Poly(Phi_prime_num, lam).sqf_part().as_expr())
    crit_poly = 2 * lam**6 - 10 * lam**4 + 10 * lam**3 - 10 * lam**2 + 2 * lam + 1
    crit_ok = sp.factor(Phi_prime_num_sqfree - crit_poly) == 0

    # 4-division polynomial psi_4: standard formula
    psi4_over_2Y = lam**6 + 5 * a * lam**4 + 20 * b * lam**3 - 5 * a**2 * lam**2 - 4 * a * b * lam - 8 * b**2 - a**3
    psi4_over_2Y = sp.simplify(psi4_over_2Y.subs({a: -1, b: sp.Rational(1, 4)}))
    psi4_ok = sp.factor(2 * psi4_over_2Y - crit_poly) == 0

    # --- Weight coordinate and quadratic/quartic relations ---
    yfun = lam**2 + Y - sp.Rational(1, 2)
    curve_residual = sp.expand(Y**2 - (lam**3 - lam + sp.Rational(1, 4)))

    quad_rel = sp.expand(yfun**2 - (2 * lam**2 - 1) * yfun + lam * (lam - 1) ** 2 * (lam + 1))
    quad_rel_simpl = sp.factor(quad_rel - curve_residual)
    quad_rel_ok = quad_rel_simpl == 0

    quad_disc = sp.factor((2 * lam**2 - 1) ** 2 - 4 * lam * (lam - 1) ** 2 * (lam + 1))
    quad_disc_expected = 4 * lam**3 - 4 * lam + 1
    quad_disc_ok = sp.factor(quad_disc - quad_disc_expected) == 0

    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    # Check that Pi(lam,y) is the expanded form of the quadratic relation in y
    Pi_from_quad = sp.expand((y**2 - (2 * lam**2 - 1) * y + lam * (lam - 1) ** 2 * (lam + 1)).subs({y: y}))
    Pi_from_quad = sp.expand(Pi_from_quad - y**2 + (2 * lam**2 - 1) * y)  # isolate constant term
    Pi_ok = sp.factor(Pi - (lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1))) == 0
    # (Pi_ok is tautological, but we keep Pi symbol as the canonical quartic.)

    disc_Pi = sp.factor(sp.discriminant(Pi, lam))
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    disc_Pi_expected = -y * (y - 1) * P_LY
    disc_Pi_ok = sp.factor(disc_Pi - disc_Pi_expected) == 0

    # --- dy=0 condition and elimination to g(lam) and P_LY(y) ---
    # On E, dY/dlam = (3 lam^2 + a)/(2Y) with a=-1 -> (3 lam^2 - 1)/(2Y)
    dy_num = sp.factor(4 * lam * Y + 3 * lam**2 - 1)
    # Substitute Y = (1-3 lam^2)/(4 lam) into curve equation and factor
    Y_branch = (1 - 3 * lam**2) / (4 * lam)
    branch_eq = sp.factor(sp.together(Y_branch**2 - (lam**3 - lam + sp.Rational(1, 4))).as_numer_denom()[0])
    g = 16 * lam**3 - 9 * lam**2 + 1
    # The numerator is defined up to an overall unit (here a sign).
    branch_factor_ok = sp.factor(branch_eq + (lam**2 - 1) * g) == 0

    # Resultant certificate for P_LY(y)
    lin_y = 4 * lam * y - (4 * lam**3 - 3 * lam**2 - 2 * lam + 1)
    res = sp.resultant(g, lin_y, lam)
    res_fact = sp.factor(res)
    res_ok = sp.factor(res_fact + 64 * P_LY) == 0

    # --- Resolvent cubic discriminant identity ---
    z = sp.Symbol("z")
    R = z**3 + (1 + 2 * y) * z**2 - (1 + 4 * y + 4 * y**2) * z - (1 + 5 * y + 13 * y**2 + 8 * y**3)
    disc_R = sp.factor(sp.discriminant(R, z))
    disc_R_ok = sp.factor(disc_R - disc_Pi_expected) == 0

    R_std = 64 * z**3 - (176 + 256 * y) * z**2 + (76 + 128 * y) * z - (64 * y**2 - 48 * y + 9)
    disc_R_std = sp.factor(sp.discriminant(R_std, z))
    disc_R_std_ok = sp.factor(disc_R_std - 2**24 * disc_Pi_expected) == 0

    # Specialization y=2: quick irreducibility witness for the resolvent cubic
    R_y2 = sp.Poly(sp.expand(R.subs({y: 2})), z, domain=sp.ZZ)
    R_y2_const = abs(int(R_y2.TC()))
    R_y2_has_int_root = False
    for d in sp.divisors(R_y2_const):
        if R_y2.eval(d) == 0 or R_y2.eval(-d) == 0:
            R_y2_has_int_root = True
            break
    # (Monic cubic) irreducible over Q iff it has no rational root.
    R_y2_irreducible_ok = not R_y2_has_int_root
    disc_at_y2 = sp.simplify(disc_Pi_expected.subs({y: 2}))
    disc_at_y2_ok = disc_at_y2 == -8108

    # --- Field-trace representation of Z_m(y) ---
    # Z_m satisfies the order-4 recurrence with characteristic Pi(lam,y)=0:
    # Z_{m} = Z_{m-1} + (2y+1) Z_{m-2} - Z_{m-3} - y(y+1) Z_{m-4}
    Z0 = sp.Integer(1)
    Z1 = y + 1
    Z2 = 2 * y + 2
    Z3 = y**2 + 5 * y + 2
    Z_init = [Z0, Z1, Z2, Z3]

    # Power sums s_m = Tr(lam^m) satisfy the same recurrence, with Newton-initial data.
    s0 = sp.Integer(4)
    s1 = sp.Integer(1)
    s2 = 4 * y + 3
    s3 = 6 * y + 1

    def extend_seq(init4: List[sp.Expr], n_max: int) -> List[sp.Expr]:
        seq = init4[:]
        for n in range(0, n_max - 3):
            # compute seq[n+4] from seq[n..n+3]
            seq.append(sp.expand(seq[n + 3] + (2 * y + 1) * seq[n + 2] - seq[n + 1] - y * (y + 1) * seq[n]))
        return seq

    Z_seq = extend_seq(Z_init, 16)  # enough for spot checks
    s_seq = extend_seq([s0, s1, s2, s3], 20)

    M = sp.Matrix([[s_seq[m + k] for k in range(4)] for m in range(4)])
    bvec = sp.Matrix([Z_seq[m] for m in range(4)])
    a_vec = sp.simplify(M.LUsolve(bvec))
    a0, a1, a2, a3 = [sp.simplify(a_vec[i]) for i in range(4)]
    u_poly = sp.simplify(a0 + a1 * lam + a2 * lam**2 + a3 * lam**3)

    # Residue / partial-fraction construction:
    # u(lam) ≡ (lam^3 N(1/lam)) / (d/dlam Pi(lam,y))   (mod Pi),
    # where N(t)=1+yt-yt^2-y^2 t^3 is the generating-function numerator.
    Pi_lam = sp.diff(Pi, lam)
    N_lam = lam**3 + y * lam**2 - y * lam - y**2
    u_residue = sp.together(N_lam / Pi_lam)
    diff_u = sp.together(u_residue - u_poly)
    diff_u_num = sp.expand(diff_u.as_numer_denom()[0])
    diff_u_rem = sp.rem(sp.Poly(diff_u_num, lam), sp.Poly(Pi, lam), lam).as_expr()
    residue_u_ok = sp.factor(diff_u_rem) == 0

    # Check denominator support: only factors y and P_LY(y) (up to units)
    den_factors = []
    for aj in (a0, a1, a2, a3):
        num, den = sp.together(aj).as_numer_denom()
        den_factors.append(sp.factor(den))
    den_lcm = sp.factor(sp.ilcm(*[sp.denom(sp.nsimplify(aj)) for aj in (a0, a1, a2, a3)])) if False else None
    # Exact symbolic check:
    denom_all = sp.factor(sp.lcm_list([sp.together(aj).as_numer_denom()[1] for aj in (a0, a1, a2, a3)]))
    denom_support_ok = sp.factor(denom_all / sp.gcd(denom_all, y * P_LY)) == 1  # denom_all divides y*P_LY

    # Clear denominators by y*P_LY
    A0 = sp.factor(y * P_LY * a0)
    A1 = sp.factor(y * P_LY * a1)
    A2 = sp.factor(y * P_LY * a2)
    A3 = sp.factor(y * P_LY * a3)
    # Verify integrality (coeffs in Z)
    A_int_ok = True
    for Aj in (A0, A1, A2, A3):
        try:
            sp.Poly(Aj, y, domain=sp.ZZ)
        except Exception:
            A_int_ok = False
            break

    # Verify the cleared identity for m up to some bound (symbolic)
    trace_id_ok = True
    for m in range(0, 13):
        lhs = sp.expand(y * P_LY * Z_seq[m])
        rhs = sp.expand(A0 * s_seq[m] + A1 * s_seq[m + 1] + A2 * s_seq[m + 2] + A3 * s_seq[m + 3])
        if sp.factor(lhs - rhs) != 0:
            trace_id_ok = False
            break

    # --- Spectral curve at (∞,∞) in P1_lambda x P1_y ---
    mu, v = sp.symbols("mu v")
    F_mu_v = (1 - mu - mu**2 + mu**3) * v**2 + mu**2 * (mu**2 - 2) * v + mu**4
    disc_v = sp.factor(sp.discriminant(F_mu_v, v))
    disc_v_expected = sp.factor(mu**5 * (mu**3 - 4 * mu**2 + 4))
    disc_v_ok = sp.factor(disc_v - disc_v_expected) == 0

    # --- Discriminants/resultants and mod p factorizations (37 coupling) ---
    disc_P_LY = sp.factor(sp.discriminant(P_LY, y))
    disc_P_LY_expected = sp.factor(-3**9 * 31**2 * 37)
    disc_P_LY_ok = sp.factor(disc_P_LY - disc_P_LY_expected) == 0

    B = sp.expand(y * (y - 1) * P_LY)
    disc_B = sp.factor(sp.discriminant(B, y))
    disc_B_expected = sp.factor(-2**20 * 3**15 * 31**2 * 37)
    disc_B_ok = sp.factor(disc_B - disc_B_expected) == 0
    disc_g = sp.factor(sp.discriminant(g, lam))
    res_g_2div = sp.factor(sp.resultant(g, denom_2div, lam))
    # Mod p factorizations
    P_mod3 = _factor_mod(P_LY, y, 3)
    P_mod31 = _factor_mod(P_LY, y, 31)
    P_mod37 = _factor_mod(P_LY, y, 37)

    # Collision point at lam=5 mod 37 -> y via 4 lam y = 4 lam^3 -3 lam^2 -2 lam + 1
    y_at_5_mod37 = sp.mod_inverse(4 * 5, 37) * (4 * 5**3 - 3 * 5**2 - 2 * 5 + 1)
    y_at_5_mod37 %= 37

    # --- Resolvent cubic: projective closure at infinity and smoothness ---
    Zp, Yp, Wp = sp.symbols("Zp Yp Wp")
    R_h = sp.expand(
        Zp**3
        + (Wp + 2 * Yp) * Zp**2
        - (Wp**2 + 4 * Yp * Wp + 4 * Yp**2) * Zp
        - (Wp**3 + 5 * Yp * Wp**2 + 13 * Yp**2 * Wp + 8 * Yp**3)
    )
    R_h_W0 = sp.factor(R_h.subs({Wp: 0}))
    R_h_W0_expected = sp.factor((Zp - 2 * Yp) * (Zp + 2 * Yp) ** 2)
    R_h_W0_ok = sp.factor(R_h_W0 - R_h_W0_expected) == 0

    # Smoothness in affine chart W=1:
    R_aff = sp.expand(R_h.subs({Wp: 1, Zp: z, Yp: y}))
    dR_aff_dz = sp.diff(R_aff, z)
    dR_aff_dy = sp.diff(R_aff, y)
    gb_aff = sp.groebner([R_aff, dR_aff_dz, dR_aff_dy], z, y, order="lex", domain=sp.QQ)
    resolvent_smooth_affine_ok = _groebner_is_unit(gb_aff)

    # Smoothness at infinity: chart Y=1 (covers all points with W=0 since Y!=0 there)
    Zc, Wc = sp.symbols("Zc Wc")
    R_inf = sp.expand(R_h.subs({Yp: 1, Zp: Zc, Wp: Wc}))
    dR_inf_dZ = sp.diff(R_inf, Zc)
    dR_inf_dW = sp.diff(R_inf, Wc)
    gb_inf = sp.groebner([R_inf, dR_inf_dZ, dR_inf_dW], Zc, Wc, order="lex", domain=sp.QQ)
    resolvent_smooth_infty_ok = _groebner_is_unit(gb_inf)

    payload: Dict[str, object] = {
        "disc_E": int(disc_E),
        "disc_E_ok": bool(disc_E_ok),
        "disc_Eprime": int(disc_Eprime),
        "disc_Eprime_ok": bool(disc_Eprime_ok),
        "Eprime_F3": int(Eprime_F3),
        "Eprime_F5": int(Eprime_F5),
        "torsion_gcd_3_5": int(torsion_gcd_3_5),
        "torsion_trivial_ok": bool(torsion_trivial_ok),
        "Phi_ok": bool(Phi_ok),
        "crit_ok": bool(crit_ok),
        "psi4_ok": bool(psi4_ok),
        "quad_rel_ok": bool(quad_rel_ok),
        "quad_disc_ok": bool(quad_disc_ok),
        "disc_Pi_ok": bool(disc_Pi_ok),
        "branch_factor_ok": bool(branch_factor_ok),
        "resultant_ok": bool(res_ok),
        "disc_R_ok": bool(disc_R_ok),
        "disc_R_std_ok": bool(disc_R_std_ok),
        "R_y2_irreducible_ok": bool(R_y2_irreducible_ok),
        "disc_at_y2": int(disc_at_y2),
        "disc_at_y2_ok": bool(disc_at_y2_ok),
        "residue_u_ok": bool(residue_u_ok),
        "trace_denom_support_ok": bool(denom_support_ok),
        "trace_A_int_ok": bool(A_int_ok),
        "trace_identity_ok": bool(trace_id_ok),
        "disc_P_LY": str(disc_P_LY),
        "disc_g": str(disc_g),
        "res_g_2div": str(res_g_2div),
        "spectral_infty_disc_v": str(disc_v),
        "spectral_infty_disc_v_expected": str(disc_v_expected),
        "spectral_infty_disc_v_ok": bool(disc_v_ok),
        "disc_P_LY_ok": bool(disc_P_LY_ok),
        "disc_B": str(disc_B),
        "disc_B_expected": str(disc_B_expected),
        "disc_B_ok": bool(disc_B_ok),
        "P_mod3": P_mod3,
        "P_mod31": P_mod31,
        "P_mod37": P_mod37,
        "y_at_lam5_mod37": int(y_at_5_mod37),
        "resolvent_projective_W0_factor": str(R_h_W0),
        "resolvent_projective_W0_ok": bool(R_h_W0_ok),
        "resolvent_projective_smooth_affine_ok": bool(resolvent_smooth_affine_ok),
        "resolvent_projective_smooth_infty_ok": bool(resolvent_smooth_infty_ok),
        "a_coeffs": [str(a0), str(a1), str(a2), str(a3)],
        "A_polys": [str(A0), str(A1), str(A2), str(A3)],
    }

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_elliptic_audit.json", payload)

        # Minimal LaTeX certificate snippet (keep it short; main text carries the narrative).
        tex_lines: List[str] = []
        tex_lines.append("% Auto-generated by scripts/exp_fold_zm_elliptic_audit.py")
        tex_lines.append("\\[")
        tex_lines.append(
            "\\Phi(\\lambda)=\\frac{\\lambda^{4}+2\\lambda^{2}-2\\lambda+1}{4\\lambda^{3}-4\\lambda+1},\\qquad"
            "\\Phi'(\\lambda)=0\\iff 2\\lambda^{6}-10\\lambda^{4}+10\\lambda^{3}-10\\lambda^{2}+2\\lambda+1=0."
        )
        tex_lines.append("\\]")
        tex_lines.append("\\[")
        tex_lines.append(
            "y=\\lambda^{2}+Y-\\tfrac12,\\qquad "
            "y^{2}-(2\\lambda^{2}-1)y+\\lambda(\\lambda-1)^{2}(\\lambda+1)=0,\\qquad "
            "\\mathrm{Disc}_{y}=4\\lambda^{3}-4\\lambda+1."
        )
        tex_lines.append("\\]")
        tex_lines.append("\\[")
        tex_lines.append("\\mathrm{Disc}_{\\lambda}(\\Pi)=-y\\,(y-1)\\,(256y^{3}+411y^{2}+165y+32).")
        tex_lines.append("\\]")
        tex_lines.append("\\[")
        tex_lines.append(
            "\\mathrm{Disc}\\bigl(256y^{3}+411y^{2}+165y+32\\bigr)=%s." % sp.latex(disc_P_LY)
        )
        tex_lines.append("\\]")
        tex_lines.append("\\[")
        tex_lines.append(
            "\\mathrm{Disc}\\bigl(y(y-1)(256y^{3}+411y^{2}+165y+32)\\bigr)=%s." % sp.latex(disc_B)
        )
        tex_lines.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_audit.tex", "\n".join(tex_lines) + "\n")


if __name__ == "__main__":
    main()

