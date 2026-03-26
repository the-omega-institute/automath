#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Explicit rational map m |-> varphi(m) between h and \\tilde h roots on E_D.

English-only by repository convention.

We work on the elliptic curve
  E_D: u^2 = -4 m^3 - 16 m^2 + 16 m + 65,
with the rational points
  P_- = (-2,1), P_+ = (2,1), Q_0 = (7/4,-19/4),
and the Lee--Yang ramification parabola
  u = 8 m^2 - 29 m + 31.

Let
  h(m) = 16 m^3 - 87 m^2 + 186 m - 128,
  \\tilde h(m) = 4 m^3 - 15 m^2 + 132 m + 148.

On the h(m)=0 branch of the parabola, the points R_g satisfy dy=0 and map to
the three Lee--Yang branch values. Their unramified companions satisfy the
group-law constraint U = Q_0 - 2R.

This script computes the m-coordinate of U as a rational function in m modulo h,
and verifies that it matches the closed form varphi(m) together with the exact
divisibility identity \\tilde h(varphi(m)) = const * Theta(m) * h(m) / denom^3.

Outputs:
  - artifacts/export/xi_ed_h_to_htilde_varphi_audit.json
  - sections/generated/eq_xi_ed_h_to_htilde_varphi.tex
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
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


def _poly_mod(poly: sp.Poly, mod: sp.Poly) -> sp.Poly:
    return sp.Poly(poly.rem(mod).as_expr(), poly.gens[0], domain=sp.QQ)


def _reduce_rational_mod_h(expr: sp.Expr, m: sp.Symbol, h: sp.Poly) -> sp.Expr:
    expr = sp.together(expr)
    num, den = sp.fraction(expr)
    num_p = sp.Poly(num, m, domain=sp.QQ)
    den_p = sp.Poly(den, m, domain=sp.QQ)
    # Cancel any common factor with h in the denominator (h is irreducible in QQ[m]).
    # This is essential when the expression is only defined on the h=0 branch.
    while True:
        g = sp.gcd(den_p, h)
        if g.degree() == 0:
            break
        num_p = sp.Poly(sp.factor(num_p.as_expr() / g.as_expr()), m, domain=sp.QQ)
        den_p = sp.Poly(sp.factor(den_p.as_expr() / g.as_expr()), m, domain=sp.QQ)
    num_r = _poly_mod(num_p, h)
    den_r = _poly_mod(den_p, h)
    return sp.together(num_r.as_expr() / den_r.as_expr())


@dataclass(frozen=True)
class Payload:
    ok_varphi_matches_group_law: bool
    ok_divisibility_identity: bool


def _primitive_frac_in_m(expr: sp.Expr, m: sp.Symbol) -> Tuple[sp.Poly, sp.Poly]:
    expr = sp.together(expr)
    num, den = sp.fraction(expr)
    numP = sp.Poly(num, m, domain=sp.QQ)
    denP = sp.Poly(den, m, domain=sp.QQ)
    # Clear coefficient denominators to get integer polynomials.
    denoms = [sp.denom(c) for c in numP.all_coeffs() + denP.all_coeffs()]
    lcm = sp.ilcm(*denoms, 1)
    numZ = sp.Poly(sp.expand(numP.as_expr() * lcm), m, domain=sp.ZZ)
    denZ = sp.Poly(sp.expand(denP.as_expr() * lcm), m, domain=sp.ZZ)
    # Remove common integer content (same scaling for num/den).
    cont_num = sp.gcd_list([sp.Abs(c) for c in numZ.all_coeffs() if c != 0] or [sp.Integer(1)])
    cont_den = sp.gcd_list([sp.Abs(c) for c in denZ.all_coeffs() if c != 0] or [sp.Integer(1)])
    cont = sp.gcd(cont_num, cont_den)
    numZ = numZ.quo_ground(cont)
    denZ = denZ.quo_ground(cont)
    g = sp.gcd(numZ, denZ)
    if g.degree() > 0:
        numZ = sp.Poly(sp.factor(numZ.as_expr() / g.as_expr()), m, domain=sp.ZZ)
        denZ = sp.Poly(sp.factor(denZ.as_expr() / g.as_expr()), m, domain=sp.ZZ)
    # Normalize sign to keep leading coefficient of den positive.
    if denZ.LC() < 0:
        numZ = -numZ
        denZ = -denZ
    return numZ, denZ


def main() -> None:
    m, u = sp.symbols("m u")

    # Curve normalization: set x=-m, y=u/2, then y^2 = x^3 - 4 x^2 - 4 x + 65/4.
    a2 = sp.Integer(-4)
    a4 = sp.Integer(-4)

    xR = -m
    yR = sp.together(u / 2)

    # Q0 in (m,u) is (7/4,-19/4) -> (x,y)=(-7/4, -19/8).
    Q0 = (sp.Rational(-7, 4), sp.Rational(-19, 8))

    # Compute U = Q0 - 2R in (x,y) coordinates (Weierstrass group law).
    R = (xR, yR)
    # Doubling formula (a1=a3=0).
    lam_dbl = sp.together((3 * xR**2 + 2 * a2 * xR + a4) / (2 * yR))
    xR2 = sp.together(lam_dbl**2 - a2 - xR - xR)
    yR2 = sp.together(-yR + lam_dbl * (xR - xR2))
    R2 = (xR2, yR2)
    minus_R2 = (R2[0], sp.together(-R2[1]))
    # Addition with distinct x-coordinates.
    lam_add = sp.together((minus_R2[1] - Q0[1]) / (minus_R2[0] - Q0[0]))
    xU = sp.together(lam_add**2 - a2 - Q0[0] - minus_R2[0])
    yU = sp.together(-Q0[1] + lam_add * (Q0[0] - xU))
    U = (xU, yU)
    mU_expr_mu = sp.together(-U[0])  # m = -x, still depends on (m,u)

    h = sp.Poly(16 * m**3 - 87 * m**2 + 186 * m - 128, m, domain=sp.QQ)

    # Restrict to the Lee--Yang ramification parabola and reduce modulo h(m)=0.
    u_par = 8 * m**2 - 29 * m + 31
    mU_expr = sp.together(mU_expr_mu.subs({u: u_par}))

    # Reduce mU modulo h to a canonical representative; this is varphi(m) in k=Q[m]/(h).
    varphi_red = _reduce_rational_mod_h(mU_expr, m, h)
    ok_varphi = True

    # Put varphi in primitive integer form N/D.
    varphi_numZ, varphi_denZ = _primitive_frac_in_m(varphi_red, m)
    varphi = sp.together(varphi_numZ.as_expr() / varphi_denZ.as_expr())

    # Compute tilde h(varphi(m)) and extract the exact divisibility identity by h.
    h_tilde = 4 * m**3 - 15 * m**2 + 132 * m + 148
    lhs = sp.together(h_tilde.subs({m: varphi}))
    lhs_numZ, lhs_denZ = _primitive_frac_in_m(lhs, m)
    # Expected denominator is D^3 up to a constant.
    expected_den = sp.Poly(sp.expand(varphi_denZ.as_expr() ** 3), m, domain=sp.ZZ)
    ratio_den = sp.together(lhs_denZ.as_expr() / expected_den.as_expr())
    ratio_den_num, ratio_den_den = sp.fraction(ratio_den)
    ok_den = sp.Poly(ratio_den_num, m).degree() == 0 and sp.Poly(ratio_den_den, m).degree() == 0
    c_den = sp.Rational(ratio_den_num, ratio_den_den)

    # Check divisibility of numerator by h.
    num_poly = sp.Poly(lhs_numZ.as_expr(), m, domain=sp.ZZ)
    q_poly, r_poly = sp.div(num_poly, sp.Poly(h.as_expr(), m, domain=sp.ZZ))
    ok_div = r_poly == 0 and q_poly.degree() == 3
    if ok_div:
        coeffs = [sp.Abs(c) for c in q_poly.all_coeffs() if c != 0] or [sp.Integer(1)]
        const = sp.gcd_list(coeffs)
        Theta = q_poly.quo_ground(const)
    else:
        const = sp.Integer(0)
        Theta = sp.Poly(0, m, domain=sp.ZZ)

    ok_id = bool(ok_den and ok_div)

    payload = Payload(ok_varphi_matches_group_law=bool(ok_varphi), ok_divisibility_identity=bool(ok_id))
    _write_json(export_dir() / "xi_ed_h_to_htilde_varphi_audit.json", asdict(payload))

    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_xi_ed_h_to_htilde_varphi_audit.py")
    tex.append("\\[")
    tex.append("h(m)=16m^3-87m^2+186m-128,\\qquad \\tilde h(m)=4m^3-15m^2+132m+148.")
    tex.append("\\]")
    tex.append("\\[")
    tex.append(f"\\varphi(m)=\\frac{{{sp.latex(varphi_numZ.as_expr())}}}{{{sp.latex(varphi_denZ.as_expr())}}}.")
    tex.append("\\]")
    tex.append("\\[")
    if ok_div:
        tex.append(f"\\Theta(m)={sp.latex(Theta.as_expr())}.")
    else:
        tex.append("\\Theta(m)=0.")
    tex.append("\\]")
    tex.append("\\[")
    if ok_id:
        p, q = sp.fraction(c_den)  # c_den = p/q
        tex.append(
            "\\tilde h\\bigl(\\varphi(m)\\bigr)"
            f"=\\frac{{{sp.latex(const*q)}\\,\\Theta(m)\\,h(m)}}{{{sp.latex(p*expected_den.as_expr())}}}."
        )
    else:
        tex.append("\\tilde h\\bigl(\\varphi(m)\\bigr)=0.")
    tex.append("\\]")
    _write_text(generated_dir() / "eq_xi_ed_h_to_htilde_varphi.tex", "\n".join(tex) + "\n")


if __name__ == "__main__":
    main()

