#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the phase-resonance resultant for the Fold fiber-weight spectral quartic Pi(lambda,y).

This script is English-only by repository convention.

Let
  Pi(lam,y) = lam^4 - lam^3 - (2y+1) lam^2 + lam + y(y+1).
For u != 0, define
  R(u,y) := Res_lam(Pi(lam,y), Pi(u lam,y)) in Z[u,y].

We verify symbolically:
  - Factorization:
      R(u,y) = y(y+1)(u-1)^4 * F(u,y),
    where F is palindromic of degree 12 in u and degree 6 in y.
  - Explicit palindromic-basis coefficients for F(u,y):
      F = a0 (u^12+1) + a1 (u^11+u) + a2 (u^10+u^2)
          + c9 (u^9+u^3) + c8 (u^8+u^4) + c7 (u^7+u^5) + c6 u^6,
    with the stated integer polynomials a0,a1,a2,c9,c8,c7,c6 in y.
  - Chebyshev compression: letting s:=u+u^{-1}, there exists G(s,y) in Z[s,y] such that
      F(u,y) = u^6 G(s,y),
    and we verify the fully expanded coefficients of G(s,y).
  - Degeneracy at u=1 (s=2):
      G(2,y) = - y(y-1) * (256y^3+411y^2+165y+32).

Outputs:
  - artifacts/export/fold_zm_phase_resonance_resultant_chebyshev_audit.json
  - sections/generated/eq_fold_zm_phase_resonance_resultant_chebyshev.tex
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _poly_in_y(expr: sp.Expr, y: sp.Symbol) -> sp.Expr:
    return sp.Poly(sp.expand(expr), y, domain=sp.ZZ).as_expr()


def _latex_poly_y(expr: sp.Expr, y: sp.Symbol) -> str:
    return sp.latex(_poly_in_y(expr, y))


def _latex_neg_paren(expr: sp.Expr, y: sp.Symbol) -> str:
    e = _poly_in_y(expr, y)
    if e.could_extract_minus_sign():
        inner = _poly_in_y(-e, y)
        return f"-\\left({sp.latex(inner)}\\right)"
    return sp.latex(e)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Res_lam(Pi(lam,y), Pi(u lam,y)) and Chebyshev compression.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-phase-resonance] start", flush=True)

    lam, y, u, s = sp.symbols("lam y u s")

    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    Pi_u = (u * lam) ** 4 - (u * lam) ** 3 - (2 * y + 1) * (u * lam) ** 2 + (u * lam) + y * (y + 1)

    R = sp.expand(sp.resultant(Pi, Pi_u, lam))
    Rpoly = sp.Poly(R, u, y, domain=sp.ZZ)

    factor = sp.expand(y * (y + 1) * (u - 1) ** 4)
    factor_poly = sp.Poly(factor, u, y, domain=sp.ZZ)
    Fpoly, rem = Rpoly.div(factor_poly)
    if not rem.is_zero:
        raise RuntimeError("R(u,y) not divisible by y(y+1)(u-1)^4 in Z[u,y].")
    F = sp.expand(Fpoly.as_expr())

    deg_u_F = int(sp.Poly(F, u, y, domain=sp.ZZ).degree(u))
    deg_y_F = int(sp.Poly(F, u, y, domain=sp.ZZ).degree(y))
    if deg_u_F != 12:
        raise RuntimeError(f"Unexpected deg_u(F): got {deg_u_F}, expected 12.")
    if deg_y_F != 6:
        raise RuntimeError(f"Unexpected deg_y(F): got {deg_y_F}, expected 6.")

    palindromic_ok = True
    for k in range(deg_u_F + 1):
        a = sp.expand(F.coeff(u, k))
        b = sp.expand(F.coeff(u, deg_u_F - k))
        if sp.expand(a - b) != 0:
            palindromic_ok = False
            break

    a0 = sp.factor(F.coeff(u, 12))
    a1 = sp.factor(F.coeff(u, 11))
    a2 = sp.factor(F.coeff(u, 10))
    c9 = _poly_in_y(F.coeff(u, 9), y)
    c8 = _poly_in_y(F.coeff(u, 8), y)
    c7 = _poly_in_y(F.coeff(u, 7), y)
    c6 = _poly_in_y(F.coeff(u, 6), y)

    a0_expected = y**3 * (y + 1) ** 3
    a1_expected = y**2 * (y + 1) ** 2 * (2 * y + 1) ** 2
    a2_expected = y * (y + 1) * (2 * y**2 - 1) * (y**2 + y + 1)
    c9_expected = -(12 * y**6 + 50 * y**5 + 63 * y**4 + 38 * y**3 + 19 * y**2 + 6 * y + 1)
    c8_expected = -(17 * y**6 + 87 * y**5 + 96 * y**4 + 33 * y**3 + 16 * y**2 + 7 * y + 2)
    c7_expected = 8 * y**6 - 26 * y**5 + 11 * y**4 + 94 * y**3 + 51 * y**2 + 14 * y + 1
    c6_expected = 28 * y**6 + 32 * y**5 + 103 * y**4 + 186 * y**3 + 103 * y**2 + 32 * y + 4

    coeffs_ok = bool(
        sp.expand(a0 - a0_expected) == 0
        and sp.expand(a1 - a1_expected) == 0
        and sp.expand(a2 - a2_expected) == 0
        and sp.expand(c9 - c9_expected) == 0
        and sp.expand(c8 - c8_expected) == 0
        and sp.expand(c7 - c7_expected) == 0
        and sp.expand(c6 - c6_expected) == 0
    )
    if not coeffs_ok:
        raise RuntimeError("Extracted palindromic coefficients do not match the claimed closed forms.")

    F_sym = sp.expand(
        a0_expected * (u**12 + 1)
        + a1_expected * (u**11 + u)
        + a2_expected * (u**10 + u**2)
        + c9_expected * (u**9 + u**3)
        + c8_expected * (u**8 + u**4)
        + c7_expected * (u**7 + u**5)
        + c6_expected * u**6
    )
    if sp.expand(F - F_sym) != 0:
        raise RuntimeError("F(u,y) does not match the symmetric-basis reconstruction.")

    # u^k + u^{-k} in terms of s = u + u^{-1}.
    C1 = s
    C2 = s**2 - 2
    C3 = s**3 - 3 * s
    C4 = s**4 - 4 * s**2 + 2
    C5 = s**5 - 5 * s**3 + 5 * s
    C6 = s**6 - 6 * s**4 + 9 * s**2 - 2
    G = sp.expand(
        a0_expected * C6 + a1_expected * C5 + a2_expected * C4 + c9_expected * C3 + c8_expected * C2 + c7_expected * C1 + c6_expected
    )

    g6 = _poly_in_y(G.coeff(s, 6), y)
    g5 = _poly_in_y(G.coeff(s, 5), y)
    g4 = _poly_in_y(G.coeff(s, 4), y)
    g3 = _poly_in_y(G.coeff(s, 3), y)
    g2 = _poly_in_y(G.coeff(s, 2), y)
    g1 = _poly_in_y(G.coeff(s, 1), y)
    g0 = _poly_in_y(G.coeff(s, 0), y)

    g6_expected = y**6 + 3 * y**5 + 3 * y**4 + y**3
    g5_expected = 4 * y**6 + 12 * y**5 + 13 * y**4 + 6 * y**3 + y**2
    g4_expected = -(4 * y**6 + 14 * y**5 + 15 * y**4 + 6 * y**3 + 2 * y**2 + y)
    g3_expected = -(32 * y**6 + 110 * y**5 + 128 * y**4 + 68 * y**3 + 24 * y**2 + 6 * y + 1)
    g2_expected = -(16 * y**6 + 76 * y**5 + 81 * y**4 + 24 * y**3 + 8 * y**2 + 3 * y + 2)
    g1_expected = 64 * y**6 + 184 * y**5 + 265 * y**4 + 238 * y**3 + 113 * y**2 + 32 * y + 4
    g0_expected = 64 * y**6 + 208 * y**5 + 295 * y**4 + 250 * y**3 + 131 * y**2 + 44 * y + 8

    G_coeffs_ok = bool(
        sp.expand(g6 - g6_expected) == 0
        and sp.expand(g5 - g5_expected) == 0
        and sp.expand(g4 - g4_expected) == 0
        and sp.expand(g3 - g3_expected) == 0
        and sp.expand(g2 - g2_expected) == 0
        and sp.expand(g1 - g1_expected) == 0
        and sp.expand(g0 - g0_expected) == 0
    )
    if not G_coeffs_ok:
        raise RuntimeError("Expanded coefficients of G(s,y) do not match the claimed formulas.")

    # Verify F(u,y) = u^6 G(u+u^{-1},y) (as an identity in Z[u,u^{-1},y]).
    F_from_G = sp.expand(u**6 * sp.expand(G.subs(s, u + 1 / u)))
    diff = sp.together(F_from_G - F_sym)
    num = sp.expand(diff.as_numer_denom()[0])
    chebyshev_ok = bool(sp.Poly(num, u, y, domain=sp.ZZ).is_zero)

    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    G2 = sp.factor(sp.expand(G.subs(s, 2)))
    degeneracy_ok = bool(sp.factor(G2 + y * (y - 1) * P_LY) == 0)

    payload: Dict[str, object] = {
        "deg_u_F": deg_u_F,
        "deg_y_F": deg_y_F,
        "palindromic_ok": palindromic_ok,
        "coeffs_ok": coeffs_ok,
        "G_coeffs_ok": G_coeffs_ok,
        "chebyshev_ok": chebyshev_ok,
        "degeneracy_ok": degeneracy_ok,
        "elapsed_s": float(time.time() - t0),
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zm_phase_resonance_resultant_chebyshev_audit.json"
        out_tex = generated_dir() / "eq_fold_zm_phase_resonance_resultant_chebyshev.tex"

        tex = []
        tex.append("% Auto-generated by scripts/exp_fold_zm_phase_resonance_resultant_chebyshev_audit.py")
        tex.append(r"\[")
        tex.append(
            r"\Pi(\lambda,y)=\lambda^{4}-\lambda^{3}-(2y+1)\lambda^{2}+\lambda+y(y+1),\qquad "
            r"\mathcal{R}(u,y):=\operatorname{Res}_{\lambda}\bigl(\Pi(\lambda,y),\Pi(u\lambda,y)\bigr)."
        )
        tex.append(r"\]")
        tex.append(r"\[")
        tex.append(r"\mathcal{R}(u,y)=y(y+1)(u-1)^{4}\,F(u,y).")
        tex.append(r"\]")

        tex.append(r"\[")
        tex.append(r"\begin{aligned}")
        tex.append(r"F(u,y)=&\ " + sp.latex(sp.factor(a0_expected)) + r"(u^{12}+1)")
        tex.append(r"+\ " + sp.latex(sp.factor(a1_expected)) + r"(u^{11}+u)")
        tex.append(r"+\ " + sp.latex(sp.factor(a2_expected)) + r"(u^{10}+u^{2})\\")
        tex.append(r"&-\ \left(" + _latex_poly_y(-c9_expected, y) + r"\right)(u^{9}+u^{3})")
        tex.append(r"-\ \left(" + _latex_poly_y(-c8_expected, y) + r"\right)(u^{8}+u^{4})\\")
        tex.append(r"&+\ \left(" + _latex_poly_y(c7_expected, y) + r"\right)(u^{7}+u^{5})")
        tex.append(r"+\ \left(" + _latex_poly_y(c6_expected, y) + r"\right)u^{6}.")
        tex.append(r"\end{aligned}")
        tex.append(r"\]")

        tex.append(r"\[")
        tex.append(r"F(u,y)=u^{6}G(s,y),\qquad s:=u+u^{-1}.")
        tex.append(r"\]")

        tex.append(r"\[")
        tex.append(r"\begin{aligned}")
        tex.append(r"G(s,y)=&\ \left(" + _latex_poly_y(g6_expected, y) + r"\right)s^{6}")
        tex.append(r"+\left(" + _latex_poly_y(g5_expected, y) + r"\right)s^{5}\\")
        tex.append(r"&+\left(" + _latex_poly_y(g4_expected, y) + r"\right)s^{4}")
        tex.append(r"+\left(" + _latex_poly_y(g3_expected, y) + r"\right)s^{3}\\")
        tex.append(r"&+\left(" + _latex_poly_y(g2_expected, y) + r"\right)s^{2}")
        tex.append(r"+\left(" + _latex_poly_y(g1_expected, y) + r"\right)s\\")
        tex.append(r"&+\left(" + _latex_poly_y(g0_expected, y) + r"\right).")
        tex.append(r"\end{aligned}")
        tex.append(r"\]")

        tex.append(r"\[")
        tex.append(r"G(2,y)=-y(y-1)\bigl(256y^{3}+411y^{2}+165y+32\bigr).")
        tex.append(r"\]")

        _write_json(out_json, payload)
        _write_text(out_tex, "\n".join(tex) + "\n")

    print("[fold-zm-phase-resonance] ok", flush=True)


if __name__ == "__main__":
    main()

