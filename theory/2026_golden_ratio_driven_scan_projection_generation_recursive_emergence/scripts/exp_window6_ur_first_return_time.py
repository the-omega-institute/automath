#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: first-return pgf for the window-6 boundary block U_R.

All output is English-only by repository convention.

We use the 4-state coarse kernel T defined by the edge–flux skeleton certificate
(see eq_window6_edge_flux_skeleton.tex). We compute the first-return time pgf:
  F_R(z) = E[z^{tau_R}]
where tau_R is the first return time to state U_R, starting from U_R.

Outputs:
  - artifacts/export/window6_ur_first_return_time.json
  - sections/generated/eq_window6_ur_first_return_time_pgf.tex
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _coarse_kernel_T() -> Tuple[List[str], List[int], List[List[int]], List[List[Fraction]]]:
    """Return (blocks, |U| vector, E undirected edge counts, T coarse Markov kernel)."""
    blocks = ["2", "1", "L", "R"]  # order consistent with eq_window6_edge_flux_skeleton
    U_size: Dict[str, int] = {"2": 27, "1": 22, "L": 9, "R": 6}
    # Undirected edge counts between unions U_alpha, symmetric with diagonal = internal edges.
    E = [
        [28, 63, 23, 20],
        [63, 21, 21, 6],
        [23, 21, 2, 6],
        [20, 6, 6, 2],
    ]
    # Directed edge counts: off-diagonal = E_ij, diagonal = 2*E_ii.
    A: List[List[int]] = [[0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            if i == j:
                A[i][j] = 2 * E[i][j]
            else:
                A[i][j] = E[i][j]
    # Coarse Markov kernel induced by one cube step under uniform within-block prior:
    #   T_ij = A_ij / (6 * |U_i|).
    T: List[List[Fraction]] = []
    for i, bi in enumerate(blocks):
        denom = 6 * U_size[bi]
        T.append([Fraction(A[i][j], denom) for j in range(4)])
    return blocks, [U_size[b] for b in blocks], E, T


def _pgf_first_return_to_R(T: List[List[Fraction]]) -> Tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Return (F(z), numerator(z), denominator(z)) for first return to state index 3."""
    z = sp.Symbol("z")

    # State order is [2,1,L,R], so R is index 3. Others are indices [0,1,2].
    a = sp.Rational(T[3][3].numerator, T[3][3].denominator)
    b = sp.Matrix([sp.Rational(T[3][k].numerator, T[3][k].denominator) for k in (0, 1, 2)]).T
    c = sp.Matrix([sp.Rational(T[k][3].numerator, T[k][3].denominator) for k in (0, 1, 2)])
    Q = sp.Matrix([[sp.Rational(T[i][j].numerator, T[i][j].denominator) for j in (0, 1, 2)] for i in (0, 1, 2)])

    I = sp.eye(3)
    H = z * (I - z * Q).inv() * c  # hitting-time pgf vector from non-R states to R
    F = z * (a + (b * H)[0])  # first-return pgf from R to R
    F = sp.together(sp.simplify(F))
    num, den = sp.fraction(F)
    return F, sp.expand(num), sp.expand(den)


def _clear_denominators(num: sp.Expr, den: sp.Expr) -> Tuple[sp.Expr, sp.Expr]:
    """Scale (num,den) by a common integer to get integer polynomials."""
    z = sp.Symbol("z")
    p_num = sp.Poly(num, z, domain=sp.QQ)
    p_den = sp.Poly(den, z, domain=sp.QQ)
    dens: List[int] = []
    for c in list(p_num.all_coeffs()) + list(p_den.all_coeffs()):
        if isinstance(c, sp.Rational):
            dens.append(int(c.q))
        else:
            dens.append(1)
    lcm = 1
    for d in dens:
        lcm = int(sp.ilcm(lcm, d))
    num_i = sp.expand(num * lcm)
    den_i = sp.expand(den * lcm)
    p_num_i = sp.Poly(num_i, z, domain=sp.ZZ)
    p_den_i = sp.Poly(den_i, z, domain=sp.ZZ)

    # Normalize by gcd of integer coefficients (and fix overall sign).
    g = 0
    for c in list(p_num_i.all_coeffs()) + list(p_den_i.all_coeffs()):
        g = int(sp.igcd(g, int(c)))
    if g > 1:
        num_i = sp.expand(num_i / g)
        den_i = sp.expand(den_i / g)

    # Ensure denominator has a negative constant term (matches existing style).
    den0 = int(sp.Poly(den_i, z, domain=sp.ZZ).eval(0))
    if den0 > 0:
        num_i = -num_i
        den_i = -den_i
    return num_i, den_i


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute first-return pgf for window-6 boundary block U_R.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_ur_first_return_time.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_window6_ur_first_return_time_pgf.tex"),
        help="Output TeX equation path.",
    )
    args = ap.parse_args()

    _, U_sizes, E, T = _coarse_kernel_T()
    F, num, den = _pgf_first_return_to_R(T)
    num_i, den_i = _clear_denominators(num, den)

    z = sp.Symbol("z")
    p_num = sp.Poly(num_i, z, domain=sp.ZZ)
    p_den = sp.Poly(den_i, z, domain=sp.ZZ)

    # Moments from the pgf.
    mean = sp.simplify(sp.diff(F, z).subs(z, 1))
    ex2m1 = sp.simplify(sp.diff(F, z, 2).subs(z, 1))  # E[X(X-1)]
    var = sp.simplify(ex2m1 + mean - mean**2)

    # Radius from the positive real root of the denominator.
    roots = [complex(r) for r in sp.nroots(p_den.as_expr())]
    pos_reals = sorted([r.real for r in roots if abs(r.imag) < 1e-10 and r.real > 0])
    rho = float(pos_reals[0]) if pos_reals else None

    payload = {
        "U_sizes": U_sizes,
        "E_undirected": E,
        "T": [[str(x) for x in row] for row in T],
        "pgf": {
            "F_R_num_int": [int(c) for c in sp.Poly(num_i, z, domain=sp.ZZ).all_coeffs()],
            "F_R_den_int": [int(c) for c in sp.Poly(den_i, z, domain=sp.ZZ).all_coeffs()],
        },
        "moments": {
            "E_tau": str(mean),
            "Var_tau": str(var),
        },
        "radius": {
            "rho_R": rho,
        },
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX snippet: pgf (kept minimal; moments are stated in the paper text).
    tex_out = Path(str(args.tex_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)

    # Pretty-print as z*(cubic)/(cubic) with integer coefficients.
    if p_num.degree() != 4:
        raise AssertionError(f"Unexpected numerator degree: {p_num.degree()}")
    if p_den.degree() != 3:
        raise AssertionError(f"Unexpected denominator degree: {p_den.degree()}")
    num_coeff = [int(c) for c in p_num.all_coeffs()]  # z^4..z^0
    den_coeff = [int(c) for c in p_den.all_coeffs()]  # z^3..z^0
    if num_coeff[-1] != 0:
        raise AssertionError("Expected numerator constant term 0 (divisible by z).")

    a4, a3, a2, a1, _a0 = num_coeff
    if a4 == 0:
        raise AssertionError("Unexpected numerator leading coefficient 0.")
    # numerator = z * (a4 z^3 + a3 z^2 + a2 z + a1)
    num_tex = f"z\\,({a4}z^3{a3:+d}z^2{a2:+d}z{a1:+d})"
    b3, b2, b1, b0 = den_coeff
    den_tex = f"{b3}z^3{b2:+d}z^2{b1:+d}z{b0:+d}"

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_window6_ur_first_return_time.py")
    lines.append("\\begin{equation}\\label{eq:window6_ur_first_return_time_pgf}")
    lines.append(f"F_R(z)=\\frac{{{num_tex}}}{{{den_tex}}}.")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")

    # Sanity checks (hard).
    if str(mean) != "32/3":
        raise AssertionError(f"Unexpected mean: {mean}")
    if str(var) != "1695268/15417":
        raise AssertionError(f"Unexpected variance: {var}")

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}")
    print(f"File: {tex_out.relative_to(generated_dir().parent.parent)}")


if __name__ == "__main__":
    main()

