#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Certificates for ordered/unordered root-ratio towers inside the p7 S5 splitting field.

We certify, by explicit integer-coefficient eliminations:
  - The degree-20 minimal polynomial R20^rat(X) for rho = beta/alpha (ordered root ratio),
    where alpha, beta are distinct roots of p7(x).
  - The degree-10 minimal polynomial R10^rat(T) for s = rho + rho^{-1} (unordered pair layer).
  - The square resultant identity Res_X(R20^rat(X), X^2 - T X + 1) = R10^rat(T)^2.
  - Discriminant factorizations and the norm identity N_{Q(s)/Q}(s^2 - 4).

Outputs:
  - artifacts/export/collision_kernel_A4_root_ratio_r20_r10_certificate.json
  - sections/generated/eq_collision_kernel_A4_root_ratio_r20_minpoly.tex
  - sections/generated/eq_collision_kernel_A4_root_ratio_r10_minpoly.tex
  - sections/generated/eq_collision_kernel_A4_root_ratio_resultant_square_identity.tex
  - sections/generated/eq_collision_kernel_A4_root_ratio_r20_discriminant_factorization.tex
  - sections/generated/eq_collision_kernel_A4_root_ratio_r10_discriminant_factorization.tex
  - sections/generated/eq_collision_kernel_A4_root_ratio_norm_s2_minus_4.tex
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _p7(u: sp.Symbol) -> sp.Poly:
    return sp.Poly(u**5 - 2 * u**4 - 7 * u**3 - 2 * u + 2, u, domain=sp.ZZ)


def _primitive_ZZ_poly(P: sp.Poly) -> sp.Poly:
    if P.is_zero:
        raise ValueError("zero polynomial")
    _content, prim = P.primitive()
    prim = sp.Poly(prim.as_expr(), prim.gens[0], domain=sp.ZZ)
    if int(prim.LC()) < 0:
        prim = -prim
    return prim


def _factorint_signed(n: int) -> Tuple[int, Dict[int, int]]:
    """Return (sign, factorint(|n|))."""
    if n == 0:
        raise ValueError("factorint(0) is undefined")
    sign = -1 if n < 0 else 1
    return sign, sp.factorint(abs(int(n)))


def _render_factorization_tex(sign: int, fac: Dict[int, int]) -> str:
    pieces: List[str] = []
    for p in sorted(fac.keys()):
        e = fac[p]
        if e == 1:
            pieces.append(f"{p}")
        else:
            pieces.append(f"{p}^{{{e}}}")
    rhs = r"\cdot ".join(pieces) if pieces else "1"
    return f"-{rhs}" if sign < 0 else rhs


def _poly_from_coeffs(symbol: sp.Symbol, coeffs_hi_to_lo: List[int]) -> sp.Poly:
    deg = len(coeffs_hi_to_lo) - 1
    expr = sum(sp.Integer(c) * symbol ** (deg - i) for i, c in enumerate(coeffs_hi_to_lo))
    return sp.Poly(expr, symbol, domain=sp.ZZ)


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _render_poly_aligned(name: str, var: str, coeffs_hi_to_lo: List[int]) -> str:
    # Compact aligned polynomial renderer (stable across SymPy versions).
    deg = len(coeffs_hi_to_lo) - 1

    def term(c: int, d: int) -> str:
        if c == 0:
            return ""
        sgn = "+" if c > 0 else "-"
        a = abs(c)
        if d == 0:
            body = f"{a}"
        elif d == 1:
            body = var if a == 1 else f"{a}{var}"
        else:
            body = f"{var}^{{{d}}}" if a == 1 else f"{a}{var}^{{{d}}}"
        return f" {sgn} {body}"

    parts: List[str] = []
    lead = coeffs_hi_to_lo[0]
    parts.append(f"{lead}{var}^{{{deg}}}" if deg != 0 else f"{lead}")
    for i, c in enumerate(coeffs_hi_to_lo[1:], start=1):
        parts.append(term(int(c), deg - i))
    poly_tex = "".join(parts).strip()
    return f"{name}({var}):={{}}&{poly_tex}."


def compute_R20_rat() -> Tuple[sp.Poly, sp.Poly]:
    """Return (R20_rat, full_res_prim) where full_res has the diagonal factor."""
    u = sp.Symbol("u")
    X = sp.Symbol("X")
    p = _p7(u)
    res_expr = sp.resultant(p.as_expr(), sp.expand(_p7(u).as_expr().subs(u, X * u)), u)
    res = _primitive_ZZ_poly(sp.Poly(sp.expand(res_expr), X, domain=sp.ZZ))

    diag = sp.Poly((X - 1) ** 5, X, domain=sp.ZZ)
    q, r = sp.div(res, diag, domain=sp.ZZ)
    if r != 0:
        raise ValueError("unexpected remainder dividing by (X-1)^5")
    R20 = _primitive_ZZ_poly(sp.Poly(q, X, domain=sp.ZZ))
    return R20, res


def compute_R10_rat(*, R20: sp.Poly) -> Tuple[sp.Poly, sp.Poly]:
    """Return (R10_rat, resultant_square_poly)."""
    X = sp.Symbol("X")
    T = sp.Symbol("T")
    quad = sp.Poly(X**2 - T * X + 1, X, T, domain=sp.ZZ)
    res_expr = sp.resultant(R20.as_expr(), quad.as_expr(), X)
    res = _primitive_ZZ_poly(sp.Poly(sp.expand(res_expr), T, domain=sp.ZZ))

    # Factor to extract the square root.
    const, factors = sp.factor_list(res.as_expr(), gens=[T])
    const = int(const)
    sq_factor_expr = sp.Integer(1)
    leftover_expr = sp.Integer(1)
    for f_expr, mult in factors:
        if mult == 2:
            sq_factor_expr *= f_expr
        else:
            leftover_expr *= f_expr**mult
    if sp.expand(leftover_expr) != 1:
        raise ValueError("resultant is not a pure square polynomial (up to unit)")

    R10 = _primitive_ZZ_poly(sp.Poly(sp.expand(sq_factor_expr), T, domain=sp.ZZ))
    # Ensure the identity holds exactly after primitive normalization:
    if sp.expand(res.as_expr() - (R10.as_expr() ** 2)) != 0:
        raise ValueError("square resultant identity does not hold exactly")
    return R10, res


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate certificates for p7 ordered/unordered root ratio towers.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_root_ratio_r20_r10_certificate.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    X = sp.Symbol("X")
    T = sp.Symbol("T")

    R20, res_full = compute_R20_rat()
    R10, res_sq = compute_R10_rat(R20=R20)

    # Expected coefficients (high -> low), as used in the manuscript.
    expected_R20 = [
        4,
        12,
        -8,
        -820,
        -6740,
        -25296,
        -83917,
        -230719,
        -467301,
        -730700,
        -849906,
        -730700,
        -467301,
        -230719,
        -83917,
        -25296,
        -6740,
        -820,
        -8,
        12,
        4,
    ]
    expected_R10 = [
        4,
        12,
        -48,
        -928,
        -6536,
        -19232,
        -43837,
        -116079,
        -192065,
        -159175,
        -69682,
    ]

    R20_expected = _poly_from_coeffs(X, expected_R20)
    R10_expected = _poly_from_coeffs(T, expected_R10)

    if R20 != R20_expected:
        raise ValueError("R20^rat does not match expected coefficients")
    if R10 != R10_expected:
        raise ValueError("R10^rat does not match expected coefficients")

    # Reciprocity check for R20.
    if sp.expand(X**20 * R20.as_expr().subs(X, 1 / X) - R20.as_expr()) != 0:
        raise ValueError("R20^rat is not reciprocal")

    # Discriminants and factorizations.
    disc_R20 = int(sp.discriminant(R20.as_expr(), X))
    disc_R10 = int(sp.discriminant(R10.as_expr(), T))
    sign20, fac20 = _factorint_signed(disc_R20)
    sign10, fac10 = _factorint_signed(disc_R10)

    # Norm identity for s^2 - 4 using R10(±2).
    lc10 = int(R10.LC())
    R10_2 = int(R10.eval(2))
    R10_m2 = int(R10.eval(-2))
    norm_s2m4 = (R10_2 * R10_m2) // (lc10 * lc10)
    if (R10_2 * R10_m2) % (lc10 * lc10) != 0:
        raise ValueError("unexpected non-integral norm from evaluation formula")

    # Write TeX certificates.
    gen = generated_dir()

    tex_R20 = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_r20_minpoly}",
        r"\begin{aligned}",
        _render_poly_aligned(r"R_{20}^{\mathrm{rat}}", "X", expected_R20),
        r"\end{aligned}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_r20_minpoly.tex", "\n".join(tex_R20))

    tex_R10 = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_r10_minpoly}",
        r"\begin{aligned}",
        _render_poly_aligned(r"R_{10}^{\mathrm{rat}}", "T", expected_R10),
        r"\end{aligned}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_r10_minpoly.tex", "\n".join(tex_R10))

    tex_res_sq = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_resultant_square_identity}",
        r"\boxed{\;",
        r"\operatorname{Res}_{X}\!\bigl(R_{20}^{\mathrm{rat}}(X),\,X^2-TX+1\bigr)=R_{10}^{\mathrm{rat}}(T)^2\;",
        r"}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_resultant_square_identity.tex", "\n".join(tex_res_sq))

    tex_disc20 = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_r20_discriminant_factorization}",
        r"\boxed{\;",
        rf"\Disc\!\bigl(R_{{20}}^{{\mathrm{{rat}}}}\bigr)={_render_factorization_tex(sign20, fac20)}\;",
        r"}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_r20_discriminant_factorization.tex", "\n".join(tex_disc20))

    tex_disc10 = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_r10_discriminant_factorization}",
        r"\boxed{\;",
        rf"\Disc\!\bigl(R_{{10}}^{{\mathrm{{rat}}}}\bigr)={_render_factorization_tex(sign10, fac10)}\;",
        r"}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_r10_discriminant_factorization.tex", "\n".join(tex_disc10))

    tex_norm = [
        "% Auto-generated by scripts/exp_collision_kernel_A4_root_ratio_r20_r10_certificate.py",
        r"\begin{equation}\label{eq:collision_kernel_A4_root_ratio_norm_s2_minus_4}",
        r"\begin{aligned}",
        rf"R_{{10}}^{{\mathrm{{rat}}}}(2)&={R10_2},\qquad R_{{10}}^{{\mathrm{{rat}}}}(-2)={R10_m2},\\",
        rf"\mathrm N_{{\QQ(s)/\QQ}}(s^2-4)&=\frac{{R_{{10}}^{{\mathrm{{rat}}}}(2)}}{{{lc10}}}\cdot\frac{{R_{{10}}^{{\mathrm{{rat}}}}(-2)}}{{{lc10}}}={norm_s2m4}.",
        r"\end{aligned}",
        r"\end{equation}",
        "",
    ]
    _write_text(gen / "eq_collision_kernel_A4_root_ratio_norm_s2_minus_4.tex", "\n".join(tex_norm))

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
        "polynomials": {
            "p7_x": "x^5 - 2*x^4 - 7*x^3 - 2*x + 2",
            "R20_rat_coeffs_deg20_to_0": expected_R20,
            "R10_rat_coeffs_deg10_to_0": expected_R10,
        },
        "checks": {
            "R20_reciprocal": True,
            "resultant_full_has_factor_(X-1)^5": True,
            "resultant_square_identity_exact": True,
        },
        "discriminants": {
            "Disc_R20_rat": disc_R20,
            "Disc_R20_rat_factorint": {str(k): int(v) for k, v in fac20.items()},
            "Disc_R10_rat": disc_R10,
            "Disc_R10_rat_factorint": {str(k): int(v) for k, v in fac10.items()},
        },
        "norms": {
            "R10_rat_lc": lc10,
            "R10_rat_at_2": R10_2,
            "R10_rat_at_-2": R10_m2,
            "N_Qs_over_Q_of_s2_minus_4": norm_s2m4,
        },
        "raw": {
            "resultant_full_degree": int(res_full.degree()),
            "resultant_square_degree": int(res_sq.degree()),
        },
    }

    _write_json(Path(args.json_out), payload)
    print(f"[A4-root-ratio] wrote {args.json_out}", flush=True)


if __name__ == "__main__":
    main()

