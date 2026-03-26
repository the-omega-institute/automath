#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the quartic elimination formula for the real-input 40-state zero-temperature prefactor.

This script certifies the elimination step

    b^4 + b^3 - 9 b^2 + 6 b - 1 = 0,
    C = 1 / (2 b (1-b) (6 - 18 b + 3 b^2 + 4 b^3)),

and computes the Sylvester resultant in b to obtain the quartic polynomial
annihilating C_infty.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp

from common_paths import export_dir


def _positive_real_root(poly: sp.Poly, lo: float, hi: float) -> sp.Expr:
    for root in poly.nroots(n=80, maxsteps=300):
        re_part = sp.re(root)
        im_part = sp.im(root)
        if abs(float(im_part)) < 1e-30:
            val = float(re_part)
            if lo < val < hi:
                return sp.N(re_part, 50)
    raise RuntimeError("Failed to locate the positive real root in the requested interval.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit the quartic elimination formula for C_infty in the real-input 40-state kernel."
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(export_dir() / "xi_real_input_40_c_infty_quartic_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    b, C = sp.symbols("b C")
    poly_b = sp.Poly(b**4 + b**3 - 9 * b**2 + 6 * b - 1, b, domain=sp.ZZ)
    relation = sp.Poly(2 * C * b * (1 - b) * (6 - 18 * b + 3 * b**2 + 4 * b**3) - 1, b, C, domain=sp.ZZ)

    resultant_expr = sp.expand(sp.resultant(poly_b.as_expr(), relation.as_expr(), b))
    resultant_poly = sp.Poly(resultant_expr, C, domain=sp.ZZ)

    b_root = _positive_real_root(poly_b, 0.25, 1.0 / 3.0)
    c_value = sp.N(1 / (2 * b_root * (1 - b_root) * (6 - 18 * b_root + 3 * b_root**2 + 4 * b_root**3)), 50)
    residual = sp.N(resultant_poly.as_expr().subs(C, c_value), 50)

    coeffs = [int(x) for x in resultant_poly.all_coeffs()]
    out = {
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
        "b_quartic": str(poly_b.as_expr()),
        "c_relation": "2*C*b*(1 - b)*(6 - 18*b + 3*b**2 + 4*b**3) - 1",
        "resultant_polynomial_in_C": str(resultant_poly.as_expr()),
        "resultant_coefficients_descending": coeffs,
        "positive_root_b": str(b_root),
        "c_infty_value": str(c_value),
        "resultant_at_c_infty": str(residual),
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    expected = [88864, -22216, -275864, -3646, 1]
    assert coeffs == expected, f"Unexpected resultant coefficients: {coeffs}"
    assert abs(float(residual)) < 1e-30, f"Resultant does not vanish at C_infty: {residual}"

    print(f"[xi-real-input-40-c-infty-quartic] wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
