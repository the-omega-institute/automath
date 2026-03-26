#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Arithmetic audit for the RH quintic and Lee--Yang cubic fields.

This script certifies the field-theoretic data used in the manuscript:

1. The RH-threshold quintic
       u^5 + 4u^4 + 3u^3 - 96u^2 - 42u - 14
   is irreducible over Q, and remains irreducible modulo 11.

2. The Lee--Yang cubic for u = kappa_*^2
       324u^3 - 540u^2 + 333u - 74
   and the amplitude cubic for b = B^2
       162b^3 + 1593b^2 + 1998b + 1184
   are both irreducible over Q.

3. Consequently,
       [Q(u_R):Q] = 5,
       [Q(u_LY):Q] = [Q(b):Q] = 3,
   the intersection degree is 1, and the compositum degree is 15.

Outputs:
  - artifacts/export/arity_pure_collision_cubic_field_decoupling_audit.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

import sympy as sp

from common_paths import export_dir


def _factor_data(poly: sp.Poly) -> List[Dict[str, Any]]:
    coeff, factors = poly.factor_list()
    data: List[Dict[str, Any]] = []
    for factor, exponent in factors:
        data.append(
            {
                "factor": sp.sstr(factor.as_expr()),
                "degree": int(factor.degree()),
                "exponent": int(exponent),
            }
        )
    return data


def _mod_factor_data(poly: sp.Poly, modulus: int) -> Dict[str, Any]:
    symbol = poly.gens[0]
    mod_poly = sp.Poly(poly.as_expr(), symbol, modulus=modulus)
    coeff, factors = mod_poly.factor_list()
    return {
        "modulus": int(modulus),
        "factorization": sp.sstr(sp.factor(poly.as_expr(), modulus=modulus)),
        "factors": [
            {
                "factor": sp.sstr(factor.as_expr()),
                "degree": int(factor.degree()),
                "exponent": int(exponent),
            }
            for factor, exponent in factors
        ],
        "irreducible": bool(
            len(factors) == 1
            and int(factors[0][0].degree()) == int(poly.degree())
            and int(factors[0][1]) == 1
        ),
    }


def _positive_real_roots(poly: sp.Poly, digits: int) -> List[str]:
    roots = poly.nroots(n=digits, maxsteps=200)
    values: List[str] = []
    for root in roots:
        real_part = sp.re(root).evalf(digits)
        imag_part = sp.im(root).evalf(digits)
        if abs(float(imag_part)) < 1e-20 and float(real_part) > 0:
            values.append(str(real_part))
    return values


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit arithmetic decoupling between the RH quintic and Lee--Yang cubic fields.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_cubic_field_decoupling_audit.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--digits",
        type=int,
        default=80,
        help="Working precision for approximate positive roots.",
    )
    args = parser.parse_args()

    u = sp.Symbol("u")
    b = sp.Symbol("b")

    rh_quintic = sp.Poly(u**5 + 4 * u**4 + 3 * u**3 - 96 * u**2 - 42 * u - 14, u, domain="ZZ")
    leyang_cubic = sp.Poly(324 * u**3 - 540 * u**2 + 333 * u - 74, u, domain="ZZ")
    amplitude_cubic = sp.Poly(162 * b**3 + 1593 * b**2 + 1998 * b + 1184, b, domain="ZZ")

    rh_mod_11 = _mod_factor_data(rh_quintic, modulus=11)
    if not rh_mod_11["irreducible"]:
        raise RuntimeError("Expected the RH quintic to remain irreducible modulo 11.")

    if not rh_quintic.is_irreducible:
        raise RuntimeError("Expected the RH quintic to be irreducible over Q.")
    if not leyang_cubic.is_irreducible:
        raise RuntimeError("Expected the Lee--Yang cubic to be irreducible over Q.")
    if not amplitude_cubic.is_irreducible:
        raise RuntimeError("Expected the amplitude cubic to be irreducible over Q.")

    degree_rh = int(rh_quintic.degree())
    degree_leyang = int(leyang_cubic.degree())
    degree_b = int(amplitude_cubic.degree())
    intersection_degree = 1
    compositum_degree = degree_rh * degree_leyang

    payload: Dict[str, Any] = {
        "rh_threshold_quintic": {
            "polynomial": sp.sstr(rh_quintic.as_expr()),
            "degree": degree_rh,
            "irreducible_over_Q": bool(rh_quintic.is_irreducible),
            "factorization_over_Q": _factor_data(rh_quintic),
            "mod_11": rh_mod_11,
            "positive_real_roots": _positive_real_roots(rh_quintic, digits=max(50, int(args.digits))),
        },
        "leyang_kappa_square_cubic": {
            "polynomial": sp.sstr(leyang_cubic.as_expr()),
            "degree": degree_leyang,
            "irreducible_over_Q": bool(leyang_cubic.is_irreducible),
            "factorization_over_Q": _factor_data(leyang_cubic),
        },
        "leyang_amplitude_square_cubic": {
            "polynomial": sp.sstr(amplitude_cubic.as_expr()),
            "degree": degree_b,
            "irreducible_over_Q": bool(amplitude_cubic.is_irreducible),
            "factorization_over_Q": _factor_data(amplitude_cubic),
        },
        "field_degree_certificate": {
            "Q_uR_degree": degree_rh,
            "Q_uLY_degree": degree_leyang,
            "Q_b_degree": degree_b,
            "coprime_degree_gcd": int(sp.gcd(degree_rh, degree_leyang)),
            "intersection_degree": intersection_degree,
            "compositum_degree_Q_uR_uLY": compositum_degree,
            "compositum_degree_Q_uR_b": compositum_degree,
            "reason": "Because the degrees 5 and 3 are coprime, the intersection degree divides both and is therefore 1.",
        },
    }

    out_path = Path(args.json_out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
