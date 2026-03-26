#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Algebraic certificate for the t-model of E_D and a point-count witness.

Outputs:
  - artifacts/export/xi_xh_ed_t_model_and_pointcount_certificate.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir


def _count_points_short_weierstrass_mod_p(a: int, b: int, p: int) -> int:
    # y^2 = x^3 + a x + b over F_p, with point at infinity.
    n = 1
    for x in range(p):
        rhs = (x * x * x + a * x + b) % p
        for y in range(p):
            if (y * y - rhs) % p == 0:
                n += 1
    return n


def _count_points_ed_t_model_mod_p(p: int) -> int:
    # W^2 = 31 T^3 - 13 T^2 - 3 T + 1 over F_p.
    n = 1
    for T in range(p):
        rhs = (31 * T**3 - 13 * T**2 - 3 * T + 1) % p
        for W in range(p):
            if (W * W - rhs) % p == 0:
                n += 1
    return n


def _ed_t_model_certificate() -> Dict[str, object]:
    m, u, t = sp.symbols("m u t")
    f = -4 * m**3 - 16 * m**2 + 16 * m + 65

    # t = (u-1)/(u-8m-33)
    u_expr = sp.solve(sp.Eq(t * (u - 8 * m - 33), u - 1), u)[0]
    expr = sp.expand(u_expr**2 - f)
    num, den = sp.together(expr).as_numer_denom()

    num_fac = sp.factor(num)
    den_fac = sp.factor(den)

    quad = sp.factor((t - 1) ** 2 * m**2 + 16 * t**2 * m + 64 * t**2 + 4 * t - 4)
    # Verify the factorization shape: num = 4*(m+4)*quad
    factor_ok = sp.simplify(num_fac - 4 * (m + 4) * quad) == 0

    a = (t - 1) ** 2
    b = 16 * t**2
    c = 64 * t**2 + 4 * t - 4
    disc = sp.factor(b**2 - 4 * a * c)
    disc_target = sp.factor(16 * (31 * t**3 - 13 * t**2 - 3 * t + 1))
    disc_ok = sp.simplify(disc - disc_target) == 0

    # Primitive generator W = ( (t-1)^2 m + 8 t^2 ) / 2
    W = sp.Symbol("W")
    W_def = ((t - 1) ** 2 * m + 8 * t**2) / 2
    W_relation = sp.factor((2 * a * m + b) ** 2 / 16)
    # W_relation should equal 31 t^3 - 13 t^2 - 3 t + 1
    W_relation_ok = sp.simplify(W_relation - (31 * t**3 - 13 * t**2 - 3 * t + 1)) == 0

    # Recover m, u in Q(t,W) (symbolic form).
    m_recon = sp.simplify((2 * W - 8 * t**2) / (t - 1) ** 2)
    u_recon = sp.simplify((8 * m_recon * t + 33 * t - 1) / (t - 1))

    return {
        "ed_model": {"u^2": str(sp.factor(f))},
        "t_definition": "t = (u-1)/(u-8m-33)",
        "u_solved_from_t": str(u_expr),
        "denominator_after_substitution": str(den_fac),
        "numerator_factorization": str(num_fac),
        "quadratic_relation_in_m": str(quad),
        "factorization_ok": bool(factor_ok),
        "discriminant": str(disc),
        "discriminant_target": str(disc_target),
        "discriminant_ok": bool(disc_ok),
        "W_definition": str(W_def),
        "W_relation": str(W_relation),
        "W_relation_ok": bool(W_relation_ok),
        "m_reconstruction_in_Q(t,W)": str(m_recon),
        "u_reconstruction_in_Q(t,W)": str(u_recon),
    }


def _pointcount_witness(p: int) -> Dict[str, object]:
    if p in (2,):
        raise ValueError("p must be an odd prime for these models.")

    # E: Y^2 = X^3 - X + 1/4. Over F_p this is Y^2 = X^3 - X + inv4.
    inv4 = pow(4, -1, p)
    nE = _count_points_short_weierstrass_mod_p(a=-1, b=inv4, p=p)
    nD = _count_points_ed_t_model_mod_p(p=p)
    aE = p + 1 - nE
    aD = p + 1 - nD
    return {
        "p": p,
        "inv4_mod_p": inv4,
        "E_count_Fp": nE,
        "EDt_count_Fp": nD,
        "a_p_E": aE,
        "a_p_EDt": aD,
        "witness_ap_inequality": bool(aE != aD),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate algebraic certificate for E_D t-model and a point-count witness."
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_xh_ed_t_model_and_pointcount_certificate.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--prime",
        type=int,
        default=7,
        help="Odd prime for the point-count witness (default: 7).",
    )
    args = parser.parse_args()

    payload: Dict[str, object] = {
        "ed_t_model_certificate": _ed_t_model_certificate(),
        "pointcount_witness": _pointcount_witness(args.prime),
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-xh-ed-t-model] wrote {jout}", flush=True)


if __name__ == "__main__":
    main()

