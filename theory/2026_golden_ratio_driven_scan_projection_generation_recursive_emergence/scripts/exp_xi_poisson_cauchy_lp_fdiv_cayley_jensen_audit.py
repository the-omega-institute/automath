#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit explicit constants for Poisson--Cauchy L^p/KL/f-div asymptotics
and the Cayley--Poisson / Jensen-footprint bridge formulas.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import paper_root, scripts_dir


def _to_fraction_string(x: sp.Expr) -> str:
    return str(sp.together(sp.simplify(x)))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit Poisson--Cauchy L^p constants, KL/f-div coefficients, and Cayley--Poisson identities."
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(
            paper_root() / "artifacts" / "export" / "xi_poisson_cauchy_lp_fdiv_cayley_jensen_audit.json"
        ),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    print("[progress] stage=init", flush=True)
    y = sp.symbols("y", real=True)
    gamma, delta, x0 = sp.symbols("gamma delta x0", real=True, positive=True)
    a = sp.symbols("a", real=True, positive=True)

    # 1) L^p sharp profile constants (R, u2, u3, u4)
    print("[progress] stage=lp-profile-constants", flush=True)
    R = (sp.Integer(1) / sp.pi) * (3 * y**2 - 1) / (1 + y**2) ** 3
    G = (sp.Integer(1) / sp.pi) * sp.Integer(1) / (1 + y**2)
    u2 = (3 * y**2 - 1) / (1 + y**2) ** 2
    u3 = 4 * y * (y**2 - 1) / (1 + y**2) ** 3
    u4 = (5 * y**4 - 10 * y**2 + 1) / (1 + y**2) ** 4

    R_l2_sq = sp.simplify(sp.integrate(sp.expand(R**2), (y, -sp.oo, sp.oo)))
    R_l2 = sp.simplify(sp.sqrt(R_l2_sq))
    # |R|_inf: verified by stationary points of numerator-weighted profile and endpoint limits.
    profile = sp.simplify(sp.Abs(3 * y**2 - 1) / (1 + y**2) ** 3)
    profile_candidates = [sp.Integer(0), sp.Integer(1), sp.sqrt(sp.Rational(1, 3))]
    profile_vals = [sp.simplify(profile.subs(y, c)) for c in profile_candidates]
    R_linf = sp.simplify((sp.Integer(1) / sp.pi) * max(profile_vals, key=lambda v: float(v.evalf())))

    I_u2_sq = sp.simplify(sp.integrate(sp.expand(G * u2**2), (y, -sp.oo, sp.oo)))
    I_u3_sq = sp.simplify(sp.integrate(sp.expand(G * u3**2), (y, -sp.oo, sp.oo)))
    I_u2u4 = sp.simplify(sp.integrate(sp.expand(G * u2 * u4), (y, -sp.oo, sp.oo)))
    I_u2_cu = sp.simplify(sp.integrate(sp.expand(G * u2**3), (y, -sp.oo, sp.oo)))

    # 2) Cayley--Poisson identity and two-sided bounds
    print("[progress] stage=cayley-poisson-identity", flush=True)
    w2 = (gamma**2 + (delta - 1) ** 2) / (gamma**2 + (delta + 1) ** 2)
    minus_log_abs_w = sp.simplify(sp.Rational(1, 2) * sp.log((gamma**2 + (delta + 1) ** 2) / (gamma**2 + (delta - 1) ** 2)))
    scale_integral = sp.simplify(
        sp.integrate(a / (gamma**2 + a**2), (a, delta - 1, delta + 1))
    )
    cauchy_kernel_a = (sp.Integer(1) / sp.pi) * a / (gamma**2 + a**2)
    scale_integral_poisson = sp.simplify(sp.pi * sp.integrate(cauchy_kernel_a, (a, delta - 1, delta + 1)))

    lower_bound = sp.simplify(2 * delta / (gamma**2 + (delta + 1) ** 2))
    upper_bound = sp.simplify(2 * delta / (gamma**2 + (delta - 1) ** 2))

    # Numerical witness grid for inequality (symbolic inequality follows from log(1+u) bounds).
    numeric_checks: List[Dict[str, float]] = []
    for g0 in [0.0, 0.5, 2.0]:
        for d0 in [0.2, 0.8, 1.0, 2.5]:
            denom = g0**2 + (d0 - 1.0) ** 2
            if denom <= 1e-15:
                continue
            lhs_val = 0.5 * math.log((g0**2 + (d0 + 1.0) ** 2) / (g0**2 + (d0 - 1.0) ** 2))
            lb_val = 2.0 * d0 / (g0**2 + (d0 + 1.0) ** 2)
            ub_val = 2.0 * d0 / (g0**2 + (d0 - 1.0) ** 2)
            numeric_checks.append(
                {
                    "gamma": g0,
                    "delta": d0,
                    "lower": lb_val,
                    "value": lhs_val,
                    "upper": ub_val,
                }
            )

    # 3) Jensen footprint algebraic bridge
    print("[progress] stage=jensen-footprint-bridge", flush=True)
    gx = gamma - x0
    cayley_mod_sq_shift = sp.simplify((gx**2 + (delta - 1) ** 2) / (gx**2 + (delta + 1) ** 2))
    minus_log_abs_w_shift = sp.simplify(
        sp.Rational(1, 2) * sp.log((gx**2 + (delta + 1) ** 2) / (gx**2 + (delta - 1) ** 2))
    )
    poisson_1plusd = sp.simplify((sp.Integer(1) / sp.pi) * (delta + 1) / (gx**2 + (delta + 1) ** 2))
    jensen_poisson_cert = sp.simplify(2 * sp.pi * (delta / (1 + delta)) * poisson_1plusd)
    jensen_poisson_cert_closed = sp.simplify(2 * delta / (gx**2 + (delta + 1) ** 2))

    out = {
        "lp_profile": {
            "R_expr": str(sp.simplify(R)),
            "R_l2_squared": _to_fraction_string(R_l2_sq),
            "R_l2": _to_fraction_string(R_l2),
            "R_linf": _to_fraction_string(R_linf),
            "profile_candidates": [str(c) for c in profile_candidates],
            "profile_values": [_to_fraction_string(v) for v in profile_vals],
            "integrals": {
                "int_G_u2_sq": _to_fraction_string(I_u2_sq),
                "int_G_u3_sq": _to_fraction_string(I_u3_sq),
                "int_G_u2u4": _to_fraction_string(I_u2u4),
                "int_G_u2_cubed": _to_fraction_string(I_u2_cu),
            },
        },
        "cayley_poisson_identity": {
            "w_squared": str(sp.simplify(w2)),
            "minus_log_abs_w": str(minus_log_abs_w),
            "scale_integral_closed": str(scale_integral),
            "scale_integral_poisson_form": str(scale_integral_poisson),
            "lower_bound": str(lower_bound),
            "upper_bound": str(upper_bound),
            "numeric_inequality_witness": numeric_checks,
        },
        "jensen_poisson_bridge": {
            "shifted_w_squared": str(cayley_mod_sq_shift),
            "minus_log_abs_w_shifted": str(minus_log_abs_w_shift),
            "poisson_certificate_expr": str(jensen_poisson_cert),
            "poisson_certificate_closed": str(jensen_poisson_cert_closed),
        },
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    print("[progress] stage=write-json", flush=True)
    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")

    print("[progress] stage=assertions", flush=True)
    assert sp.simplify(R_l2_sq - sp.Rational(3, 16) / sp.pi) == 0, "R L2^2 constant mismatch"
    assert sp.simplify(R_l2 - sp.sqrt(3) / (4 * sp.sqrt(sp.pi))) == 0, "R L2 constant mismatch"
    assert sp.simplify(R_linf - sp.Integer(1) / sp.pi) == 0, "R Linf constant mismatch"
    assert sp.simplify(I_u2_sq - sp.Rational(1, 4)) == 0, "Integral int G u2^2 mismatch"
    assert sp.simplify(I_u3_sq - sp.Rational(3, 16)) == 0, "Integral int G u3^2 mismatch"
    assert sp.simplify(I_u2u4 + sp.Rational(1, 8)) == 0, "Integral int G u2u4 mismatch"
    assert sp.simplify(I_u2_cu + sp.Rational(3, 32)) == 0, "Integral int G u2^3 mismatch"
    assert sp.simplify(minus_log_abs_w - scale_integral) == 0, "Cayley scale integral identity mismatch"
    assert sp.simplify(scale_integral - scale_integral_poisson) == 0, "Poisson-scale identity mismatch"
    assert sp.simplify(jensen_poisson_cert - jensen_poisson_cert_closed) == 0, "Jensen Poisson certificate mismatch"
    for row in numeric_checks:
        assert row["lower"] <= row["value"] + 1e-12, "Lower inequality witness failed"
        assert row["value"] <= row["upper"] + 1e-12, "Upper inequality witness failed"

    print("[progress] stage=done", flush=True)


if __name__ == "__main__":
    main()

