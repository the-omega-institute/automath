#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit interference-prime and local-geometry claims for PLY/Q5/A7/F_delta.

Checks included:
  - resultant factorization Res_y(PLY, Q5),
  - characteristic p common-root patterns for PLY and Q5,
  - intersection primes for D_prim(y)=y(y-1)PLY(y) and Q5(y),
  - local expansions at (T,y)=(5,-10) in F_73 and (0,12) in F_31,
  - resultant factorization Res_y(Q5, A7),
  - explicit special fibers of F_delta(T;y) at y=0,1,-10,12.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import paper_root, scripts_dir


def _factor_mod(poly_expr: sp.Expr, var: sp.Symbol, p: int) -> List[Dict[str, object]]:
    poly = sp.Poly(poly_expr, var, modulus=p)
    _, factors = poly.factor_list()
    out: List[Dict[str, object]] = []
    for f, e in factors:
        out.append({"factor": str(f.as_expr()), "degree": int(f.degree()), "exp": int(e)})
    return out


def _poly_mod(poly_expr: sp.Expr, var: sp.Symbol, p: int) -> sp.Poly:
    return sp.Poly(sp.expand(poly_expr), var, modulus=p)


def _factorint_abs(n: int) -> Dict[int, int]:
    return {int(k): int(v) for k, v in sp.factorint(abs(int(n))).items()}


def _terms_leq_total_degree(poly_expr: sp.Expr, vars_: Tuple[sp.Symbol, ...], p: int, deg: int) -> List[Dict[str, object]]:
    poly = sp.Poly(sp.expand(poly_expr), *vars_, modulus=p)
    out: List[Dict[str, object]] = []
    for mon, coef in poly.terms():
        if sum(mon) <= deg:
            out.append({"monomial": list(mon), "coef": int(coef)})
    out.sort(key=lambda d: (sum(d["monomial"]), d["monomial"]))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit PLY/Q5/A7 interference-prime and local-geometry claims.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(
            paper_root()
            / "artifacts"
            / "export"
            / "xi_leyang_ply_q5_a7_interference_geometry_audit.json"
        ),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    print("[progress] stage=init", flush=True)
    y, T = sp.symbols("y T")
    t, s, s1 = sp.symbols("t s s1")

    PLY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80
    A7 = (
        45056 * y**7
        + 60160 * y**6
        - 11984 * y**5
        - 19765 * y**4
        + 18906 * y**3
        + 14723 * y**2
        + 2216 * y
        + 200
    )
    F_delta = T**4 + (8 * y - 3) * T**3 + (2 * y**2 - 34 * y - 4) * T**2 - y * (y - 1) * PLY

    print("[progress] stage=resultants", flush=True)
    res_ply_q5 = int(sp.resultant(PLY, Q5, y))
    res_q5_a7 = int(sp.resultant(Q5, A7, y))

    print("[progress] stage=mod-factors-ply-q5", flush=True)
    fac_31_ply = _factor_mod(PLY, y, 31)
    fac_31_q5 = _factor_mod(Q5, y, 31)
    fac_73_ply = _factor_mod(PLY, y, 73)
    fac_73_q5 = _factor_mod(Q5, y, 73)

    gcd_31_ply_q5 = _poly_mod(sp.gcd(_poly_mod(PLY, y, 31), _poly_mod(Q5, y, 31)).as_expr(), y, 31).as_expr()
    gcd_73_ply_q5 = _poly_mod(sp.gcd(_poly_mod(PLY, y, 73), _poly_mod(Q5, y, 73)).as_expr(), y, 73).as_expr()

    print("[progress] stage=intersection-primes", flush=True)
    D_prim = sp.expand(y * (y - 1) * PLY)
    dprim_q5_gcd = {}
    for p in [2, 3, 5, 13, 31, 73]:
        dprim_q5_gcd[p] = str(sp.gcd(_poly_mod(D_prim, y, p), _poly_mod(Q5, y, p)).as_expr())

    q5_at_0 = int(Q5.subs(y, 0))
    q5_at_1 = int(Q5.subs(y, 1))

    print("[progress] stage=local-geometry", flush=True)
    F_73_shift = sp.Poly(sp.expand(F_delta.subs({T: t + 5, y: s - 10})), t, s, modulus=73).as_expr()
    F_73_quad_terms = _terms_leq_total_degree(F_73_shift, (t, s), 73, 2)
    Fy = sp.diff(F_delta, y)
    FT = sp.diff(F_delta, T)
    Fy_0m10_mod73 = int(sp.Mod(Fy.subs({T: 0, y: -10}), 73))
    FT_0m10_mod73 = int(sp.Mod(FT.subs({T: 0, y: -10}), 73))

    F_31_shift = sp.expand(F_delta.subs({T: t, y: s + 12}))
    F_31_shift_mod = sp.Poly(F_31_shift, t, s, modulus=31).as_expr()
    F_31_terms_deg4 = _terms_leq_total_degree(F_31_shift_mod, (t, s), 31, 4)
    F_31_shift_s1 = sp.expand(F_31_shift_mod.subs(s, s1 - 2 * t**2))
    F_31_shift_s1_mod = sp.Poly(F_31_shift_s1, t, s1, modulus=31).as_expr()
    F_31_terms_s1_deg4 = _terms_leq_total_degree(F_31_shift_s1_mod, (t, s1), 31, 4)

    print("[progress] stage=special-fibers-and-gcd", flush=True)
    special_fibers = {}
    for p, y0 in [(5, 0), (13, 1), (73, -10), (31, 12)]:
        f_poly = _poly_mod(F_delta.subs(y, y0), T, p)
        _, factors = f_poly.factor_list()
        special_fibers[f"{p}:{y0}"] = {
            "poly": str(f_poly.as_expr()),
            "factors": [{"factor": str(ff.as_expr()), "exp": int(ee)} for ff, ee in factors],
        }

    gcd_q5_a7_mod = {}
    for p in [5, 13, 31, 73]:
        gcd_poly = sp.gcd(_poly_mod(Q5, y, p), _poly_mod(A7, y, p))
        gcd_q5_a7_mod[p] = str(_poly_mod(gcd_poly.as_expr(), y, p).as_expr())

    out = {
        "polynomials": {
            "PLY": str(sp.expand(PLY)),
            "Q5": str(sp.expand(Q5)),
            "A7": str(sp.expand(A7)),
            "F_delta": str(sp.expand(F_delta)),
        },
        "resultants": {
            "Res_y_PLY_Q5": int(res_ply_q5),
            "Res_y_PLY_Q5_factorint_abs": _factorint_abs(res_ply_q5),
            "Res_y_Q5_A7": int(res_q5_a7),
            "Res_y_Q5_A7_factorint_abs": _factorint_abs(res_q5_a7),
        },
        "mod_ply_q5_common_root_data": {
            "p31_factors_PLY": fac_31_ply,
            "p31_factors_Q5": fac_31_q5,
            "p31_gcd": str(gcd_31_ply_q5),
            "p73_factors_PLY": fac_73_ply,
            "p73_factors_Q5": fac_73_q5,
            "p73_gcd": str(gcd_73_ply_q5),
        },
        "Dprim_Q5_intersection": {
            "Q5_at_0": int(q5_at_0),
            "Q5_at_1": int(q5_at_1),
            "gcd_mod_primes": dprim_q5_gcd,
        },
        "char73_local_geometry": {
            "quadratic_terms_at_(T-5,y+10)": F_73_quad_terms,
            "F_T_at_(0,-10)_mod73": int(FT_0m10_mod73),
            "F_y_at_(0,-10)_mod73": int(Fy_0m10_mod73),
        },
        "char31_local_geometry": {
            "terms_total_degree_le_4_in_(t,s)": F_31_terms_deg4,
            "terms_total_degree_le_4_after_s1_shift": F_31_terms_s1_deg4,
        },
        "special_fibers": special_fibers,
        "gcd_Q5_A7_mod_p": gcd_q5_a7_mod,
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    print("[progress] stage=write-json", flush=True)
    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("[progress] stage=assertions", flush=True)
    assert _factorint_abs(res_ply_q5) == {2: 20, 3: 12, 31: 4, 73: 1}, "Unexpected factorization for Res_y(PLY,Q5)"
    assert _factorint_abs(res_q5_a7) == {2: 47, 3: 16, 5: 1, 13: 1, 31: 8, 73: 1}, "Unexpected factorization for Res_y(Q5,A7)"
    assert str(gcd_31_ply_q5) == "y**2 + 7*y - 11", "Unexpected gcd mod 31 for (PLY,Q5)"
    assert str(gcd_73_ply_q5) == "y + 10", "Unexpected gcd mod 73 for (PLY,Q5)"
    assert int(Fy_0m10_mod73) != 0, "Expected smoothness witness F_y != 0 at (0,-10) mod 73"
    assert special_fibers["73:-10"]["poly"] == "T**4 - 10*T**3 + 25*T**2", "Unexpected F_delta fiber at (73,-10)"
    assert special_fibers["31:12"]["poly"] == "T**4", "Unexpected F_delta fiber at (31,12)"
    assert special_fibers["5:0"]["poly"] == "T**4 + 2*T**3 + T**2", "Unexpected F_delta fiber at (5,0)"
    assert special_fibers["13:1"]["poly"] == "T**4 + 5*T**3 + 3*T**2", "Unexpected F_delta fiber at (13,1)"

    print("[progress] stage=done", flush=True)


if __name__ == "__main__":
    main()

