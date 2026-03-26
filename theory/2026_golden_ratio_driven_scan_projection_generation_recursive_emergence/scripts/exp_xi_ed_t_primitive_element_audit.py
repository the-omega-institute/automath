#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Primitive element t for Q(E_D)/Q(y): resultants, norm, cubic, discriminant.

English-only by repository convention.

We work on the elliptic curve
  E_D: u^2 = -4 m^3 - 16 m^2 + 16 m + 65
and the degree-3 map
  y = (u - (4 m^2 - 17)) / (2 (m-2)(m+2)^2).

We also use the plane model F(m,y)=0 with
  F(m,y) = (m-2)(m+2)^2 y^2 + (4 m^2 - 17) y + (4 m - 7)
and the lift
  U(m,y) = 2 (m-2)(m+2)^2 y + (4 m^2 - 17)
so that u = U(m,y) on E_D.

Define
  t = (U-1)/(U-8 m - 33) in Q(E_D).

This script verifies:
  - Res_m(U-1, F) = 8 y^3 (24 y - 23)
  - Res_m(U-8m-33, F) = 8 y^3 (8 y - 3)^2 (24 y - 23)
  - Norm_{Q(E_D)/Q(y)}(t) = 1/(8 y - 3)^2
  - Elimination in m gives the cubic:
      (8y-3)^2 t^3 - (32y+19) t^2 + (16y+11) t - 1 = 0
    up to removable degeneracy factors.
  - Disc_t(cubic) = 2^12 * Delta(y), with Delta(y)=-y(y-1)g(y),
    g(y)=256 y^3 + 411 y^2 + 165 y + 32.

Outputs:
  - artifacts/export/xi_ed_t_primitive_element_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    ok_res_u_minus_1: bool
    ok_res_u_minus_8m_33: bool
    ok_norm: bool
    ok_cubic_factor_present: bool
    ok_disc: bool
    res_u_minus_1_factored: str
    res_u_minus_8m_33_factored: str
    norm_simplified: str
    cubic_found: str
    disc_cubic_factored: str
    disc_target_factored: str


def _factor_str(expr: sp.Expr) -> str:
    return sp.sstr(sp.factor(expr))


def main() -> None:
    m, y, t = sp.symbols("m y t")

    A = (m - 2) * (m + 2) ** 2
    B = 4 * m**2 - 17
    F = sp.expand(A * y**2 + B * y + (4 * m - 7))
    U = sp.expand(2 * A * y + B)

    # Resultants in m.
    res1 = sp.factor(sp.resultant(U - 1, F, m))
    res2 = sp.factor(sp.resultant(U - 8 * m - 33, F, m))

    target1 = sp.factor(8 * y**3 * (24 * y - 23))
    target2 = sp.factor(8 * y**3 * (8 * y - 3) ** 2 * (24 * y - 23))

    ok_res1 = sp.simplify(res1 - target1) == 0
    ok_res2 = sp.simplify(res2 - target2) == 0

    norm = sp.factor(sp.together(res1 / res2))
    ok_norm = sp.simplify(norm - 1 / (8 * y - 3) ** 2) == 0

    # Eliminate m from {F=0, (U-1) - t (U-8m-33)=0}.
    eq_lin = sp.expand((U - 1) - t * (U - 8 * m - 33))
    elim = sp.factor(sp.resultant(eq_lin, F, m))

    # Expected cubic.
    cubic = sp.Poly((8 * y - 3) ** 2 * t**3 - (32 * y + 19) * t**2 + (16 * y + 11) * t - 1, t, y)

    # Look for a factor matching the expected cubic up to a nonzero factor in QQ[y].
    ok_cubic = False
    cubic_found = sp.Integer(0)
    for fac, _exp in sp.factor_list(elim)[1]:
        p = sp.Poly(fac, t, y, domain=sp.QQ)
        if p.degree(t) != 3:
            continue
        # Normalize in t to compare in QQ(y)[t].
        p_monic = sp.Poly(sp.together(p.as_expr() / p.LC()), t, y, domain=sp.QQ)
        c_monic = sp.Poly(sp.together(cubic.as_expr() / cubic.LC()), t, y, domain=sp.QQ)
        if sp.simplify(p_monic.as_expr() - c_monic.as_expr()) == 0:
            ok_cubic = True
            cubic_found = fac
            break

    disc_cubic = sp.factor(sp.discriminant(cubic.as_expr(), t))
    g = 256 * y**3 + 411 * y**2 + 165 * y + 32
    Delta = -y * (y - 1) * g
    disc_target = sp.factor(2**12 * Delta)
    ok_disc = sp.simplify(disc_cubic - disc_target) == 0

    payload = Payload(
        ok_res_u_minus_1=bool(ok_res1),
        ok_res_u_minus_8m_33=bool(ok_res2),
        ok_norm=bool(ok_norm),
        ok_cubic_factor_present=bool(ok_cubic),
        ok_disc=bool(ok_disc),
        res_u_minus_1_factored=_factor_str(res1),
        res_u_minus_8m_33_factored=_factor_str(res2),
        norm_simplified=_factor_str(norm),
        cubic_found=_factor_str(cubic_found) if ok_cubic else "",
        disc_cubic_factored=_factor_str(disc_cubic),
        disc_target_factored=_factor_str(disc_target),
    )

    _write_json(export_dir() / "xi_ed_t_primitive_element_audit.json", asdict(payload))


if __name__ == "__main__":
    main()

