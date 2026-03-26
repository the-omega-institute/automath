#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: p=3 renormalization for the Lee--Yang Perron branch Lambda(t).

This script checks:
- Pi(2+3v, 1+27u) factors as 27*H(u,v) with the stated integer H.
- dH/dv(0,0) = 1.
- Pi(2+3v, 1+9u) factors as 9*H9(u,v) and H9 ≡ u (mod 3).
- H(u,v) ≡ u + v^3 - v^2 + v (mod 3).
- Computes a short truncation of v(u) solving H(u,v)=0 to verify consistency.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def _paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _export_path() -> Path:
    return _paper_root() / "artifacts" / "export" / "fold_zm_leyang_perron_p3_renormalization_audit.json"


def _pi(lam: sp.Expr, y: sp.Expr) -> sp.Expr:
    return lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)


def _poly_mod(p: sp.Expr, *gens: sp.Symbol, modulus: int) -> sp.Poly:
    return sp.Poly(sp.expand(p), *gens, modulus=modulus)


def _series_v_of_u(H: sp.Expr, u: sp.Symbol, v: sp.Symbol, n_terms: int) -> list[int]:
    """
    Solve H(u, v(u)) = 0 with v(0)=0 as a truncated power series over Q.
    Returns integer numerators of coefficients after clearing denominators by lcm.

    The LaTeX proof uses Hensel/implicit function; this is a sanity check only.
    """
    coeffs: list[sp.Rational] = []
    vu = sp.Integer(0)

    for k in range(1, n_terms + 1):
        ck = sp.Symbol(f"c{k}")
        trial = vu + ck * u**k
        trunc = sp.series(sp.expand(H.subs({v: trial})), u, 0, k + 1).removeO()
        eq = sp.expand(trunc.coeff(u, k))
        sol = sp.solve(sp.Eq(eq, 0), ck)
        if len(sol) != 1:
            raise RuntimeError(f"non-unique coefficient at order {k}: {sol}")
        ck_val = sp.nsimplify(sol[0])
        if not isinstance(ck_val, sp.Rational):
            raise RuntimeError(f"non-rational coefficient at order {k}: {ck_val}")
        coeffs.append(ck_val)
        vu = sp.expand(vu + ck_val * u**k)

    den_lcm = sp.ilcm(*[c.q for c in coeffs]) if coeffs else 1
    ints = [int(c * den_lcm) for c in coeffs]
    return ints


def main() -> None:
    u, v = sp.symbols("u v")
    lam, y = sp.symbols("lam y")

    Pi = _pi(lam, y)

    expr_27 = sp.expand(Pi.subs({lam: 2 + 3 * v, y: 1 + 27 * u}))
    expr_9 = sp.expand(Pi.subs({lam: 2 + 3 * v, y: 1 + 9 * u}))

    H_from_expr = sp.expand(expr_27 / 27)
    H9_from_expr = sp.expand(expr_9 / 9)

    H_stated = (
        27 * u**2
        - 18 * u * v**2
        - 24 * u * v
        - 5 * u
        + 3 * v**4
        + 7 * v**3
        + 5 * v**2
        + v
    )
    H9_stated = (
        9 * u**2
        - 18 * u * v**2
        - 24 * u * v
        - 5 * u
        + 9 * v**4
        + 21 * v**3
        + 15 * v**2
        + 3 * v
    )

    dHdv_00 = sp.diff(H_stated, v).subs({u: 0, v: 0})

    H_mod3 = _poly_mod(H_stated, u, v, modulus=3).as_expr()
    H9_mod3 = _poly_mod(H9_stated, u, v, modulus=3).as_expr()

    cubic_mod3 = _poly_mod(u + v**3 - v**2 + v, u, v, modulus=3).as_expr()

    # Truncated series sanity check (not used in the paper statements).
    v_series_scaled_ints = _series_v_of_u(H_stated, u=u, v=v, n_terms=12)

    out = {
        "checks": {
            "Pi_27_factor_ok": sp.expand(expr_27 - 27 * H_stated) == 0,
            "Pi_27_H_matches_expansion": sp.expand(H_from_expr - H_stated) == 0,
            "dHdv_at_00": int(dHdv_00),
            "Pi_9_factor_ok": sp.expand(expr_9 - 9 * H9_stated) == 0,
            "Pi_9_H9_matches_expansion": sp.expand(H9_from_expr - H9_stated) == 0,
            "H_mod3_equals_u_plus_v3_minus_v2_plus_v": _poly_mod(H_mod3 - cubic_mod3, u, v, modulus=3).as_expr()
            == 0,
            "H9_mod3_equals_u": _poly_mod(H9_mod3 - u, u, v, modulus=3).as_expr() == 0,
        },
        "polynomials": {
            "H": sp.srepr(sp.expand(H_stated)),
            "H9": sp.srepr(sp.expand(H9_stated)),
            "H_mod3": sp.srepr(H_mod3),
            "H9_mod3": sp.srepr(H9_mod3),
        },
        "v_series_trunc": {
            "note": "Integers proportional to first coefficients of v(u); see script for scaling.",
            "scaled_coeffs": v_series_scaled_ints,
        },
    }

    p = _export_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

