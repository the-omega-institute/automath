#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Lee–Yang branch-data reconstruction from kappa_*^2.

This script verifies exact polynomial identities used in:
  - quadratic reconstruction of (lambda_0, y_0, beta_*) from u = kappa_*^2,
  - minimal polynomial for beta_*,
  - the deck involution u -> 25/21 - u and pullback factorization of P_LY(y(u))
    and B(y)=y(y-1)P_LY(y).

Outputs:
  - artifacts/export/xi_leyang_kappa_square_quadratic_reconstruction_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Optional

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _poly_eq(a: sp.Expr, b: sp.Expr) -> bool:
    return bool(sp.factor(a - b) == 0)


@dataclass(frozen=True)
class Payload:
    ok_quadratic_reconstruction: bool
    ok_beta_minpoly: bool
    ok_integralizations: bool
    ok_deck_involution: bool
    ok_pullback_factorizations: bool
    details_first_failure: Optional[str]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Lee–Yang u=kappa^2 reconstruction identities.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()

    u, y, beta, T, S = sp.symbols("u y beta T S")

    g = 324 * u**3 - 540 * u**2 + 333 * u - 74

    lam_poly = -sp.Rational(31, 16) + sp.Rational(27, 4) * u - sp.Rational(27, 4) * u**2
    y_poly = -sp.Rational(1091, 256) + sp.Rational(675, 64) * u - sp.Rational(567, 64) * u**2
    beta_poly = -sp.Rational(11, 36) - sp.Rational(1, 8) * u + sp.Rational(5, 4) * u**2

    # Quadratic identities as cleared-denominator forms.
    ok_quadratic = True
    fail: Optional[str] = None
    if not _poly_eq(16 * lam_poly + 31, 108 * u * (1 - u)):
        ok_quadratic = False
        fail = "16*lambda(u)+31 != 108*u*(1-u)"
    if ok_quadratic and not _poly_eq(256 * y_poly + 1091, 108 * u * (25 - 21 * u)):
        ok_quadratic = False
        fail = "256*y(u)+1091 != 108*u*(25-21u)"
    if ok_quadratic and not _poly_eq(72 * beta_poly + 22, 9 * u * (10 * u - 1)):
        ok_quadratic = False
        fail = "72*beta(u)+22 != 9*u*(10u-1)"

    # Verify lambda(u) and y(u) are consistent with the defining relations on the Lee–Yang branch:
    #   h(lam)=16 lam^3 - 9 lam^2 + 1 = 0
    #   y = (4 lam^3 - 3 lam^2 - 2 lam + 1)/(4 lam)
    h = 16 * sp.Symbol("lam") ** 3 - 9 * sp.Symbol("lam") ** 2 + 1
    lam = sp.Symbol("lam")
    h_sub = sp.factor(sp.together(h.subs(lam, lam_poly)))
    num_h = sp.factor(sp.together(h_sub).as_numer_denom()[0])
    if ok_quadratic:
        q, r = sp.div(num_h, sp.Poly(g, u))
        if sp.factor(r.as_expr()) != 0:
            ok_quadratic = False
            fail = "h(lambda(u)) not 0 mod g(u)"

    y_from_lam = sp.together((4 * lam**3 - 3 * lam**2 - 2 * lam + 1) / (4 * lam))
    y_sub = sp.factor(sp.together(y_from_lam.subs(lam, lam_poly) - y_poly))
    num_y = sp.factor(sp.together(y_sub).as_numer_denom()[0])
    if ok_quadratic:
        q, r = sp.div(num_y, sp.Poly(g, u))
        if sp.factor(r.as_expr()) != 0:
            ok_quadratic = False
            fail = "y(lambda(u)) - y(u) not 0 mod g(u)"

    # Minimal polynomial for beta via elimination.
    beta_expected = 419904 * beta**3 + 93312 * beta**2 + 72279 * beta - 1112
    res_beta = sp.resultant(g, sp.together(beta_poly - beta).as_numer_denom()[0], u)
    res_beta_factored = sp.factor(res_beta)
    # The resultant is proportional to beta_expected; normalize by content.
    ok_beta = bool(sp.factor(beta_expected) == beta_expected)
    if ok_beta:
        ratio = sp.together(res_beta_factored / beta_expected)
        ok_beta = bool(sp.factor(ratio).free_symbols <= {sp.Integer(1)} or ratio.free_symbols == set())
        if not ok_beta:
            # fallback: compare after making primitive in beta
            rb = sp.Poly(res_beta_factored, beta).primitive()[1]
            be = sp.Poly(beta_expected, beta).primitive()[1]
            ok_beta = bool(rb == be)
    if not ok_beta and fail is None:
        fail = "beta minimal polynomial elimination mismatch"

    # Integralizations:
    T_poly_expected = T**3 - 270 * T**2 + 26973 * T - 971028
    S_poly_expected = S**3 + 11664 * S**2 + 474222519 * S - 382943630016

    T_poly = sp.expand(g.subs(u, T / 162) * 162**3)
    T_poly = sp.Poly(T_poly, T)
    # make monic
    T_poly_monic = sp.Poly(T_poly.monic(), T)

    S_rel_num = sp.together(beta_poly.subs(u, u) - S / 52488).as_numer_denom()[0]
    res_S = sp.resultant(g, S_rel_num, u)
    res_S = sp.Poly(sp.factor(res_S), S)
    res_S_monic = sp.Poly(res_S.monic(), S)

    ok_int = bool(T_poly_monic.as_expr() == T_poly_expected and res_S_monic.as_expr() == S_poly_expected)
    if not ok_int and fail is None:
        fail = "integralization monic polynomials mismatch"

    # Deck involution and pullbacks.
    iota = sp.Rational(25, 21) - u
    ok_iota = bool(sp.factor(y_poly.subs(u, iota) - y_poly) == 0)
    if not ok_iota and fail is None:
        fail = "y(u) not invariant under iota(u)=25/21-u"

    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    pull = sp.factor(sp.together(P_LY.subs(y, y_poly)))
    pull_poly = sp.Poly(pull, u)
    g_iota = sp.Poly(g.subs(u, iota), u)
    target_PL = sp.factor(sp.Rational(3**4 * 7**3, 2**14) * sp.Poly(g, u).as_expr() * g_iota.as_expr())
    ok_pull = bool(sp.factor(pull_poly.as_expr() - target_PL) == 0)

    B = y * (y - 1) * P_LY
    pullB = sp.factor(sp.together(B.subs(y, y_poly)))
    q0 = 2268 * u**2 - 2700 * u + 1091
    q1 = 756 * u**2 - 900 * u + 449
    target_B = sp.factor(
        sp.Rational(3**5 * 7**3, 2**30) * q0 * q1 * sp.Poly(g, u).as_expr() * g_iota.as_expr()
    )
    ok_pull = bool(ok_pull and sp.factor(pullB - target_B) == 0)
    if not ok_pull and fail is None:
        fail = "pullback factorization mismatch"

    payload = Payload(
        ok_quadratic_reconstruction=ok_quadratic,
        ok_beta_minpoly=ok_beta,
        ok_integralizations=ok_int,
        ok_deck_involution=ok_iota,
        ok_pullback_factorizations=ok_pull,
        details_first_failure=fail,
    )

    if not args.no_output:
        out = export_dir() / "xi_leyang_kappa_square_quadratic_reconstruction_audit.json"
        _write_json(out, asdict(payload))
        print(f"[xi-leyang-kappa-square] wrote {out}", flush=True)

    dt = time.time() - t0
    print(f"[xi-leyang-kappa-square] done elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

