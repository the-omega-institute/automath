#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the Möbius cocycle for y under doubling on E.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

We verify the explicit PGL_2(Q(X)) representation:
  [2]^*(y) = (a(X) y + b(X)) / (c(X) y + d(X))
with the stated a,b,c,d, and the factorizations of det and trace.

Outputs:
  - artifacts/export/fold_zm_elliptic_y_doubling_mobius_cocycle_audit.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _curve_remainder_in_Y(num: sp.Expr, X: sp.Symbol, Y: sp.Symbol) -> sp.Expr:
    """Reduce a polynomial numerator modulo Y^2 - (X^3 - X + 1/4)."""
    f = X**3 - X + sp.Rational(1, 4)
    curve_poly = sp.Poly(Y**2 - f, Y)
    return sp.Poly(num, Y).rem(curve_poly).as_expr()


def _is_zero_in_QE(expr: sp.Expr, X: sp.Symbol, Y: sp.Symbol) -> bool:
    """Check expr == 0 in Q(E)=Q(X,Y)/(Y^2 - (X^3-X+1/4))."""
    num = sp.together(expr).as_numer_denom()[0]
    rem = _curve_remainder_in_Y(num, X, Y)
    remY = sp.Poly(rem, Y)
    c0 = sp.together(remY.nth(0)).as_numer_denom()[0]
    c1 = sp.together(remY.nth(1)).as_numer_denom()[0]
    return sp.Poly(c0, X, domain=sp.QQ).is_zero and sp.Poly(c1, X, domain=sp.QQ).is_zero


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    def log(msg: str) -> None:
        if not args.quiet:
            print(msg, flush=True)

    X, Y = sp.symbols("X Y")
    y = X**2 + Y - sp.Rational(1, 2)
    D = 4 * X**3 - 4 * X + 1

    # Doubling formulas on short Weierstrass:
    #   m = (3X^2 - 1)/(2Y), X2 = m^2 - 2X, Y2 = m*(X - X2) - Y.
    m = (3 * X**2 - 1) / (2 * Y)
    X2 = sp.together(m**2 - 2 * X)
    Y2 = sp.together(m * (X - X2) - Y)
    y2 = sp.together(X2**2 + Y2 - sp.Rational(1, 2))

    a = 2 * (2 * X**8 - 8 * X**6 - 8 * X**5 + 44 * X**4 - 24 * X**3 + 1)
    b = -2 * (
        2 * X**10
        - 4 * X**9
        - 9 * X**8
        + 16 * X**7
        + 27 * X**6
        - 20 * X**5
        - X**4
        - 15 * X**3
        + 10 * X**2
        + X
        - 1
    )
    c = 4 * D**2
    d = -2 * (2 * X**2 - 1) * D**2

    y_mobius = sp.together((a * y + b) / (c * y + d))

    log("Checking [2]^*y Möbius identity in Q(E).")
    ok_identity = _is_zero_in_QE(y2 - y_mobius, X, Y)
    if not ok_identity:
        raise AssertionError("Möbius cocycle identity failed in Q(E).")

    log("Checking det/trace factorizations in Q[X].")
    detM = sp.expand(a * d - b * c)
    det_expected = sp.expand(
        -4
        * D**3
        * (2 * X**6 - 10 * X**4 + 10 * X**3 - 10 * X**2 + 2 * X + 1)
    )
    ok_det = sp.Poly(detM - det_expected, X, domain=sp.QQ).is_zero
    if not ok_det:
        raise AssertionError("det(M) factorization identity failed.")

    trM = sp.expand(a + d)
    psi3 = 3 * X**4 - 6 * X**2 + 3 * X - 1
    tr_expected = sp.expand(-4 * psi3 * (5 * X**4 - 2 * X**2 - X + 1))
    ok_tr = sp.Poly(trM - tr_expected, X, domain=sp.QQ).is_zero
    if not ok_tr:
        raise AssertionError("tr(M) factorization identity failed.")

    out = export_dir() / "fold_zm_elliptic_y_doubling_mobius_cocycle_audit.json"
    _write_json(
        out,
        {
            "ok_identity_in_QE": ok_identity,
            "ok_det_identity": ok_det,
            "ok_tr_identity": ok_tr,
        },
    )
    log(f"Wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

