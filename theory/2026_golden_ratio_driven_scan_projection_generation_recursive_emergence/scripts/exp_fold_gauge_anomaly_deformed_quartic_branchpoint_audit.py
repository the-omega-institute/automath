#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit symbolic identities for the deformed quartic branchpoint system F_t(mu,u).

This script checks, using exact SymPy algebra:
  - Linear elimination formulas for X = t u and Y = u^3 under F_t = d_mu F_t = 0.
  - The mu-only reduction equation E_t(mu) and the rational recovery u(mu).
  - The specialization t=2 factorization E_2(mu) = (mu+1) Q10(mu).
  - The local series at the resonant real point (t,u,mu) = (2,1,-1) up to cubic order.

Outputs:
  - artifacts/export/fold_gauge_anomaly_deformed_quartic_branchpoint_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class SeriesRow:
    u1: str
    u2: str
    u3: str
    mu1: str
    mu2: str
    mu3: str


def _elim_XY(mu: sp.Symbol) -> Tuple[sp.Expr, sp.Expr]:
    X = sp.Symbol("X")
    Y = sp.Symbol("Y")
    eq1 = sp.Eq(mu**4 - mu**3 - mu**2 - mu * Y + (-mu**2 + mu + 1) * X, 0)
    eq2 = sp.Eq(4 * mu**3 - 3 * mu**2 - 2 * mu - Y + (1 - 2 * mu) * X, 0)
    sol = sp.solve([eq1, eq2], [X, Y], dict=True)
    if len(sol) != 1:
        raise RuntimeError("Unexpected number of (X,Y) solutions.")
    return sp.simplify(sol[0][X]), sp.simplify(sol[0][Y])


def main() -> None:
    mu, u, t = sp.symbols("mu u t")

    Ft = mu**4 - mu**3 - (t * u + 1) * mu**2 + mu * (t * u - u**3) + t * u
    dmu = sp.diff(Ft, mu)

    # Linear elimination identities (X,Y) as rational functions of mu.
    X_mu, Y_mu = _elim_XY(mu)
    X_expected = sp.simplify(mu**2 * (3 * mu**2 - 2 * mu - 1) / (mu**2 + 1))
    Y_expected = sp.simplify(-2 * mu * (mu**2 - mu - 1) ** 2 / (mu**2 + 1))
    if sp.simplify(X_mu - X_expected) != 0:
        raise AssertionError("X(mu) elimination formula mismatch.")
    if sp.simplify(Y_mu - Y_expected) != 0:
        raise AssertionError("Y(mu) elimination formula mismatch.")

    # mu-only reduction E_t(mu) from u = X/t and u^3 = Y.
    u_mu = sp.simplify(X_expected / t)
    Et_from_constraint = sp.together(u_mu**3 - Y_expected)
    num = sp.factor(sp.together(Et_from_constraint).as_numer_denom()[0])

    Et_expected = sp.factor(
        2 * t**3 * (mu**2 + 1) ** 2 * (mu**2 - mu - 1) ** 2 + mu**5 * (3 * mu**2 - 2 * mu - 1) ** 3
    )
    # The cleared numerator equals mu * E_t(mu). (The mu=0 branch corresponds to u=0, excluded in-text.)
    if sp.factor(num - mu * Et_expected) != 0:
        raise AssertionError("E_t(mu) reduction mismatch.")

    # t=2 factorization and Q10 check.
    Et2 = sp.factor(Et_expected.subs(t, 2))
    Q10 = sp.factor(Et2 / (mu + 1))
    Q10_expected = sp.Poly(
        27 * mu**10
        - 81 * mu**9
        + 90 * mu**8
        - 46 * mu**7
        + 11 * mu**6
        - mu**5
        - 32 * mu**4
        + 32 * mu**3
        + 16 * mu
        + 16,
        mu,
    ).as_expr()
    if sp.factor(Q10 - Q10_expected) != 0:
        raise AssertionError("Q10(mu) mismatch under t=2 factorization.")

    # Local series at (t,mu) = (2,-1) from E_t(mu)=0, then u(mu,t)=X/t.
    eps = sp.Symbol("eps")
    a1, a2, a3 = sp.symbols("a1 a2 a3")
    b1, b2, b3 = sp.symbols("b1 b2 b3")

    mu_ans = -1 + a1 * eps + a2 * eps**2 + a3 * eps**3
    t_ans = 2 + eps
    Et_series = sp.series(Et_expected.subs({t: t_ans, mu: mu_ans}), eps, 0, 4).removeO()
    coeffs = [sp.expand(Et_series).coeff(eps, k) for k in range(1, 4)]
    sol_a = sp.solve(coeffs, [a1, a2, a3], dict=True)
    if len(sol_a) != 1:
        raise RuntimeError("Unexpected series solution multiplicity for mu(t).")
    sol_a = sol_a[0]

    mu_series = sp.expand(mu_ans.subs(sol_a))
    u_series_expr = sp.simplify(u_mu.subs({t: t_ans, mu: mu_series}))
    u_series = sp.series(u_series_expr, eps, 0, 4).removeO()

    # Expected coefficients.
    mu_expected = -1 + (-sp.Rational(1, 2)) * eps + sp.Rational(3, 16) * eps**2 + (-sp.Rational(23, 64)) * eps**3
    u_expected = 1 + eps - sp.Rational(1, 2) * eps**2 + sp.Rational(7, 8) * eps**3
    if sp.expand(mu_series - mu_expected) != 0:
        raise AssertionError("mu_b(t) series coefficients mismatch.")
    if sp.expand(u_series - u_expected) != 0:
        raise AssertionError("u_b(t) series coefficients mismatch.")

    row = SeriesRow(
        u1=str(sp.Rational(1, 1)),
        u2=str(-sp.Rational(1, 2)),
        u3=str(sp.Rational(7, 8)),
        mu1=str(-sp.Rational(1, 2)),
        mu2=str(sp.Rational(3, 16)),
        mu3=str(-sp.Rational(23, 64)),
    )

    payload: Dict[str, object] = {
        "X_mu": sp.srepr(X_expected),
        "Y_mu": sp.srepr(Y_expected),
        "Et_expected": sp.srepr(Et_expected),
        "Et2_factor": sp.srepr(Et2),
        "series": asdict(row),
        "ok": True,
    }

    out_json = export_dir() / "fold_gauge_anomaly_deformed_quartic_branchpoint_audit.json"
    _write_json(out_json, payload)
    print("[fold-gauge-anomaly-deformed-quartic-branchpoint-audit] ok")


if __name__ == "__main__":
    main()

