#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit P_G(theta) cumulants up to order 5 (uniform baseline).

We use the implicit quartic F(mu,u)=0 for mu(u)=2*rho(A_theta) with u=e^theta,
expand the unique analytic branch at (u,mu)=(1,2), and extract the Taylor
series of P_G(theta)=log(mu(e^theta)/2).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import paper_root, scripts_dir


@dataclass(frozen=True)
class SeriesCoeff:
    order: int
    value: str


def _series_solution_mu_theta(max_order: int) -> List[sp.Rational]:
    """
    Return coefficients a_k for mu(e^theta)=2 + sum_{k>=1} a_k theta^k.
    """
    theta = sp.Symbol("theta")
    u = sp.exp(theta)
    mu = sp.Symbol("mu")

    # Quartic from sections/generated/eq_fold_gauge_anomaly_pressure.tex
    F = mu**4 - mu**3 - 2 * u * mu**2 - mu**2 - mu * u**3 + 2 * mu * u + 2 * u

    # Ansatz mu(theta) = 2 + a1*theta + ... + aN*theta^N.
    a = sp.symbols("a1:" + str(max_order + 1))
    mu_series = 2 + sp.Add(*[a[k - 1] * theta**k for k in range(1, max_order + 1)])

    # Expand F(mu(theta), exp(theta)) as a series and solve coefficients sequentially.
    expr = sp.series(sp.expand(F.subs({mu: mu_series})), theta, 0, max_order + 1).removeO()
    expr = sp.expand(expr)

    solved: Dict[sp.Symbol, sp.Rational] = {}
    for k in range(1, max_order + 1):
        ck = sp.expand(expr.subs(solved)).coeff(theta, k)
        # ck is linear in a_k given previous coefficients fixed (implicit function theorem).
        ak = a[k - 1]
        sol = sp.solve(sp.Eq(ck, 0), ak, dict=True)
        if len(sol) != 1 or ak not in sol[0]:
            raise RuntimeError(f"Failed to solve coefficient a{k} uniquely.")
        solved[ak] = sp.nsimplify(sol[0][ak], rational=True)

    return [sp.Rational(solved[a[k - 1]]) for k in range(1, max_order + 1)]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit P_G cumulants up to order 5 (uniform baseline).")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "fold_gauge_anomaly_pressure_cumulants5.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    theta = sp.Symbol("theta")

    a = _series_solution_mu_theta(max_order=5)
    mu_theta = 2 + sum(a[k - 1] * theta**k for k in range(1, 6))
    P = sp.series(sp.log(mu_theta / 2), theta, 0, 6).removeO()
    P = sp.expand(P)

    # Extract cumulants kappa_r = P^{(r)}(0).
    kappa = [sp.diff(P, theta, r).subs(theta, 0) for r in range(1, 6)]

    # Expected values from the paper text.
    expected_kappa = [
        sp.Rational(4, 9),
        sp.Rational(118, 243),
        sp.Rational(-1174, 2187),
        sp.Rational(-8890, 19683),
        sp.Rational(17294570, 1594323),
    ]

    expected_series = [
        sp.Rational(4, 9),
        sp.Rational(59, 243),
        sp.Rational(-587, 6561),
        sp.Rational(-4445, 236196),
        sp.Rational(1729457, 19131876),
    ]

    series_coeffs = [sp.expand(P).coeff(theta, k) for k in range(1, 6)]

    out: Dict[str, object] = {
        "mu_theta_series_coeffs": [asdict(SeriesCoeff(order=k, value=str(a[k - 1]))) for k in range(1, 6)],
        "P_series_coeffs": [asdict(SeriesCoeff(order=k, value=str(series_coeffs[k - 1]))) for k in range(1, 6)],
        "kappa": [asdict(SeriesCoeff(order=r, value=str(kappa[r - 1]))) for r in range(1, 6)],
        "expected": {
            "P_series_coeffs": [str(c) for c in expected_series],
            "kappa": [str(c) for c in expected_kappa],
        },
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    for r in range(1, 6):
        assert sp.simplify(kappa[r - 1] - expected_kappa[r - 1]) == 0, f"kappa_{r} mismatch"
    for k in range(1, 6):
        assert sp.simplify(series_coeffs[k - 1] - expected_series[k - 1]) == 0, f"P series coeff theta^{k} mismatch"


if __name__ == "__main__":
    main()

