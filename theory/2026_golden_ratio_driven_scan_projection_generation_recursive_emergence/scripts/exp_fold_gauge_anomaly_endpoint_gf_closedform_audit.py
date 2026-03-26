#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit closed forms for fold-gauge anomaly endpoints and generating function.

This script audits identities stated in:
  sections/body/folding/subsubsec__fold-gauge-anomaly-spectral-recurrence-certificates.tex

Audits:
- Rational closed form for F(z,u) = sum_{m>=0} E_pi[u^{G_m}] z^m
- Endpoint probabilities P(G_m=0) and P(G_m=m) against stated Fibonacci / mod-3 laws

Outputs:
- artifacts/export/fold_gauge_anomaly_endpoint_gf_closedform_audit.json
"""

from __future__ import annotations

import json
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _fib(n: int) -> int:
    if n < 0:
        raise ValueError("fib expects n>=0")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _parry_kernel() -> sp.Matrix:
    # State order: (a,b,c,d)
    return sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 4), sp.Integer(0), sp.Rational(1, 4)],
            [sp.Integer(0), sp.Integer(0), sp.Integer(1), sp.Integer(0)],
            [sp.Rational(1, 2), sp.Rational(1, 2), sp.Integer(0), sp.Integer(0)],
            [sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(0)],
        ]
    )


def _stationary_pi(P: sp.Matrix) -> sp.Matrix:
    # Solve pi^T P = pi^T, sum pi = 1.
    pa, pb, pc, pd = sp.symbols("pa pb pc pd")
    pi = sp.Matrix([pa, pb, pc, pd])
    eqs = list((pi.T * P - pi.T)[0, :]) + [sp.Eq(pa + pb + pc + pd, 1)]
    sol = sp.solve(eqs, [pa, pb, pc, pd], dict=True)
    if len(sol) != 1:
        raise RuntimeError(f"expected unique stationary solution, got {len(sol)}")
    s = sol[0]
    return sp.Matrix([sp.simplify(s[pa]), sp.simplify(s[pb]), sp.simplify(s[pc]), sp.simplify(s[pd])])


def _tilt_kernel(P: sp.Matrix, u: sp.Symbol) -> sp.Matrix:
    # g=1 on edges (a,b), (b,c), (c,a); else 0.
    Q = sp.Matrix(P)  # copy
    # (a,b)
    Q[0, 1] = Q[0, 1] * u
    # (b,c)
    Q[1, 2] = Q[1, 2] * u
    # (c,a)
    Q[2, 0] = Q[2, 0] * u
    return Q


def _D_m(pi: sp.Matrix, Q: sp.Matrix, m: int, u: sp.Symbol) -> sp.Expr:
    one = sp.Matrix([1, 1, 1, 1])
    expr = (pi.T * (Q ** m) * one)[0, 0]
    return sp.together(sp.simplify(expr))


def main() -> None:
    u, z = sp.symbols("u z")
    P = _parry_kernel()
    pi = _stationary_pi(P)
    Q = _tilt_kernel(P, u)

    # Generating function via transfer-matrix:
    I = sp.eye(4)
    one = sp.Matrix([1, 1, 1, 1])
    F = sp.together((pi.T * (I - z * Q).inv() * one)[0, 0])

    Delta = 8 - 4 * z - (4 * u + 2) * z**2 + (2 * u - u**3) * z**3 + u * z**4
    N = (
        72
        + 4 * z
        - 12 * z**2
        - 2 * z**3
        + 32 * u * z
        - 24 * u * z**2
        - 10 * u * z**3
        + 18 * u**2 * z**2
        + 4 * u**2 * z**3
        - u**3 * z**3
    )

    gf_diff = sp.together(F - sp.Rational(1, 9) * N / Delta)
    gf_ok = sp.simplify(sp.factor(gf_diff)) == 0

    # Endpoint checks.
    m_max = 15
    endpoint_zero_ok = True
    endpoint_full_ok = True
    bad_zero: List[Dict[str, str]] = []
    bad_full: List[Dict[str, str]] = []
    for m in range(0, m_max + 1):
        Dm = _D_m(pi, Q, m, u)

        # P(G_m=0) = D_m(0)
        p0 = sp.simplify(Dm.subs(u, 0))
        if m == 0:
            p0_rhs = sp.Integer(1)
        elif m == 1:
            p0_rhs = sp.Rational(5, 9)
        else:
            p0_rhs = sp.Rational(_fib(m + 5), 9 * (2**m))
        if sp.simplify(p0 - p0_rhs) != 0:
            endpoint_zero_ok = False
            bad_zero.append({"m": str(m), "lhs": str(p0), "rhs": str(p0_rhs)})

        # P(G_m=m) = [u^m] D_m(u)
        if m >= 1:
            poly = sp.Poly(sp.expand(Dm), u)
            pm = sp.simplify(poly.coeffs()[0] if poly.degree() == 0 else poly.coeff_monomial(u**m))
            if m % 3 == 2:
                pm_rhs = sp.Rational(1, 2**m)
            else:
                pm_rhs = sp.Rational(8, 9) * sp.Rational(1, 2**m)
            if sp.simplify(pm - pm_rhs) != 0:
                endpoint_full_ok = False
                bad_full.append({"m": str(m), "lhs": str(pm), "rhs": str(pm_rhs)})

    out = {
        "gf_ok": gf_ok,
        "endpoint_zero_ok": endpoint_zero_ok,
        "endpoint_full_ok": endpoint_full_ok,
        "m_max": m_max,
        "bad_zero": bad_zero,
        "bad_full": bad_full,
        "pi": [str(x) for x in list(pi)],
    }
    export_dir().mkdir(parents=True, exist_ok=True)
    (export_dir() / "fold_gauge_anomaly_endpoint_gf_closedform_audit.json").write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()

