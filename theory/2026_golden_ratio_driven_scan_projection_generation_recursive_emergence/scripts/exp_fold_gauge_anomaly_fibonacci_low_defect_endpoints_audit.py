#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: Fibonacci low-defect coefficients + Perron endpoint expansions (p=1/2 baseline)."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    details: Dict[str, object]


def _fib(n: int) -> int:
    if n < 0:
        return 0
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _compute_Mf_polys(nmax: int) -> List[sp.Poly]:
    u = sp.Symbol("u")
    Mf: List[sp.Poly] = [sp.Poly(0, u, domain="ZZ") for _ in range(nmax + 1)]
    Mf[0] = sp.Poly(1, u, domain="ZZ")
    Mf[1] = sp.Poly(2, u, domain="ZZ")
    Mf[2] = sp.Poly(3 + u, u, domain="ZZ")
    Mf[3] = sp.Poly(5 + u + 2 * u**2, u, domain="ZZ")
    for m in range(4, nmax + 1):
        expr = (
            Mf[m - 1].as_expr()
            + (2 * u + 1) * Mf[m - 2].as_expr()
            + (u**3 - 2 * u) * Mf[m - 3].as_expr()
            - 2 * u * Mf[m - 4].as_expr()
        )
        Mf[m] = sp.Poly(sp.expand(expr), u, domain="ZZ")
    return Mf


def _check_fibonacci_low_defect(Mf: List[sp.Poly]) -> List[Check]:
    u = sp.Symbol("u")
    checks: List[Check] = []

    nmax = len(Mf) - 1
    mismatches: List[Tuple[int, int, int, int]] = []
    for m in range(0, nmax + 1):
        a0 = int(Mf[m].coeff_monomial(u**0))
        exp0 = _fib(m + 2)
        a1 = int(Mf[m].coeff_monomial(u**1))
        exp1 = 0 if m in (0, 1) else _fib(m - 1)
        a2 = int(Mf[m].coeff_monomial(u**2))
        exp2 = 0 if m in (0, 1, 2) else 2 * _fib(m - 1)
        if (a0, a1, a2) != (exp0, exp1, exp2):
            mismatches.append((m, a0 - exp0, a1 - exp1, a2 - exp2))

    checks.append(
        Check(
            name="fibonacci_low_defect_coefficients",
            ok=len(mismatches) == 0,
            details={
                "nmax": nmax,
                "num_mismatches": len(mismatches),
                "mismatch_samples": mismatches[:10],
            },
        )
    )
    return checks


def _check_degree_and_leading_period3(Mf: List[sp.Poly]) -> List[Check]:
    u = sp.Symbol("u")
    nmax = len(Mf) - 1

    bad_deg: List[Tuple[int, int, int]] = []
    bad_lead: List[Tuple[int, int, int]] = []
    for m in range(2, nmax + 1):
        deg = int(Mf[m].degree())
        if deg != m - 1:
            bad_deg.append((m, deg, m - 1))

        lead = int(Mf[m].coeff_monomial(u ** (m - 1)))
        exp = 1 if (m % 3 == 2) else 2
        if lead != exp:
            bad_lead.append((m, lead, exp))

    return [
        Check(
            name="degree_is_m_minus_1",
            ok=len(bad_deg) == 0,
            details={"nmax": nmax, "num_bad": len(bad_deg), "bad_samples": bad_deg[:10]},
        ),
        Check(
            name="leading_coefficient_period_3",
            ok=len(bad_lead) == 0,
            details={"nmax": nmax, "num_bad": len(bad_lead), "bad_samples": bad_lead[:10]},
        ),
    ]


def _check_explicit_closed_forms_k3_to_k6(Mf: List[sp.Poly]) -> List[Check]:
    u = sp.Symbol("u")
    nmax = len(Mf) - 1

    mismatches: List[Dict[str, int]] = []
    for m in range(0, nmax + 1):
        Fm = _fib(m)
        Fm1 = _fib(m - 1)

        a3 = int(Mf[m].coeff_monomial(u**3))
        a4 = int(Mf[m].coeff_monomial(u**4))
        a5 = int(Mf[m].coeff_monomial(u**5))
        a6 = int(Mf[m].coeff_monomial(u**6))

        if m >= 5:
            num = (m - 26) * Fm + 2 * (m + 20) * Fm1
            if num % 5 != 0 or a3 != num // 5:
                mismatches.append({"m": m, "k": 3, "got": a3, "exp": num // 5})

        if m >= 7:
            num = (m - 136) * Fm + 2 * (m + 105) * Fm1
            if num % 5 != 0 or a4 != num // 5:
                mismatches.append({"m": m, "k": 4, "got": a4, "exp": num // 5})

        if m >= 9:
            num = 4 * (m - 181) * Fm + (1150 - 2 * m) * Fm1
            if num % 5 != 0 or a5 != num // 5:
                mismatches.append({"m": m, "k": 5, "got": a5, "exp": num // 5})

        if m >= 11:
            num = (5 * m * m + 393 * m - 40048) * Fm + (-5 * m * m - 619 * m + 64550) * Fm1
            if num % 50 != 0 or a6 != num // 50:
                mismatches.append({"m": m, "k": 6, "got": a6, "exp": num // 50})

    return [
        Check(
            name="explicit_closed_forms_k3_to_k6",
            ok=len(mismatches) == 0,
            details={
                "nmax": nmax,
                "num_mismatches": len(mismatches),
                "mismatch_samples": mismatches[:10],
            },
        )
    ]


def _solve_low_temp_mu_series() -> Check:
    u = sp.Symbol("u")
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    c1, c2, c3, c4, c5, c6 = sp.symbols("c1 c2 c3 c4 c5 c6")

    mu = phi + c1 * u + c2 * u**2 + c3 * u**3 + c4 * u**4 + c5 * u**5 + c6 * u**6
    F = mu**4 - mu**3 - (2 * u + 1) * mu**2 + (2 * u - u**3) * mu + 2 * u

    series = sp.expand(F).series(u, 0, 7).removeO()
    eqs = [sp.Eq(sp.expand(series).coeff(u, n), 0) for n in range(1, 7)]
    sol = sp.solve(eqs, [c1, c2, c3, c4, c5, c6], dict=True)
    if len(sol) != 1:
        return Check(
            name="low_temp_mu_series_coefficients",
            ok=False,
            details={"reason": "unexpected_solution_count", "count": len(sol)},
        )
    sol = sol[0]

    expected = {
        c1: sp.Integer(0),
        c2: sp.Integer(0),
        c3: sp.Rational(1, 2) - sqrt5 / 10,
        c4: sp.Integer(2) - 4 * sqrt5 / 5,
        c5: sp.Integer(10) - 22 * sqrt5 / 5,
        c6: sp.Rational(105, 2) - 1173 * sqrt5 / 50,
    }
    ok = all(sp.simplify(sol[k] - expected[k]) == 0 for k in expected)
    details = {
        "c1": str(sol[c1]),
        "c2": str(sol[c2]),
        "c3": str(sol[c3]),
        "c4": str(sol[c4]),
        "c5": str(sol[c5]),
        "c6": str(sol[c6]),
    }
    if not ok:
        details["expected"] = {str(k): str(v) for k, v in expected.items()}
    return Check(name="low_temp_mu_series_coefficients", ok=ok, details=details)


def _solve_high_temp_mu_asymptotic() -> List[Check]:
    v = sp.Symbol("v")  # v = 1/u -> 0+
    c0, c1, c2, c3 = sp.symbols("c0 c1 c2 c3")

    u = 1 / v
    mu = 1 / v + c0 + c1 * v + c2 * v**2 + c3 * v**3
    F = mu**4 - mu**3 - (2 * u + 1) * mu**2 + (2 * u - u**3) * mu + 2 * u

    # Clear leading v^{-4} and expand around v=0.
    expr = sp.expand((v**4) * F).series(v, 0, 5).removeO()
    # Need enough constraints to determine (c0,c1,c2,c3).
    eqs = [sp.Eq(sp.expand(expr).coeff(v, n), 0) for n in range(0, 5)]
    sol = sp.solve(eqs, [c0, c1, c2, c3], dict=True)
    if len(sol) != 1:
        return [
            Check(
                name="high_temp_mu_inverse_power_coefficients",
                ok=False,
                details={"reason": "unexpected_solution_count", "count": len(sol)},
            )
        ]
    sol = sol[0]

    expected = {c0: sp.Integer(1), c1: sp.Integer(0), c2: sp.Rational(-1, 3), c3: sp.Rational(8, 9)}
    ok_coeff = all(sp.simplify(sol[k] - expected[k]) == 0 for k in expected)

    # Check log expansion coefficients in t = e^{-theta} = v.
    t = sp.Symbol("t")
    mu_t = 1 / t + 1 - sp.Rational(1, 3) * t**2 + sp.Rational(8, 9) * t**3
    log_part = sp.log(1 + t - sp.Rational(1, 3) * t**3 + sp.Rational(8, 9) * t**4)
    s = sp.expand(log_part.series(t, 0, 5).removeO())
    coeffs = {n: sp.simplify(s.coeff(t, n)) for n in range(1, 5)}
    expected_coeffs = {1: sp.Integer(1), 2: sp.Rational(-1, 2), 3: sp.Integer(0), 4: sp.Rational(35, 36)}
    ok_log = all(sp.simplify(coeffs[n] - expected_coeffs[n]) == 0 for n in expected_coeffs)

    return [
        Check(
            name="high_temp_mu_inverse_power_coefficients",
            ok=ok_coeff,
            details={str(k): str(sol[k]) for k in expected},
        ),
        Check(
            name="high_temp_pressure_log_correction_series",
            ok=ok_log,
            details={
                "series_log1px_up_to_t4": str(s),
                "coeffs": {str(k): str(v) for k, v in coeffs.items()},
            },
        ),
    ]


def main() -> None:
    checks: List[Check] = []

    Mf = _compute_Mf_polys(nmax=30)
    checks.extend(_check_fibonacci_low_defect(Mf))
    checks.extend(_check_degree_and_leading_period3(Mf))
    checks.extend(_check_explicit_closed_forms_k3_to_k6(Mf))
    checks.append(_solve_low_temp_mu_series())
    checks.extend(_solve_high_temp_mu_asymptotic())

    ok = all(c.ok for c in checks)

    out = export_dir() / "fold_gauge_anomaly_fibonacci_low_defect_endpoints_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "ok": ok,
        "checks": [asdict(c) for c in checks],
    }
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not ok:
        raise SystemExit(f"audit failed: wrote {out}")
    print(f"[ok] wrote {out}")


if __name__ == "__main__":
    main()

