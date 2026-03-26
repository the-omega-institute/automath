#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit exact constants for the xi collision-pressure conclusions.

This script certifies the explicit formulas used for the real-input 40-state
collision pressure P_2(theta)=log rho(exp(theta)), namely:

  - the local Legendre/Cramer--Edgeworth expansion of the normalized rate
    function I_2 around its mean alpha_*;
  - the continuous Edgeworth median shift constant;
  - the prime-twist p^2 threshold constants c2, c4 and sample errors;
  - the mod-2 twisted trace decomposition into one real mode plus one complex
    conjugate pair;
  - the negative-frequency algebraic branch alpha_- attached to the mod-2
    parity twist.

Output:
  - artifacts/export/xi_real_input_40_collision_ldp_median_twist_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp
import sympy as sp

from common_paths import export_dir


@dataclass(frozen=True)
class PrimeTwistSample:
    p: int
    rho_over_lambda: str
    log_rho_over_lambda: str
    asymptotic_log: str
    abs_error: str
    scaled_p6_error: str


@dataclass(frozen=True)
class TraceSample:
    n: int
    exact_trace: int
    spectral_trace: str
    abs_error: str


def _sp_str(expr: sp.Expr) -> str:
    return str(sp.simplify(expr))


def _mp_str(x: mp.mpf | mp.mpc, nd: int = 18) -> str:
    if isinstance(x, mp.mpc):
        sign = "+" if x.imag >= 0 else ""
        return f"{mp.nstr(x.real, nd)}{sign}{mp.nstr(x.imag, nd)}j"
    return mp.nstr(x, nd)


def _alpha_from_rho(rho: mp.mpf) -> mp.mpf:
    num = (rho**2 - 2 * rho - 1) * (rho - 1)
    den = 2 * rho**3 - 5 * rho**2 + 4 * rho + 1
    return num / den


def _derive_theta_inverse_and_rate(
    k2: sp.Expr, k3: sp.Expr, k4: sp.Expr
) -> Dict[str, sp.Expr]:
    delta = sp.Symbol("delta")
    a1, a2, a3 = sp.symbols("a1 a2 a3")
    theta_series = a1 * delta + a2 * delta**2 + a3 * delta**3
    alpha_minus_mean = sp.expand(
        k2 * theta_series + sp.Rational(1, 2) * k3 * theta_series**2 + sp.Rational(1, 6) * k4 * theta_series**3
    )

    s1 = sp.solve(sp.Eq(alpha_minus_mean.coeff(delta, 1), 1), a1, dict=True)
    if not s1:
        raise RuntimeError("No inverse-series solution for a1.")
    sol1 = s1[0]

    s2 = sp.solve(sp.Eq(alpha_minus_mean.subs(sol1).coeff(delta, 2), 0), a2, dict=True)
    if not s2:
        raise RuntimeError("No inverse-series solution for a2.")
    sol2 = {**sol1, **s2[0]}

    s3 = sp.solve(sp.Eq(alpha_minus_mean.subs(sol2).coeff(delta, 3), 0), a3, dict=True)
    if not s3:
        raise RuntimeError("No inverse-series solution for a3.")
    sol3 = {**sol2, **s3[0]}

    theta_inverse = sp.expand(theta_series.subs(sol3))
    rate_series = sp.expand(sp.integrate(theta_inverse, (delta, 0, delta)))

    return {
        "theta_inverse": theta_inverse,
        "rate_series": rate_series,
        "theta_a1": sp.simplify(theta_inverse.coeff(delta, 1)),
        "theta_a2": sp.simplify(theta_inverse.coeff(delta, 2)),
        "theta_a3": sp.simplify(theta_inverse.coeff(delta, 3)),
        "rate_q2": sp.simplify(rate_series.coeff(delta, 2)),
        "rate_q3": sp.simplify(rate_series.coeff(delta, 3)),
        "rate_q4": sp.simplify(rate_series.coeff(delta, 4)),
    }


def _prime_twist_samples(primes: List[int]) -> List[PrimeTwistSample]:
    mp.mp.dps = 80
    sqrt5 = mp.sqrt(5)
    lam = (3 + sqrt5) / 2
    c2 = (2 * mp.pi**2 / 125) * (6 * sqrt5 - 5)
    c4 = (2 * mp.pi**4 / 9375) * (7 + 24 * sqrt5)

    out: List[PrimeTwistSample] = []
    for p in primes:
        u = mp.e ** (2j * mp.pi / p)
        roots = mp.polyroots([1, -2, -(u + 1), u], maxsteps=200)
        rho_p = max(abs(root) for root in roots)
        log_ratio = mp.log(rho_p / lam)
        asym = -c2 / (p**2) + c4 / (p**4)
        abs_error = abs(log_ratio - asym)
        out.append(
            PrimeTwistSample(
                p=int(p),
                rho_over_lambda=_mp_str(rho_p / lam),
                log_rho_over_lambda=_mp_str(log_ratio),
                asymptotic_log=_mp_str(asym),
                abs_error=_mp_str(abs_error),
                scaled_p6_error=_mp_str(abs_error * (p**6)),
            )
        )
    return out


def _parity_trace_samples() -> Dict[str, object]:
    x = sp.Symbol("x")
    F = sp.Matrix([[1, 1], [1, 0]])
    A = sp.kronecker_product(F, F)
    D_minus = sp.diag(1, 1, 1, -1)
    W_minus = D_minus * A

    charpoly = sp.expand(W_minus.charpoly(x).as_expr())
    factored = sp.factor(charpoly)
    expected_factor = (x + 1) * (x**3 - 2 * x**2 - 1)
    if sp.expand(charpoly - expected_factor) != 0:
        raise RuntimeError("Unexpected mod-2 twisted characteristic polynomial.")

    cubic = sp.Poly(x**3 - 2 * x**2 - 1, x)
    roots = list(cubic.nroots(n=80))
    real_roots = [root for root in roots if abs(sp.im(root)) < sp.Float("1e-40")]
    complex_roots = [root for root in roots if abs(sp.im(root)) >= sp.Float("1e-40")]
    if len(real_roots) != 1 or len(complex_roots) != 2:
        raise RuntimeError("Unexpected cubic root pattern for x^3 - 2 x^2 - 1.")

    rho_minus_sym = sp.re(real_roots[0])
    rho_minus = mp.mpf(str(sp.N(rho_minus_sym, 60)))
    xi = complex_roots[0] if sp.im(complex_roots[0]) > 0 else complex_roots[1]
    xi_mp = mp.mpc(str(sp.N(sp.re(xi), 60)), str(sp.N(sp.im(xi), 60)))

    cos_theta = ((2 - rho_minus) * mp.sqrt(rho_minus)) / 2
    if cos_theta > 1:
        cos_theta = mp.mpf("1")
    if cos_theta < -1:
        cos_theta = mp.mpf("-1")
    theta = mp.acos(cos_theta)

    trace_samples: List[TraceSample] = []
    for n in range(1, 13):
        exact_trace = int((W_minus**n).trace())
        spectral_trace = rho_minus**n + (-1) ** n + 2 * rho_minus ** (-mp.mpf(n) / 2) * mp.cos(n * theta)
        trace_samples.append(
            TraceSample(
                n=n,
                exact_trace=exact_trace,
                spectral_trace=_mp_str(spectral_trace),
                abs_error=_mp_str(abs(spectral_trace - exact_trace), 6),
            )
        )
        if abs(spectral_trace - exact_trace) > mp.mpf("1e-40"):
            raise RuntimeError(f"Trace mismatch at n={n}.")

    return {
        "charpoly": _sp_str(charpoly),
        "charpoly_factorized": str(factored),
        "rho_minus": _mp_str(rho_minus, 24),
        "xi": _mp_str(xi_mp),
        "xi_abs": _mp_str(abs(xi_mp)),
        "theta": _mp_str(theta),
        "cos_theta": _mp_str(cos_theta),
        "trace_samples": [asdict(sample) for sample in trace_samples],
    }


def _mod2_negative_frequency_branch(rho_minus: mp.mpf) -> Dict[str, object]:
    a = sp.Symbol("a")
    cubic = sp.Poly(59 * a**3 - 59 * a**2 + 15 * a + 2, a)
    roots = cubic.nroots(n=80, maxsteps=200)
    real_roots = [root for root in roots if abs(sp.im(root)) < sp.Float("1e-40")]
    if len(real_roots) != 1:
        raise RuntimeError("Expected exactly one real root for the alpha_- cubic.")

    alpha_minus = _alpha_from_rho(rho_minus)
    alpha_cubic_root = mp.mpf(str(sp.re(real_roots[0]).evalf(70)))
    residual = 59 * alpha_minus**3 - 59 * alpha_minus**2 + 15 * alpha_minus + 2
    match_gap = abs(alpha_minus - alpha_cubic_root)

    return {
        "cubic": "59*a^3 - 59*a^2 + 15*a + 2",
        "discriminant": str(sp.discriminant(cubic.as_expr(), a)),
        "alpha_minus_from_rho": _mp_str(alpha_minus, 24),
        "alpha_minus_from_cubic_root": _mp_str(alpha_cubic_root, 24),
        "alpha_minus_match_gap": _mp_str(match_gap, 8),
        "alpha_minus_residual": _mp_str(residual, 24),
        "f_at_minus_tenth": str(sp.nsimplify(cubic.as_expr().subs(a, sp.Rational(-1, 10)))),
        "f_at_zero": str(cubic.as_expr().subs(a, 0)),
        "in_physical_interval": bool(0 <= alpha_minus <= mp.mpf("0.5")),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit the xi collision-pressure LDP, median, twist, and parity-trace constants."
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(export_dir() / "xi_real_input_40_collision_ldp_median_twist_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    sqrt5 = sp.sqrt(5)
    alpha_star = (sp.Integer(3) - sqrt5) / 10
    k2 = (6 * sqrt5 - 5) / 125
    k3 = (9 + 10 * sqrt5) / 625
    k4 = (7 + 24 * sqrt5) / 3125

    derived = _derive_theta_inverse_and_rate(k2=k2, k3=k3, k4=k4)

    theta_a1_expected = sp.simplify(1 / k2)
    theta_a2_expected = sp.simplify(-k3 / (2 * k2**3))
    theta_a3_expected = sp.simplify((3 * k3**2 - k2 * k4) / (6 * k2**5))
    rate_q2_expected = sp.simplify(1 / (2 * k2))
    rate_q3_expected = sp.simplify(-k3 / (6 * k2**3))
    rate_q4_expected = sp.simplify((3 * k3**2 - k2 * k4) / (24 * k2**5))
    asymmetry_expected = sp.simplify(-k3 / (3 * k2**3))
    median_shift = sp.simplify(-k3 / (6 * k2))
    median_shift_expected = sp.simplify(-sp.Rational(23, 310) - 52 * sqrt5 / 2325)
    c2 = sp.simplify((2 * sp.pi**2 / 125) * (6 * sqrt5 - 5))
    c4 = sp.simplify((2 * sp.pi**4 / 9375) * (7 + 24 * sqrt5))

    if derived["theta_a1"] != theta_a1_expected:
        raise RuntimeError("Unexpected inverse-series coefficient a1.")
    if derived["theta_a2"] != theta_a2_expected:
        raise RuntimeError("Unexpected inverse-series coefficient a2.")
    if derived["theta_a3"] != theta_a3_expected:
        raise RuntimeError("Unexpected inverse-series coefficient a3.")
    if derived["rate_q2"] != rate_q2_expected:
        raise RuntimeError("Unexpected quadratic rate coefficient.")
    if derived["rate_q3"] != rate_q3_expected:
        raise RuntimeError("Unexpected cubic rate coefficient.")
    if derived["rate_q4"] != rate_q4_expected:
        raise RuntimeError("Unexpected quartic rate coefficient.")
    if sp.simplify(median_shift - median_shift_expected) != 0:
        raise RuntimeError("Unexpected continuous median shift constant.")

    prime_samples = _prime_twist_samples(primes=[5, 7, 11, 17, 31, 61])
    for sample in prime_samples:
        if mp.mpf(sample.scaled_p6_error) >= mp.mpf("8"):
            raise RuntimeError(f"Prime-twist asymptotic error too large at p={sample.p}.")

    parity_data = _parity_trace_samples()
    rho_minus = mp.mpf(parity_data["rho_minus"])
    negative_branch = _mod2_negative_frequency_branch(rho_minus)

    out: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
        "collision_cumulants": {
            "alpha_star": _sp_str(alpha_star),
            "kappa_2": _sp_str(k2),
            "kappa_3": _sp_str(k3),
            "kappa_4": _sp_str(k4),
        },
        "local_legendre_expansion": {
            "theta_inverse_series": _sp_str(derived["theta_inverse"]),
            "rate_series": _sp_str(derived["rate_series"]),
            "quadratic_coeff": _sp_str(rate_q2_expected),
            "cubic_coeff": _sp_str(rate_q3_expected),
            "quartic_coeff": _sp_str(rate_q4_expected),
            "odd_asymmetry_coeff": _sp_str(asymmetry_expected),
        },
        "continuous_edgeworth_median": {
            "shift_exact": _sp_str(median_shift),
            "shift_decimal": str(sp.N(median_shift, 20)),
        },
        "prime_twist_threshold": {
            "c2_exact": _sp_str(c2),
            "c4_exact": _sp_str(c4),
            "samples": [asdict(sample) for sample in prime_samples],
        },
        "mod2_parity_trace": parity_data,
        "mod2_negative_frequency_branch": negative_branch,
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"[xi-real-input-40-collision] wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
