#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit a Jensen/repulsion/blind-spot/Fourier-Prony packet.

This script provides a small deterministic audit for:
1. The log-radius Jensen potential representation and the piecewise power-law
   form of the repulsion radius in a finite zero sample.
2. The finite-radius blind-spot construction for Jensen certificates.
3. The unit-step Fourier-Prony linearization of a finite comoving defect
   profile, including Hankel nondegeneracy and exact recovery from 2N samples.
"""

from __future__ import annotations

import json
import math
from itertools import permutations
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir


def _sp_str(expr: sp.Expr) -> str:
    return str(sp.simplify(expr))


def _mp_str(x: mp.mpf | mp.mpc, nd: int = 18) -> str:
    if isinstance(x, mp.mpc):
        sign = "+" if x.imag >= 0 else ""
        return f"{mp.nstr(x.real, nd)}{sign}{mp.nstr(x.imag, nd)}j"
    return mp.nstr(x, nd)


def _jensen_piecewise_audit() -> Dict[str, object]:
    radius_levels = [sp.Rational(1, 5), sp.Rational(1, 2), sp.Rational(4, 5)]
    multiplicities = [2, 1, 3]
    cumulative = []
    total = 0
    for mult in multiplicities:
        total += int(mult)
        cumulative.append(total)

    sample_rhos = [
        sp.Rational(1, 10),
        sp.Rational(2, 5),
        sp.Rational(3, 5),
        sp.Rational(9, 10),
    ]

    interval_data: List[Dict[str, object]] = []
    left_endpoints = [sp.Integer(0)] + radius_levels
    right_endpoints = radius_levels + [sp.Integer(1)]
    for j, (left, right) in enumerate(zip(left_endpoints, right_endpoints)):
        exponent = 1 - (cumulative[j - 1] if j > 0 else 0)
        prefactor = sp.Integer(1)
        for i in range(j):
            prefactor *= radius_levels[i] ** multiplicities[i]
        interval_data.append(
            {
                "interval": f"({left}, {right})",
                "log_slope": int(exponent),
                "prefactor": _sp_str(prefactor),
                "power_law": f"rho**({exponent}) * ({_sp_str(prefactor)})",
            }
        )

    checks: List[Dict[str, object]] = []
    for rho in sample_rhos:
        u = sp.log(rho)
        D_sum = sp.Integer(0)
        D_potential = sp.Integer(0)
        count = 0
        interval_index = 0
        for idx, (r0, mult) in enumerate(zip(radius_levels, multiplicities), start=1):
            if rho > r0:
                D_sum += mult * sp.log(rho / r0)
                D_potential += mult * (u - sp.log(r0))
                count += int(mult)
                interval_index = idx

        prefactor = sp.Integer(1)
        for i in range(interval_index):
            prefactor *= radius_levels[i] ** multiplicities[i]
        power_law = sp.simplify(rho ** (1 - count) * prefactor)
        r_star = sp.simplify(rho * sp.exp(-D_sum))

        checks.append(
            {
                "rho": _sp_str(rho),
                "u": _sp_str(u),
                "zero_count": count,
                "jensen_sum": _sp_str(D_sum),
                "potential_formula": _sp_str(D_potential),
                "potential_match": bool(sp.simplify(D_sum - D_potential) == 0),
                "repulsion_radius": _sp_str(r_star),
                "power_law_value": _sp_str(power_law),
                "power_law_match": bool(sp.simplify(r_star - power_law) == 0),
            }
        )

    return {
        "radius_levels": [_sp_str(r) for r in radius_levels],
        "multiplicities": multiplicities,
        "interval_data": interval_data,
        "sample_checks": checks,
    }


def _finite_sampling_blindspot() -> Dict[str, object]:
    sample_radii = [mp.mpf("0.2"), mp.mpf("0.4"), mp.mpf("0.7")]
    hidden_zero_radius = mp.mpf("0.9")

    def defect_from_zero_radii(rho: mp.mpf, zero_radii: Sequence[mp.mpf]) -> mp.mpf:
        total = mp.mpf("0")
        for r in zero_radii:
            if r < rho:
                total += mp.log(rho / r)
        return total

    b0 = [defect_from_zero_radii(rho, []) for rho in sample_radii]
    b1 = [defect_from_zero_radii(rho, [hidden_zero_radius]) for rho in sample_radii]

    return {
        "sample_radii": [_mp_str(rho, 8) for rho in sample_radii],
        "hidden_zero_radius": _mp_str(hidden_zero_radius, 8),
        "certificate_B0": [_mp_str(v, 8) for v in b0],
        "certificate_B1": [_mp_str(v, 8) for v in b1],
        "same_certificate": all(abs(x - y) < mp.mpf("1e-40") for x, y in zip(b0, b1)),
    }


def _comoving_fourier_prony_audit() -> Dict[str, object]:
    mp.mp.dps = 80

    atoms: Sequence[Tuple[mp.mpf, mp.mpf, int]] = [
        (mp.mpf("-0.7"), mp.mpf("0.2"), 1),
        (mp.mpf("0.45"), mp.mpf("0.35"), 2),
        (mp.mpf("1.1"), mp.mpf("0.15"), 1),
    ]
    N = len(atoms)

    def h_profile(x: mp.mpf) -> mp.mpf:
        total = mp.mpf("0")
        for gamma, delta, mult in atoms:
            total += mp.mpf(mult) * (4 * delta) / ((gamma - x) ** 2 + (1 + delta) ** 2)
        return total

    def hhat_formula(xi: mp.mpf) -> mp.mpc:
        total = mp.mpc("0")
        for gamma, delta, mult in atoms:
            coeff = 4 * mp.pi * mp.mpf(mult) * delta / (1 + delta)
            total += coeff * mp.e ** (-(1 + delta) * abs(xi)) * mp.e ** (-1j * gamma * xi)
        return total

    xi_checks = [mp.mpf("0"), mp.mpf("0.5"), mp.mpf("1.0"), mp.mpf("2.0")]
    fourier_checks: List[Dict[str, object]] = []
    max_fourier_error = mp.mpf("0")
    for xi in xi_checks:
        numeric = mp.quad(lambda x: h_profile(x) * mp.e ** (-1j * xi * x), [-mp.inf, mp.inf])
        closed = hhat_formula(xi)
        err = abs(numeric - closed)
        max_fourier_error = max(max_fourier_error, err)
        fourier_checks.append(
            {
                "xi": _mp_str(xi, 8),
                "numeric": _mp_str(numeric, 20),
                "closed_form": _mp_str(closed, 20),
                "abs_error": _mp_str(err, 8),
            }
        )

    lambdas = [mp.e ** (-(1 + delta) - 1j * gamma) for gamma, delta, _ in atoms]
    coeffs = [4 * mp.pi * mp.mpf(mult) * delta / (1 + delta) for gamma, delta, mult in atoms]
    samples = [sum(coeffs[j] * lambdas[j] ** n for j in range(N)) for n in range(2 * N)]

    hankel = mp.matrix(N)
    for i in range(N):
        for j in range(N):
            hankel[i, j] = samples[i + j]
    hankel_det = mp.det(hankel)

    rhs = mp.matrix(N, 1)
    for i in range(N):
        rhs[i] = -samples[N + i]
    coeff_vec = mp.lu_solve(hankel, rhs)
    q_coeffs = [coeff_vec[i] for i in range(N)] + [mp.mpf("1")]
    poly_desc = [q_coeffs[-1]] + list(reversed(q_coeffs[:-1]))
    recovered_lambdas = list(mp.polyroots(poly_desc, maxsteps=300))

    vandermonde = mp.matrix(N)
    for i in range(N):
        for j in range(N):
            vandermonde[i, j] = recovered_lambdas[j] ** i
    sample_col = mp.matrix(N, 1)
    for i in range(N):
        sample_col[i] = samples[i]
    recovered_coeffs_col = mp.lu_solve(vandermonde, sample_col)
    recovered_coeffs = [recovered_coeffs_col[i] for i in range(N)]

    best_perm = min(
        permutations(range(N)),
        key=lambda perm: sum(abs(lambdas[i] - recovered_lambdas[perm[i]]) for i in range(N)),
    )
    matched_lambdas = [recovered_lambdas[best_perm[i]] for i in range(N)]
    matched_coeffs = [recovered_coeffs[best_perm[i]] for i in range(N)]

    lambda_max_error = max(abs(lambdas[i] - matched_lambdas[i]) for i in range(N))
    coeff_max_error = max(abs(coeffs[i] - matched_coeffs[i]) for i in range(N))

    recurrence_residuals: List[str] = []
    for n in range(3):
        residual = mp.mpc("0")
        for ell, q in enumerate(q_coeffs):
            residual += q * sum(coeffs[j] * lambdas[j] ** (n + ell) for j in range(N))
        recurrence_residuals.append(_mp_str(residual, 12))

    decoded_parameters: List[Dict[str, object]] = []
    for lam, coeff in zip(matched_lambdas, matched_coeffs):
        delta = -mp.log(abs(lam)) - 1
        gamma_mod_2pi = -mp.arg(lam)
        multiplicity = coeff * (1 + delta) / (4 * mp.pi * delta)
        decoded_parameters.append(
            {
                "lambda": _mp_str(lam, 20),
                "delta": _mp_str(delta, 16),
                "gamma_mod_2pi": _mp_str(gamma_mod_2pi, 16),
                "multiplicity": _mp_str(multiplicity, 16),
            }
        )

    return {
        "atoms": [
            {
                "gamma": _mp_str(gamma, 8),
                "delta": _mp_str(delta, 8),
                "multiplicity": int(mult),
                "lambda": _mp_str(lam, 20),
                "coefficient": _mp_str(coeff, 20),
            }
            for (gamma, delta, mult), lam, coeff in zip(atoms, lambdas, coeffs)
        ],
        "fourier_checks": fourier_checks,
        "max_fourier_abs_error": _mp_str(max_fourier_error, 8),
        "samples_0_to_2N_minus_1": [_mp_str(v, 20) for v in samples],
        "leading_hankel_det": _mp_str(hankel_det, 20),
        "annihilating_polynomial_coeffs_low_to_high": [_mp_str(v, 20) for v in q_coeffs],
        "recovered_lambda_max_error": _mp_str(lambda_max_error, 8),
        "recovered_coefficient_max_error": _mp_str(coeff_max_error, 8),
        "recurrence_residuals": recurrence_residuals,
        "decoded_parameters": decoded_parameters,
    }


def main() -> None:
    out = {
        "jensen_piecewise_audit": _jensen_piecewise_audit(),
        "finite_sampling_blindspot": _finite_sampling_blindspot(),
        "comoving_fourier_prony_audit": _comoving_fourier_prony_audit(),
    }
    out_path = export_dir() / "xi_jensen_comoving_prony_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[write] {out_path}")


if __name__ == "__main__":
    main()
