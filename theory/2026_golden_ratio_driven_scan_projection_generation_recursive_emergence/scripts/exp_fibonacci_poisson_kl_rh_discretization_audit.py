#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit identities for the Fibonacci-indexed Poisson--KL certificate chain:
  - Poisson semigroup factorization at Fibonacci times,
  - explicit Fibonacci radius/time conjugacy and asymptotics,
  - reverse-KL decomposition of Jensen-type averages,
  - finite evidence for KL plateau rigidity at Fibonacci times,
  - sequence-level discretization checks for defect conditions.

Output:
  - artifacts/export/fibonacci_poisson_kl_rh_discretization_audit.json
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fib_list(n: int) -> List[int]:
    if n < 0:
        return []
    out = [0, 1]
    for _ in range(2, n + 1):
        out.append(out[-1] + out[-2])
    return out[: n + 1]


def _poisson_kernel(x: mp.mpf, t: mp.mpf) -> mp.mpf:
    return (mp.mpf(1) / mp.pi) * (t / (x * x + t * t))


def _cauchy_density(x: mp.mpf, a: mp.mpf) -> mp.mpf:
    return (mp.mpf(1) / mp.pi) * (a / (x * x + a * a))


def _kl_divergence(p, q) -> mp.mpf:
    # Numerically robust on heavy tails by splitting finite/tail bands.
    def integrand(x):
        px = p(x)
        qx = q(x)
        return px * mp.log(px / qx)

    return mp.quad(integrand, [-mp.inf, -20, -5, 0, 5, 20, mp.inf])


@dataclass(frozen=True)
class FibonacciRadiusRow:
    m: int
    Fm: int
    rho_m: float
    t_of_rho: float
    thickness: float
    thickness_formula: float
    asymptotic_ratio: float


@dataclass(frozen=True)
class AnalyticJensenRow:
    rho: float
    lhs_mean_log_absF: float
    rhs_reverse_kl_minus_half_logZ: float
    abs_error: float


def main() -> None:
    mp.mp.dps = 80
    ok = True

    # ------------------------------------------------------------------
    # 450: Fibonacci-time semigroup factorization via Fourier multiplier.
    # ------------------------------------------------------------------
    fib = _fib_list(22)
    xi_samples = [mp.mpf("0.0"), mp.mpf("0.17"), mp.mpf("1.0"), mp.mpf("3.5"), mp.mpf("7.25")]
    max_factorization_error = mp.mpf("0.0")
    for m in range(1, 19):
        for xi in xi_samples:
            lhs = mp.e ** (-fib[m + 2] * abs(xi))
            rhs = mp.e ** (-fib[m + 1] * abs(xi)) * mp.e ** (-fib[m] * abs(xi))
            err = abs(lhs - rhs)
            if err > max_factorization_error:
                max_factorization_error = err
    semigroup_factorization_ok = max_factorization_error < mp.mpf("1e-40")
    ok = ok and semigroup_factorization_ok

    # ------------------------------------------------------------------
    # 451: explicit radius chain formulas and asymptotics.
    # ------------------------------------------------------------------
    phi = (mp.sqrt(5) + 1) / 2
    radius_rows: List[FibonacciRadiusRow] = []
    max_time_conjugacy_error = mp.mpf("0.0")
    max_thickness_formula_error = mp.mpf("0.0")
    for m in range(1, 21):
        Fm = fib[m]
        rho_m = mp.mpf(Fm) / mp.mpf(Fm + 2)
        t_of_rho = (2 * rho_m) / (1 - rho_m)
        thickness = 1 - rho_m * rho_m
        thickness_formula = 4 * mp.mpf(Fm + 1) / mp.mpf((Fm + 2) ** 2)
        asym_ratio = thickness / (4 * mp.sqrt(5) * (phi ** (-m)))

        err_t = abs(t_of_rho - Fm)
        err_th = abs(thickness - thickness_formula)
        if err_t > max_time_conjugacy_error:
            max_time_conjugacy_error = err_t
        if err_th > max_thickness_formula_error:
            max_thickness_formula_error = err_th

        radius_rows.append(
            FibonacciRadiusRow(
                m=int(m),
                Fm=int(Fm),
                rho_m=float(rho_m),
                t_of_rho=float(t_of_rho),
                thickness=float(thickness),
                thickness_formula=float(thickness_formula),
                asymptotic_ratio=float(asym_ratio),
            )
        )

    fib_radius_formula_ok = (max_time_conjugacy_error < mp.mpf("1e-40")) and (
        max_thickness_formula_error < mp.mpf("1e-40")
    )
    ok = ok and fib_radius_formula_ok

    asym_tail = [r.asymptotic_ratio for r in radius_rows[-6:]]
    asymptotic_tail_mean = sum(asym_tail) / len(asym_tail)
    asymptotic_ratio_near_one = abs(asymptotic_tail_mean - 1.0) < 0.10
    ok = ok and asymptotic_ratio_near_one

    # ------------------------------------------------------------------
    # 452: reverse-KL decomposition.
    # ------------------------------------------------------------------
    # 452.1 discrete exact identity
    mu_weights = [mp.mpf("0.2"), mp.mpf("0.3"), mp.mpf("0.5")]
    f_vals = [mp.mpf("2.0"), mp.mpf("1.5"), mp.mpf("4.0")]
    Z_disc = sum(w * fv for w, fv in zip(mu_weights, f_vals))
    nu_weights = [(w * fv) / Z_disc for w, fv in zip(mu_weights, f_vals)]
    lhs_disc = sum(w * mp.log(w / n) for w, n in zip(mu_weights, nu_weights))
    rhs_disc = mp.log(Z_disc) - sum(w * mp.log(fv) for w, fv in zip(mu_weights, f_vals))
    reverse_kl_identity_discrete_error = abs(lhs_disc - rhs_disc)
    reverse_kl_discrete_ok = reverse_kl_identity_discrete_error < mp.mpf("1e-40")
    ok = ok and reverse_kl_discrete_ok

    # 452.2 analytic-circle specialization
    a = mp.mpf("0.4")
    rho_samples = [mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf("0.8")]
    analytic_rows: List[AnalyticJensenRow] = []
    analytic_max_error = mp.mpf("0.0")
    for rho in rho_samples:
        def F_theta(theta):
            return 1 - a * rho * mp.e ** (1j * theta)

        def f_theta(theta):
            return 1 / (abs(F_theta(theta)) ** 2)

        Z = (1 / (2 * mp.pi)) * mp.quad(f_theta, [-mp.pi, mp.pi])
        mean_log_absF = (1 / (2 * mp.pi)) * mp.quad(lambda th: mp.log(abs(F_theta(th))), [-mp.pi, mp.pi])
        KL_mu_nu = (1 / (2 * mp.pi)) * mp.quad(lambda th: mp.log(Z / f_theta(th)), [-mp.pi, mp.pi])
        rhs = mp.mpf("0.5") * KL_mu_nu - mp.mpf("0.5") * mp.log(Z)
        err = abs(mean_log_absF - rhs)
        if err > analytic_max_error:
            analytic_max_error = err
        analytic_rows.append(
            AnalyticJensenRow(
                rho=float(rho),
                lhs_mean_log_absF=float(mean_log_absF),
                rhs_reverse_kl_minus_half_logZ=float(rhs),
                abs_error=float(err),
            )
        )
    reverse_kl_circle_ok = analytic_max_error < mp.mpf("1e-9")
    ok = ok and reverse_kl_circle_ok

    # ------------------------------------------------------------------
    # 453/454/455 finite evidence via explicit Cauchy mixtures.
    # ------------------------------------------------------------------
    # equilibrium profile (exact fixed point)
    E_eq_vals: List[float] = []
    J_eq_vals: List[float] = []
    # non-equilibrium profile
    E_non_vals: List[float] = []
    J_non_vals: List[float] = []

    fib_times = [1, 2, 3, 5, 8, 13]

    for t_int in fib_times:
        t = mp.mpf(t_int)

        c_t = lambda x: _cauchy_density(x, 1 + t)
        h_eq_t = lambda x: _cauchy_density(x, 1 + t)
        h_non_t = lambda x: mp.mpf("0.55") * _cauchy_density(x, mp.mpf("0.6") + t) + mp.mpf("0.45") * _cauchy_density(
            x, mp.mpf("2.7") + t
        )

        E_eq = _kl_divergence(h_eq_t, c_t)
        E_non = _kl_divergence(h_non_t, c_t)
        J_eq = E_eq + _kl_divergence(c_t, h_eq_t)
        J_non = E_non + _kl_divergence(c_t, h_non_t)

        E_eq_vals.append(float(E_eq))
        E_non_vals.append(float(E_non))
        J_eq_vals.append(float(J_eq))
        J_non_vals.append(float(J_non))

    # monotonicity checks on Fibonacci time grid
    tol_mono = 1e-8
    E_non_monotone = all(E_non_vals[i + 1] <= E_non_vals[i] + tol_mono for i in range(len(E_non_vals) - 1))
    J_non_monotone = all(J_non_vals[i + 1] <= J_non_vals[i] + tol_mono for i in range(len(J_non_vals) - 1))
    eq_zero = max(abs(v) for v in E_eq_vals + J_eq_vals) < 1e-9
    plateau_non_eq_abs_diffs = [abs(E_non_vals[i + 1] - E_non_vals[i]) for i in range(len(E_non_vals) - 1)]
    non_eq_no_platform = min(plateau_non_eq_abs_diffs) > 1e-6
    finite_evidence_platform_rule_ok = eq_zero and non_eq_no_platform
    ok = ok and E_non_monotone and J_non_monotone and finite_evidence_platform_rule_ok

    # ------------------------------------------------------------------
    # 456 sequence-level discretization sanity checks.
    # ------------------------------------------------------------------
    fib_rhos = [mp.mpf(fib[m]) / mp.mpf(fib[m] + 2) for m in range(5, 15)]
    rho_seq = [1 - mp.mpf(2) ** (-n) for n in range(2, 40)]  # monotone to 1

    def n_of_m(rho_target):
        for idx, r in enumerate(rho_seq):
            if r >= rho_target:
                return idx
        return len(rho_seq) - 1

    # monotone transfer check for a synthetic nondecreasing model defect.
    D_mono = lambda r: r**2
    transfer_ok = True
    transfer_rows: List[Dict[str, object]] = []
    for rho_m in fib_rhos:
        idx = n_of_m(rho_m)
        lhs = D_mono(rho_m)
        rhs = D_mono(rho_seq[idx])
        cond = lhs <= rhs + mp.mpf("1e-40")
        transfer_ok = transfer_ok and cond
        transfer_rows.append(
            {
                "rho_m": float(rho_m),
                "rho_n_of_m": float(rho_seq[idx]),
                "D_rho_m": float(lhs),
                "D_rho_n_of_m": float(rhs),
                "inequality_holds": bool(cond),
            }
        )

    # vanishing-equivalence finite models:
    #   model A (zero defect): both sequence conditions hold.
    #   model B (single interior zero r0): both fail for eps_m -> 0.
    D_zero = lambda r: mp.mpf("0.0")
    r0 = mp.mpf("0.5")
    D_single = lambda r: mp.log(r / r0) if r > r0 else mp.mpf("0.0")
    eps_m = [mp.mpf(1) / mp.mpf(k) for k in range(5, 5 + len(fib_rhos))]

    modelA_fib_ok = all(D_zero(r) <= e for r, e in zip(fib_rhos, eps_m))
    modelA_seq_ok = all(D_zero(rho_seq[k]) <= mp.mpf("1.0") / mp.mpf(k + 2) for k in range(10, 25))
    modelB_fib_ok = all(D_single(r) <= e for r, e in zip(fib_rhos, eps_m))
    modelB_seq_ok = all(D_single(rho_seq[k]) <= mp.mpf("1.0") / mp.mpf(k + 2) for k in range(10, 25))
    discretization_models_consistent = modelA_fib_ok and modelA_seq_ok and (not modelB_fib_ok) and (not modelB_seq_ok)
    ok = ok and transfer_ok and discretization_models_consistent

    payload: Dict[str, object] = {
        "ok": bool(ok),
        "checks": {
            "semigroup_factorization_ok": bool(semigroup_factorization_ok),
            "fib_radius_formula_ok": bool(fib_radius_formula_ok),
            "asymptotic_ratio_near_one": bool(asymptotic_ratio_near_one),
            "reverse_kl_discrete_ok": bool(reverse_kl_discrete_ok),
            "reverse_kl_circle_ok": bool(reverse_kl_circle_ok),
            "E_non_monotone_on_fib_times": bool(E_non_monotone),
            "J_non_monotone_on_fib_times": bool(J_non_monotone),
            "finite_evidence_platform_rule_ok": bool(finite_evidence_platform_rule_ok),
            "discretization_transfer_ok": bool(transfer_ok),
            "discretization_models_consistent": bool(discretization_models_consistent),
        },
        "fibonacci_semigroup": {
            "max_multiplier_factorization_error": float(max_factorization_error),
            "xi_samples": [float(v) for v in xi_samples],
        },
        "fibonacci_radius_chain": {
            "rows": [asdict(r) for r in radius_rows],
            "max_time_conjugacy_error": float(max_time_conjugacy_error),
            "max_thickness_formula_error": float(max_thickness_formula_error),
            "asymptotic_tail_mean_ratio": float(asymptotic_tail_mean),
        },
        "reverse_kl_jensen": {
            "discrete_identity_error": float(reverse_kl_identity_discrete_error),
            "analytic_rows": [asdict(r) for r in analytic_rows],
            "analytic_max_error": float(analytic_max_error),
        },
        "kl_platform_finite_evidence": {
            "fib_times": fib_times,
            "E_equilibrium": E_eq_vals,
            "J_equilibrium": J_eq_vals,
            "E_nonequilibrium": E_non_vals,
            "J_nonequilibrium": J_non_vals,
            "plateau_non_eq_abs_diffs": plateau_non_eq_abs_diffs,
        },
        "defect_discretization": {
            "transfer_rows": transfer_rows,
            "modelA_zero_defect": {
                "fib_condition": bool(modelA_fib_ok),
                "generic_sequence_condition": bool(modelA_seq_ok),
            },
            "modelB_single_interior_zero": {
                "fib_condition": bool(modelB_fib_ok),
                "generic_sequence_condition": bool(modelB_seq_ok),
            },
        },
    }

    out_path = export_dir() / "fibonacci_poisson_kl_rh_discretization_audit.json"
    _write_json(out_path, payload)
    print(f"[fibonacci-poisson-kl-rh-discretization] ok={ok} wrote={out_path}", flush=True)

    if not ok:
        raise RuntimeError("Fibonacci/Poisson/KL/RH discretization audit failed.")


if __name__ == "__main__":
    main()

