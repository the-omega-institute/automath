#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit max-entropy Markov kernel and symmetrized spectrum for diagonal-rate couplings.

This script is English-only by repository convention.

We consider the optimization defining R_w(delta):
  R_w(delta) = inf { I_P(X;Y) : P_X=P_Y=w, P(X=Y) >= 1-delta }.
For delta < 1 - sum_x w(x)^2, the unique optimizer has the exponential-family form
  P*(x,y) = u_x u_y (1 + kappa 1_{x=y}) / Z,
with kappa > 0 and u_x > 0. The induced Markov kernel is K*(y|x)=P*(x,y)/w(x).

This audit script numerically (finite-dimensional, no black-box solvers) verifies:
  - The coupling constraints, diagonal mass, and KL / entropy identities.
  - The symmetrization S = D^{-1/2} P* D^{-1/2} is symmetric PSD and shares spectrum with K*.
  - The "diagonal + rank-one" secular determinant identity for S.
  - The rank-one refresh decomposition of K*, the 1D collapse of det(I-zK*), and the closed form det'(I-K*).
  - The small-distortion (delta -> 0) slope of 1-lambda_2(delta) matches the
    predicted coefficient nu_2(w) / (A_{1/2}(w)^2 - 1), where nu_2(w) is the
    smallest positive eigenvalue of L_{1/2}(w)=A_{1/2}(w)diag(w^{-1/2})-11^T.
  - The critical-line Laplacian L_w=L_{1/2}(w)/(A_{1/2}(w)^2-1), its pseudodeterminant,
    the explicit Xi_w(s)=det'(L_w+sI), and the zeta-scaling limit from det(I-e^{-s delta}K*).

Outputs:
  - artifacts/export/pom_diagonal_rate_maxent_markov_spectrum_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_normalize_prob(w: np.ndarray) -> np.ndarray:
    w = np.asarray(w, dtype=float)
    if np.any(w <= 0):
        raise ValueError("w must be strictly positive.")
    s = float(w.sum())
    if not (s > 0):
        raise ValueError("w sum must be positive.")
    return w / s


def _entropy(p: np.ndarray) -> float:
    p = np.asarray(p, dtype=float)
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


def _mutual_information(P: np.ndarray, w: np.ndarray) -> float:
    # I(P)=sum_{x,y} P(x,y) log(P(x,y)/(w(x)w(y))).
    w = np.asarray(w, dtype=float)
    P = np.asarray(P, dtype=float)
    denom = w[:, None] * w[None, :]
    mask = P > 0
    return float((P[mask] * np.log(P[mask] / denom[mask])).sum())


@dataclass(frozen=True)
class OptimalCoupling:
    w: np.ndarray
    delta: float
    kappa: float
    u: np.ndarray
    Z: float
    P: np.ndarray
    K: np.ndarray
    S: np.ndarray


def _u_from_kappa_Z(w: np.ndarray, kappa: float, Z: float) -> np.ndarray:
    # Solve u_x(1 + kappa u_x) = Z w_x with positive root.
    # Stable form: u = (2 Z w) / (sqrt(1 + 4 kappa Z w) + 1).
    t = np.sqrt(1.0 + 4.0 * kappa * Z * w)
    u = (2.0 * Z * w) / (t + 1.0)
    return u


def _solve_Z_sum_u_equals_one(w: np.ndarray, kappa: float, *, rtol: float = 1e-14) -> Tuple[float, np.ndarray]:
    # Fix scale by enforcing A = sum_x u_x = 1.
    if not (kappa >= 0):
        raise ValueError("kappa must be >= 0.")
    if kappa == 0.0:
        # u = w, Z=1
        return 1.0, w.copy()

    def sum_u(Z: float) -> float:
        u = _u_from_kappa_Z(w, kappa, Z)
        return float(u.sum())

    lo = 0.0
    hi = 1.0
    # Expand hi until sum_u(hi) >= 1.
    for _ in range(200):
        if sum_u(hi) >= 1.0:
            break
        hi *= 2.0
    else:
        raise RuntimeError("Failed to bracket Z for sum_u(Z)=1.")

    # Bisection.
    for _ in range(400):
        mid = 0.5 * (lo + hi)
        sm = sum_u(mid)
        if sm < 1.0:
            lo = mid
        else:
            hi = mid
        if hi - lo <= rtol * max(1.0, hi):
            break

    Z = hi
    u = _u_from_kappa_Z(w, kappa, Z)
    # Sanity: sum u close to 1.
    if not math.isfinite(float(u.sum())):
        raise RuntimeError("Non-finite u sum.")
    return float(Z), u


def _diag_mass_from_kappa(w: np.ndarray, kappa: float) -> float:
    Z, u = _solve_Z_sum_u_equals_one(w, kappa)
    P_diag = (1.0 + kappa) * (u**2) / Z
    return float(P_diag.sum())


def _solve_kappa_for_delta(w: np.ndarray, delta: float, *, rtol: float = 1e-12) -> float:
    # Solve diag_mass(kappa) = 1 - delta for delta in (0, 1-p2(w)).
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must be in (0,1).")
    p2 = float((w * w).sum())
    delta0 = 1.0 - p2
    if not (delta < delta0):
        raise ValueError("Need delta < 1 - sum w^2 for active diagonal constraint.")

    target = 1.0 - delta

    # Bracket kappa.
    lo = 0.0
    hi = 1.0
    for _ in range(200):
        if _diag_mass_from_kappa(w, hi) >= target:
            break
        hi *= 2.0
    else:
        raise RuntimeError("Failed to bracket kappa.")

    # Bisection on kappa.
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        pmid = _diag_mass_from_kappa(w, mid)
        if pmid < target:
            lo = mid
        else:
            hi = mid
        if hi - lo <= rtol * max(1.0, hi):
            break

    return float(hi)


def compute_optimal_coupling(w: np.ndarray, delta: float) -> OptimalCoupling:
    w = _safe_normalize_prob(w)
    kappa = _solve_kappa_for_delta(w, delta)
    Z, u = _solve_Z_sum_u_equals_one(w, kappa)

    # Build P*(x,y) = u_x u_y (1 + kappa 1_{x=y}) / Z.
    P = np.outer(u, u) / Z
    P[np.diag_indices_from(P)] = (1.0 + kappa) * (u**2) / Z

    # Markov kernel K(y|x) = P(x,y) / w(x).
    K = P / w[:, None]

    # Symmetrized operator on Euclidean space: S = D^{-1/2} P D^{-1/2}.
    inv_sqrt_w = 1.0 / np.sqrt(w)
    S = (inv_sqrt_w[:, None] * P) * inv_sqrt_w[None, :]

    return OptimalCoupling(w=w, delta=float(delta), kappa=float(kappa), u=u, Z=float(Z), P=P, K=K, S=S)


def _secular_det_identity_error(S: np.ndarray, a: np.ndarray, d: np.ndarray, lam: float) -> float:
    # Compare det(S - lam I) to prod(d-lam) * (1 + sum a^2/(d-lam)).
    n = S.shape[0]
    left = float(np.linalg.det(S - lam * np.eye(n)))
    prod = float(np.prod(d - lam))
    right = prod * float(1.0 + np.sum((a * a) / (d - lam)))
    denom = max(1.0, abs(left), abs(right))
    return abs(left - right) / denom


def _rel_err(a: complex, b: complex) -> float:
    denom = max(1.0, abs(a), abs(b))
    return float(abs(a - b) / denom)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit diagonal-rate maxent Markov kernel spectrum")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    # Test cases (fixed, deterministic).
    test_ws = [
        np.array([0.5, 0.3, 0.2]),
        np.array([0.25, 0.25, 0.25, 0.25]),
        np.array([0.4, 0.35, 0.15, 0.10]),
    ]
    # Use very small deltas to probe the delta->0 slope.
    test_deltas = [1e-6, 5e-7, 2e-7]

    cases: List[Dict[str, object]] = []
    all_ok = True

    for w in test_ws:
        w = _safe_normalize_prob(w)
        n = int(w.size)
        p2 = float((w * w).sum())
        delta0 = 1.0 - p2

        A = float(np.sqrt(w).sum())
        C12 = float(A * A - 1.0)
        ones = np.ones(n)
        sqrt_w = np.sqrt(w)
        L12 = A * np.diag(1.0 / sqrt_w) - np.outer(ones, ones)
        # L12 is PSD with one zero eigenvalue.
        nu = np.linalg.eigvalsh(L12)
        # Smallest positive eigenvalue (tolerate numerical noise).
        nu_pos = [float(x) for x in nu if x > 1e-12]
        nu2 = min(nu_pos) if nu_pos else 0.0
        slope_th = nu2 / C12

        # Critical-line Laplacian: L_w = L12 / C12.
        Lw = L12 / C12
        mu = np.linalg.eigvalsh(Lw)
        mu_pos = np.array([float(x) for x in mu if x > 1e-12], dtype=float)
        pdet_eig = float(np.prod(mu_pos)) if mu_pos.size else 0.0
        pdet_formula = float(A ** (n - 2) / (C12 ** (n - 1) * math.sqrt(float(np.prod(w)))))
        pdet_rel_err = _rel_err(pdet_eig, pdet_formula)

        B = float(np.sum(1.0 / sqrt_w))
        p_minus1 = float(np.sum(1.0 / w))
        tr_formula = float((A * B - n) / C12)
        tr2_formula = float((A * A * p_minus1 - 2.0 * A * B + n * n) / (C12 * C12))
        tr_eig = float(mu.sum())
        tr2_eig = float((mu * mu).sum())
        tr_rel_err = _rel_err(tr_eig, tr_formula)
        tr2_rel_err = _rel_err(tr2_eig, tr2_formula)

        prod_inv_sqrt_w = float(np.prod(1.0 / sqrt_w))

        def xi_formula(s: float) -> float:
            # Xi_w(s) = det'(L_w + sI) with explicit closed form.
            arr = A + (s * C12) * sqrt_w
            total_prod = float(np.prod(arr))
            sum_term = float(np.sum(w / arr))
            pref = prod_inv_sqrt_w / (A * (C12 ** (n - 1)))
            return float(pref * total_prod * sum_term)

        xi_tests = [0.3, 1.0]
        xi_checks: List[Dict[str, object]] = []
        xi_all_ok = True
        for s in xi_tests:
            xi_eig = float(np.prod(mu_pos + float(s)))
            xi_form = float(xi_formula(float(s)))
            rel = _rel_err(xi_eig, xi_form)
            ok = rel <= 5e-10
            xi_all_ok = xi_all_ok and ok
            xi_checks.append({"s": float(s), "xi_eig": xi_eig, "xi_formula": xi_form, "rel_err": rel, "ok": bool(ok)})

        critical_ok = (pdet_rel_err <= 5e-10) and (tr_rel_err <= 5e-10) and (tr2_rel_err <= 5e-10) and xi_all_ok

        case_entry: Dict[str, object] = {
            "w": [float(x) for x in w],
            "n": n,
            "p2": p2,
            "delta0": delta0,
            "A12": A,
            "C12": C12,
            "nu2": nu2,
            "slope_th": slope_th,
            "critical": {
                "pdet_eig": pdet_eig,
                "pdet_formula": pdet_formula,
                "pdet_rel_err": pdet_rel_err,
                "tr_eig": tr_eig,
                "tr_formula": tr_formula,
                "tr_rel_err": tr_rel_err,
                "tr2_eig": tr2_eig,
                "tr2_formula": tr2_formula,
                "tr2_rel_err": tr2_rel_err,
                "xi_tests": xi_checks,
                "ok": bool(critical_ok),
            },
            "deltas": [],
        }

        # Pick deltas safely inside (0,delta0).
        deltas = [d for d in test_deltas if d < 0.2 * delta0]
        if not deltas:
            deltas = [min(1e-5, 0.1 * delta0)]

        for delta in deltas:
            oc = compute_optimal_coupling(w, delta)

            # Basic coupling checks.
            PX = oc.P.sum(axis=1)
            PY = oc.P.sum(axis=0)
            diag_mass = float(np.trace(oc.P))
            coupling_ok = (
                np.allclose(PX, oc.w, rtol=0, atol=5e-11)
                and np.allclose(PY, oc.w, rtol=0, atol=5e-11)
                and abs(diag_mass - (1.0 - delta)) <= 5e-10
                and abs(float(oc.P.sum()) - 1.0) <= 5e-11
            )

            # Entropy-rate / mutual-information identity: H(w)-h(K)=I_P.
            Hw = _entropy(oc.w)
            row_ent = float(sum(oc.w[i] * _entropy(oc.K[i, :]) for i in range(n)))
            I = _mutual_information(oc.P, oc.w)
            info_ok = abs((Hw - row_ent) - I) <= 5e-10

            # Symmetrization similarity: spectra of S and K match (within tol).
            eigS = np.linalg.eigvalsh(oc.S)
            eigK = np.linalg.eigvals(oc.K)  # K is similar to S, so should be real.
            eigK = np.sort(np.real_if_close(eigK, tol=1e3).real)
            eigS_sorted = np.sort(eigS)
            spec_ok = np.allclose(eigK, eigS_sorted, rtol=0, atol=5e-9)

            # Nonnegativity / Markov bounds.
            bounds_ok = (eigS.min() >= -5e-10) and (eigS.max() <= 1.0 + 5e-10)

            # Secular determinant identity for a few lambda values.
            a = oc.u / np.sqrt(oc.w) / math.sqrt(oc.Z)  # normalize so S = a a^T + kappa diag(a^2)
            # With our P = outer(u,u)/Z + kappa diag(u^2)/Z, S = outer(a,a) + kappa diag(a^2).
            d = oc.kappa * (a * a)
            det_errs = []
            for lam in (0.0, 0.123, 0.777):
                # Avoid poles.
                if np.min(np.abs(d - lam)) < 1e-10:
                    continue
                det_errs.append(_secular_det_identity_error(oc.S, a, d, lam))
            det_ok = (max(det_errs) if det_errs else 0.0) <= 5e-8

            # Small-distortion slope estimate for lambda2.
            eig_desc = np.sort(eigS)[::-1]
            lam2 = float(eig_desc[1]) if n >= 2 else 1.0
            slope_est = (1.0 - lam2) / delta
            slope_rel_err = abs(slope_est - slope_th) / max(1e-12, abs(slope_th))
            # Numerical slope check (asymptotic, so allow a modest tolerance).
            slope_ok = slope_rel_err <= 5e-2

            # Rank-one refresh decomposition for K.
            A_u = float(oc.u.sum())
            pi = oc.u / A_u
            r = A_u / (A_u + oc.kappa * oc.u)
            K_refresh = np.outer(r, pi)
            K_refresh[np.diag_indices_from(K_refresh)] += (1.0 - r)
            refresh_err_max = float(np.max(np.abs(oc.K - K_refresh)))
            refresh_ok = refresh_err_max <= 5e-10

            # Determinant collapse for det(I - zK) (compare via spectrum).
            z_tests = [0.0, 0.3, -0.6, 0.9]
            det_collapse_errs: List[float] = []
            for z in z_tests:
                left_det = float(np.prod(1.0 - float(z) * eigS_sorted))
                diag_fac = float(np.prod(1.0 - float(z) * (1.0 - r)))
                denom = 1.0 - float(z) * (1.0 - r)
                secular = float(1.0 - float(z) * float(np.sum(pi * r / denom)))
                right_det = diag_fac * secular
                det_collapse_errs.append(_rel_err(left_det, right_det))
            det_collapse_err_max = float(max(det_collapse_errs) if det_collapse_errs else 0.0)
            det_collapse_ok = det_collapse_err_max <= 5e-8

            # Reduced determinant det'(I-K) closed form.
            detprime_eig = float(np.prod(1.0 - eig_desc[1:]))
            detprime_formula = float(np.prod(r) * float(np.sum(pi / r)))
            detprime_rel_err = _rel_err(detprime_eig, detprime_formula)
            detprime_ok = detprime_rel_err <= 5e-8

            # First-order critical Laplacian expansion: (I-S)/delta -> Lw.
            approx_Lw = (np.eye(n) - oc.S) / float(delta)
            Lw_first_order_rel_err = float(
                np.linalg.norm(approx_Lw - Lw, ord="fro") / max(1e-12, np.linalg.norm(Lw, ord="fro"))
            )
            Lw_first_order_ok = Lw_first_order_rel_err <= 5e-4

            # Zeta-scaling limit from det(I - e^{-s delta}K) (computed via S spectrum).
            s_scale = 0.7
            z_scale = math.exp(-s_scale * float(delta))
            det_scale = float(np.prod(1.0 - z_scale * eigS_sorted))
            scaled = det_scale / (1.0 - z_scale) / (float(delta) ** (n - 1))
            xi_target = float(np.prod(mu_pos + float(s_scale)))
            xi_scaling_rel_err = _rel_err(scaled, xi_target)
            xi_scaling_ok = xi_scaling_rel_err <= 2e-2

            this_ok = (
                critical_ok
                and coupling_ok
                and info_ok
                and spec_ok
                and bounds_ok
                and det_ok
                and refresh_ok
                and det_collapse_ok
                and detprime_ok
                and Lw_first_order_ok
                and slope_ok
                and xi_scaling_ok
            )
            all_ok = all_ok and this_ok

            case_entry["deltas"].append(
                {
                    "delta": float(delta),
                    "kappa": float(oc.kappa),
                    "Z": float(oc.Z),
                    "diag_mass": float(diag_mass),
                    "H_w": float(Hw),
                    "h_K": float(row_ent),
                    "I": float(I),
                    "lambda2": float(lam2),
                    "slope_est": float(slope_est),
                    "slope_rel_err": float(slope_rel_err),
                    "slope_ok": bool(slope_ok),
                    "det_err_max": float(max(det_errs) if det_errs else 0.0),
                    "refresh_err_max": float(refresh_err_max),
                    "refresh_ok": bool(refresh_ok),
                    "det_collapse_err_max": float(det_collapse_err_max),
                    "det_collapse_ok": bool(det_collapse_ok),
                    "detprime_eig": float(detprime_eig),
                    "detprime_formula": float(detprime_formula),
                    "detprime_rel_err": float(detprime_rel_err),
                    "detprime_ok": bool(detprime_ok),
                    "Lw_first_order_rel_err": float(Lw_first_order_rel_err),
                    "Lw_first_order_ok": bool(Lw_first_order_ok),
                    "xi_scaling_s": float(s_scale),
                    "xi_scaling_est": float(scaled),
                    "xi_scaling_target": float(xi_target),
                    "xi_scaling_rel_err": float(xi_scaling_rel_err),
                    "xi_scaling_ok": bool(xi_scaling_ok),
                    "ok": bool(this_ok),
                }
            )

        cases.append(case_entry)

    payload: Dict[str, object] = {
        "ok": bool(all_ok),
        "cases": cases,
    }

    if not args.no_output:
        _write_json(export_dir() / "pom_diagonal_rate_maxent_markov_spectrum_audit.json", payload)

    if not all_ok:
        raise SystemExit("Audit failed: some checks did not pass.")


if __name__ == "__main__":
    main()

