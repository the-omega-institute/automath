#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Certificates for Gram-volume monotonicity / coherence bound / Toeplitz extrema & free energy.

This script numerically audits several inequalities/asymptotics used in the Hellinger-Gram
Toeplitz section:
  - Gram determinant monotonicity under contractions (T* T <= I)
  - Coherence lower bound: S = -log det(G) >= ||E||_F^2 / (2(1+||E||_2)) for G = I+E, diag(E)=0
  - Nearest-neighbor product upper bound for det(G) built from the Hellinger kernel A
  - Toeplitz symbol extrema: max at theta=0, min at theta=pi, and q_* = exp(-2 pi^2 / Delta)
    scaling for sigma_Delta(pi)
  - Condition number scaling cond ~ (1/8) exp(2 pi^2 / Delta) as Delta -> 0
  - Free-energy density f(Delta) small-Delta expansion:
        f(Delta) = -pi^2/Delta + log(pi^2/Delta) + 2 log 2 - Delta/16 + O(exp(-2 pi^2/Delta))
  - Cluster additivity of log det for widely separated blocks

Outputs: one JSON certificate under artifacts/export/.
All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import numpy as np

from common_paths import export_dir


def A_float(delta: float) -> float:
    d = abs(delta)
    if d == 0.0:
        return 1.0
    return d / (2.0 * math.sinh(d / 2.0))


def sigma_poisson(theta: mp.mpf, Delta: mp.mpf, K: int) -> mp.mpf:
    s = mp.mpf(0)
    for k in range(-K, K + 1):
        x = mp.pi * (theta + 2 * mp.pi * mp.mpf(k)) / Delta
        s += mp.sech(x) ** 2
    return (mp.pi**2 / Delta) * s


def free_energy_numeric(Delta: mp.mpf) -> mp.mpf:
    # f(Delta) = (1/2pi) ∫_{-pi}^{pi} log sigma_Delta(theta) d theta
    K = 5
    f_int = mp.quad(lambda t: mp.log(sigma_poisson(t, Delta, K)), [-mp.pi, -mp.pi / 2, 0, mp.pi / 2, mp.pi])
    return f_int / (2 * mp.pi)


def free_energy_asymp(Delta: mp.mpf) -> mp.mpf:
    return -mp.pi**2 / Delta + mp.log(mp.pi**2 / Delta) + 2 * mp.log(2) - Delta / 16


def random_unitary(n: int, rng: np.random.Generator) -> np.ndarray:
    X = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    Q, R = np.linalg.qr(X)
    # Normalize phases to make Q unitary.
    ph = np.diag(R) / np.abs(np.diag(R))
    return Q * ph.conj()


def gram_from_columns(Psi: np.ndarray) -> np.ndarray:
    return Psi.conj().T @ Psi


def slogdet_posdef(G: np.ndarray) -> float:
    sign, logdet = np.linalg.slogdet(G)
    if sign <= 0:
        raise RuntimeError("expected positive determinant")
    return float(logdet)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate certificates for Gram-volume monotonicity and Toeplitz extrema/free-energy asymptotics.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "hellinger_volume_monotonicity_toeplitz_extrema_free_energy_certificate.json"),
        help="Output JSON path.",
    )
    parser.add_argument("--mp-dps", type=int, default=90, help="mpmath working precision (decimal digits).")
    parser.add_argument("--seed", type=int, default=7, help="Random seed for numpy checks.")
    args = parser.parse_args()

    mp.mp.dps = int(args.mp_dps)
    rng = np.random.default_rng(int(args.seed))

    # --- 401: contraction monotonicity for Gram det ---
    m = 12
    kappa = 6
    Psi = rng.normal(size=(m, kappa)) + 1j * rng.normal(size=(m, kappa))
    # Normalize columns.
    Psi = Psi / np.linalg.norm(Psi, axis=0, keepdims=True)
    G = gram_from_columns(Psi)

    # Build a random contraction T = U diag(scales) U^*
    U = random_unitary(m, rng)
    scales = np.linspace(1.0, 0.2, m)
    T = U @ np.diag(scales) @ U.conj().T
    TPsi = T @ Psi
    GT = gram_from_columns(TPsi)

    # PSD order check via eigenvalues of G - GT.
    eig_min = float(np.min(np.linalg.eigvalsh(G - GT)))
    logdet_G = slogdet_posdef(G)
    logdet_GT = slogdet_posdef(GT)

    # Equality test: isometry on span (use basis vectors -> Gram is I)
    Psi_basis = np.zeros((m, kappa), dtype=complex)
    for j in range(kappa):
        Psi_basis[j, j] = 1.0
    G_basis = gram_from_columns(Psi_basis)
    T_iso = np.diag([1.0] * kappa + [0.3] * (m - kappa)).astype(complex)
    GT_iso = gram_from_columns(T_iso @ Psi_basis)

    # --- 402: coherence lower bound ---
    E = G - np.eye(kappa)
    E_fro2 = float(np.sum(np.abs(E) ** 2))
    E_op = float(np.max(np.abs(np.linalg.eigvalsh(E))))
    S = -(logdet_G)
    bound = E_fro2 / (2.0 * (1.0 + E_op))

    # --- 410: nearest-neighbor product bound for the Hellinger kernel ---
    s_pts = sorted([float(rng.random() * 6.0) for _ in range(10)])
    n = len(s_pts)
    Gs = np.empty((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            Gs[i, j] = A_float(s_pts[i] - s_pts[j])
    detGs = float(np.linalg.det(Gs))
    prod_nn = 1.0
    gaps = []
    for j in range(n - 1):
        Dj = s_pts[j + 1] - s_pts[j]
        gaps.append(Dj)
        prod_nn *= (1.0 - A_float(Dj) ** 2)

    # --- 403/404: Toeplitz symbol extrema and condition number scaling ---
    toeplitz_rows: List[Dict[str, object]] = []
    for Delta_str in ["0.8", "0.6", "0.4", "0.25"]:
        Delta = mp.mpf(Delta_str)
        K = 4
        N = 4001
        thetas = [(-mp.pi) + (2 * mp.pi) * mp.mpf(i) / mp.mpf(N - 1) for i in range(N)]
        vals = [sigma_poisson(th, Delta, K) for th in thetas]
        # find max/min
        imax = max(range(N), key=lambda i: vals[i])
        imin = min(range(N), key=lambda i: vals[i])
        th_max = thetas[imax]
        th_min = thetas[imin]
        sig_max = vals[imax]
        sig_min = vals[imin]

        qstar = mp.e ** (-2 * mp.pi**2 / Delta)
        sig0_pred = (mp.pi**2 / Delta)
        sigpi_pred = (8 * mp.pi**2 / Delta) * qstar
        cond = sig0_pred / sigpi_pred
        cond_pred = (mp.mpf(1) / 8) * mp.e ** (2 * mp.pi**2 / Delta)

        toeplitz_rows.append(
            {
                "Delta": Delta_str,
                "grid_N": int(N),
                "theta_max_arg": mp.nstr(th_max, 20),
                "theta_min_arg": mp.nstr(th_min, 20),
                "sigma_max_grid": mp.nstr(sig_max, 30),
                "sigma_min_grid": mp.nstr(sig_min, 30),
                "sigma(0)_poisson": mp.nstr(sigma_poisson(mp.mpf(0), Delta, K), 30),
                "sigma(pi)_poisson": mp.nstr(sigma_poisson(mp.pi, Delta, K), 30),
                "sigma(0)_pred_pi^2_over_Delta": mp.nstr(sig0_pred, 30),
                "sigma(pi)_pred_8pi^2_over_Delta_times_qstar": mp.nstr(sigpi_pred, 30),
                "sigma(pi)_ratio_to_pred": mp.nstr(sigma_poisson(mp.pi, Delta, K) / sigpi_pred, 20),
                "cond_pred_(1/8)exp(2pi^2/Delta)": mp.nstr(cond_pred, 30),
                "cond_ratio_poisson_to_pred": mp.nstr((sigma_poisson(mp.mpf(0), Delta, K) / sigma_poisson(mp.pi, Delta, K)) / cond_pred, 20),
            }
        )

    # --- 405: free-energy density expansion ---
    f_rows: List[Dict[str, str]] = []
    for Delta_str in ["0.8", "0.6", "0.4"]:
        Delta = mp.mpf(Delta_str)
        fn = free_energy_numeric(Delta)
        fa = free_energy_asymp(Delta)
        f_rows.append(
            {
                "Delta": Delta_str,
                "f_numeric": mp.nstr(fn, 30),
                "f_asymp": mp.nstr(fa, 30),
                "abs_err": mp.nstr(mp.fabs(fn - fa), 12),
            }
        )

    # --- 408: cluster additivity (illustrative scaling) ---
    cluster_rows: List[Dict[str, object]] = []
    for L in [6.0, 8.0, 10.0]:
        s1 = [0.0, 1.0, 2.0]
        s2 = [L + 0.0, L + 1.0]
        s = s1 + s2
        Gfull = np.empty((len(s), len(s)), dtype=float)
        for i in range(len(s)):
            for j in range(len(s)):
                Gfull[i, j] = A_float(s[i] - s[j])
        G1 = Gfull[: len(s1), : len(s1)]
        G2 = Gfull[len(s1) :, len(s1) :]
        logdet_full = slogdet_posdef(Gfull)
        diff = logdet_full - slogdet_posdef(G1) - slogdet_posdef(G2)
        scale = (len(s1) * len(s2)) * (L**2) * math.exp(-L)
        cluster_rows.append(
            {
                "L": L,
                "kappa1": len(s1),
                "kappa2": len(s2),
                "logdet_interaction_term": diff,
                "k1k2_L^2_exp(-L)": scale,
                "ratio_diff_over_scale": (diff / scale) if scale > 0 else None,
            }
        )

    payload: Dict[str, object] = {
        "script": Path(__file__).name,
        "seed": int(args.seed),
        "mp_dps": int(args.mp_dps),
        "contraction_monotonicity": {
            "kappa": int(kappa),
            "ambient_dim": int(m),
            "min_eig_G_minus_GT": eig_min,
            "logdet_G": logdet_G,
            "logdet_GT": logdet_GT,
            "det_monotone_holds": bool(logdet_GT <= logdet_G + 1e-10),
            "basis_case_logdet_G": float(np.linalg.slogdet(G_basis)[1]),
            "basis_case_logdet_GT_iso_on_span": float(np.linalg.slogdet(GT_iso)[1]),
            "basis_case_equal": bool(abs(np.linalg.slogdet(G_basis)[1] - np.linalg.slogdet(GT_iso)[1]) <= 1e-12),
        },
        "coherence_lower_bound": {
            "S=-logdet(G)": S,
            "E_fro2": E_fro2,
            "E_op": E_op,
            "bound": bound,
            "bound_holds": bool(S + 1e-12 >= bound),
        },
        "nearest_neighbor_product_bound": {
            "s_points": [round(x, 8) for x in s_pts],
            "gaps": [round(x, 8) for x in gaps],
            "detG": detGs,
            "prod_{j}(1-A(gap_j)^2)": prod_nn,
            "det_le_prod": bool(detGs <= prod_nn + 1e-12),
        },
        "toeplitz_symbol_extrema_and_cond": toeplitz_rows,
        "free_energy_density_small_Delta": f_rows,
        "cluster_additivity_scaling": cluster_rows,
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

