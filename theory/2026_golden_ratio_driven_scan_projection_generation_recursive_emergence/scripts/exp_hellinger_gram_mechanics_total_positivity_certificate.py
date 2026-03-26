#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Certificates for Hellinger-Gram mechanics / total positivity / Toeplitz inverse decay.

This script provides reproducible numerical checks for statements appearing in the
Hellinger-Gram Toeplitz section, including:
  - First-variation identity for S_{1/2}(s) = -log det G(s)
  - Checkerboard sign of G(s)^{-1} under ordered depths
  - Eigenvector sign-change counts (oscillation signature)
  - Cluster conditioning blow-up exponent under s_j = s0 + eps t_j
  - Toeplitz inverse entry decay for equispaced depths
  - Quasi-orthogonality regime: det G ≈ 1 for large separation

Outputs: one JSON certificate under artifacts/export/.
All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import numpy as np

from common_paths import export_dir


def A(delta: mp.mpf) -> mp.mpf:
    d = mp.fabs(delta)
    if d == 0:
        return mp.mpf(1)
    return d / (2 * mp.sinh(d / 2))


def Aprime(delta: mp.mpf) -> mp.mpf:
    if delta == 0:
        return mp.mpf(0)
    return A(delta) * (mp.mpf(1) / delta - mp.mpf("0.5") * mp.coth(delta / 2))


def gram_mp(s: Sequence[mp.mpf]) -> mp.matrix:
    k = len(s)
    G = mp.matrix(k)
    for i in range(k):
        for j in range(k):
            G[i, j] = A(s[i] - s[j])
    return G


def gram_np(s: Sequence[float]) -> np.ndarray:
    s_arr = np.asarray(s, dtype=float)
    k = int(s_arr.size)
    G = np.empty((k, k), dtype=float)
    for i in range(k):
        for j in range(k):
            d = abs(s_arr[i] - s_arr[j])
            if d == 0.0:
                G[i, j] = 1.0
            else:
                G[i, j] = d / (2.0 * np.sinh(d / 2.0))
    return G


def S_mp(s: Sequence[mp.mpf]) -> mp.mpf:
    G = gram_mp(s)
    return -mp.log(mp.det(G))


def grad_formula_mp(s: Sequence[mp.mpf]) -> List[mp.mpf]:
    G = gram_mp(s)
    inv = mp.inverse(G)
    k = len(s)
    out: List[mp.mpf] = []
    for j in range(k):
        sm = mp.mpf(0)
        for k2 in range(k):
            sm += inv[j, k2] * Aprime(s[j] - s[k2])
        out.append(-2 * sm)
    return out


def grad_finite_diff_mp(s: Sequence[mp.mpf], h: mp.mpf) -> List[mp.mpf]:
    k = len(s)
    out: List[mp.mpf] = []
    for j in range(k):
        sp = list(s)
        sm = list(s)
        sp[j] += h
        sm[j] -= h
        out.append((S_mp(sp) - S_mp(sm)) / (2 * h))
    return out


def checkerboard_min(inv: mp.matrix) -> mp.mpf:
    k = inv.rows
    m = None
    for i in range(k):
        for j in range(k):
            v = ((-1) ** (i + j)) * inv[i, j]
            if m is None or v < m:
                m = v
    assert m is not None
    return mp.mpf(m)


def count_sign_changes(v: np.ndarray, tol: float = 1e-12) -> int:
    signs: List[int] = []
    for x in v.tolist():
        if abs(x) <= tol:
            continue
        signs.append(1 if x > 0 else -1)
    if not signs:
        return 0
    return sum(1 for i in range(1, len(signs)) if signs[i] != signs[i - 1])


def toeplitz_inverse_decay(Delta: float, k: int) -> Dict[str, object]:
    G = np.empty((k, k), dtype=float)
    for i in range(k):
        for j in range(k):
            d = abs(i - j) * Delta
            if d == 0.0:
                G[i, j] = 1.0
            else:
                G[i, j] = d / (2.0 * np.sinh(d / 2.0))
    inv = np.linalg.inv(G)
    max_by_d: Dict[int, float] = {}
    for i in range(k):
        for j in range(k):
            d = abs(i - j)
            max_by_d[d] = max(max_by_d.get(d, 0.0), float(abs(inv[i, j])))

    ratios: List[float] = []
    for d in range(5, min(15, k - 2)):
        if max_by_d.get(d, 0.0) > 0.0 and max_by_d.get(d + 1, 0.0) > 0.0:
            ratios.append(max_by_d[d + 1] / max_by_d[d])
    median_ratio = float(np.median(ratios)) if ratios else float("nan")
    inferred_c = float(-np.log(median_ratio)) if (ratios and median_ratio > 0.0) else float("nan")

    return {
        "Delta": str(Delta),
        "k": int(k),
        "max_abs_inv_by_offset": {str(d): v for d, v in sorted(max_by_d.items())},
        "median_ratio_offset_d_to_dplus1_over_d_in_[5,15]": median_ratio,
        "inferred_exponent_c_from_median_ratio": inferred_c,
        "Delta_over_2": float(Delta / 2.0),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate certificates for Hellinger-Gram mechanics / total positivity / Toeplitz inverse decay.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "hellinger_gram_mechanics_total_positivity_certificate.json"),
        help="Output JSON path.",
    )
    parser.add_argument("--mp-dps", type=int, default=90, help="mpmath working precision (decimal digits).")
    args = parser.parse_args()

    mp.mp.dps = int(args.mp_dps)
    h = mp.mpf("1e-6")

    # --- First variation (gradient) ---
    s_grad = [mp.mpf("0.0"), mp.mpf("0.7"), mp.mpf("1.9"), mp.mpf("3.2"), mp.mpf("5.0")]
    g_formula = grad_formula_mp(s_grad)
    g_fd = grad_finite_diff_mp(s_grad, h)
    grad_errs = [mp.fabs(a - b) for a, b in zip(g_formula, g_fd)]
    grad_max_err = max(grad_errs) if grad_errs else mp.mpf(0)

    # --- Checkerboard inverse sign + eigen oscillation signature ---
    s_tp = [mp.mpf("0.0"), mp.mpf("2.0"), mp.mpf("5.0"), mp.mpf("9.0"), mp.mpf("14.0")]
    G_tp = gram_mp(s_tp)
    inv_tp = mp.inverse(G_tp)
    cb_min = checkerboard_min(inv_tp)

    w, V = np.linalg.eigh(gram_np([float(x) for x in s_tp]))
    idx = np.argsort(w)[::-1]
    w = w[idx]
    V = V[:, idx]
    sign_changes = []
    for r in range(V.shape[1]):
        v = V[:, r].copy()
        # Fix global sign for reproducible counting.
        for i in range(v.size):
            if abs(v[i]) > 1e-14:
                if v[i] < 0:
                    v = -v
                break
        sign_changes.append(count_sign_changes(v))

    # --- Cluster conditioning blow-up (cond2) ---
    cluster_rows: List[Dict[str, object]] = []
    for t_list in [
        [mp.mpf("0.0"), mp.mpf("1.0"), mp.mpf("3.0"), mp.mpf("4.0")],
        [mp.mpf("0.0"), mp.mpf("1.0"), mp.mpf("2.0"), mp.mpf("5.0"), mp.mpf("7.0")],
    ]:
        kappa = len(t_list)
        for eps in [mp.mpf("1e-1"), mp.mpf("5e-2"), mp.mpf("2e-2"), mp.mpf("1e-2")]:
            s = [eps * t for t in t_list]
            G = gram_mp(s)
            eigs = mp.eigsy(G)[0]  # eigenvalues
            lam_min = min(eigs)
            lam_max = max(eigs)
            cond2 = lam_max / lam_min
            scaled = cond2 * (eps ** (kappa * (kappa - 1)))
            cluster_rows.append(
                {
                    "kappa": int(kappa),
                    "t": [str(x) for x in t_list],
                    "eps": str(eps),
                    "cond2": mp.nstr(cond2, 25),
                    "cond2_times_eps_pow_k(k-1)": mp.nstr(scaled, 25),
                    "lam_min": mp.nstr(lam_min, 25),
                    "lam_max": mp.nstr(lam_max, 25),
                }
            )

    # --- Quasi-orthogonality: large separation => det ~ 1 ---
    k_qo = 10
    Delta_qo = mp.mpf("8.0")
    s_qo = [Delta_qo * mp.mpf(j) for j in range(k_qo)]
    G_qo = gram_mp(s_qo)
    det_qo = mp.det(G_qo)
    S_qo = -mp.log(det_qo)
    # infinity row-sum of off-diagonal
    row_sums = []
    for i in range(k_qo):
        rs = mp.mpf(0)
        for j in range(k_qo):
            if i == j:
                continue
            rs += mp.fabs(G_qo[i, j])
        row_sums.append(rs)
    qo_row_sum = max(row_sums) if row_sums else mp.mpf(0)

    # --- Two-body potential identity check ---
    V_rows: List[Dict[str, str]] = []
    for Delta in [mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf("6.0")]:
        V_exact = -mp.log(A(Delta))
        V_rhs = Delta / 2 - mp.log(Delta) + mp.log(1 - mp.e ** (-Delta))
        V_rows.append(
            {
                "Delta": str(Delta),
                "V_exact": mp.nstr(V_exact, 30),
                "V_rhs": mp.nstr(V_rhs, 30),
                "abs_err": mp.nstr(mp.fabs(V_exact - V_rhs), 10),
            }
        )

    payload: Dict[str, object] = {
        "script": Path(__file__).name,
        "mp_dps": int(args.mp_dps),
        "first_variation": {
            "s": [str(x) for x in s_grad],
            "h": str(h),
            "grad_formula": [mp.nstr(x, 30) for x in g_formula],
            "grad_finite_diff": [mp.nstr(x, 30) for x in g_fd],
            "max_abs_err": mp.nstr(grad_max_err, 20),
        },
        "checkerboard_inverse_sign": {
            "s": [str(x) for x in s_tp],
            "detG": mp.nstr(mp.det(G_tp), 30),
            "min_{i,j} (-1)^(i+j) (G^{-1})_{ij}": mp.nstr(cb_min, 30),
            "all_positive": bool(cb_min > 0),
        },
        "eigen_oscillation_signature": {
            "s": [str(x) for x in s_tp],
            "eigenvalues_desc": [float(x) for x in w.tolist()],
            "sign_changes_by_rank_desc": [int(x) for x in sign_changes],
        },
        "cluster_conditioning": cluster_rows,
        "toeplitz_inverse_decay": toeplitz_inverse_decay(Delta=1.3, k=40),
        "quasi_orthogonality": {
            "kappa": int(k_qo),
            "Delta_spacing": str(Delta_qo),
            "detG": mp.nstr(det_qo, 30),
            "S=-logdet": mp.nstr(S_qo, 30),
            "max_offdiag_row_sum": mp.nstr(qo_row_sum, 20),
        },
        "two_body_potential_identity": V_rows,
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

