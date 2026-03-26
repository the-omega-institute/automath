#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: Pick--Poisson Gram homothetic spectrum and ledger under phi_m.

This script numerically audits the exact structural identities proved in:
  - con:xi-terminal-pick-poisson-homothetic-spectrum-scaling
  - con:xi-terminal-pick-poisson-spectral-function-renormalization
  - con:xi-terminal-pick-poisson-schur-ledger-homothetic-scaling
  - con:xi-terminal-pick-poisson-characteristic-homogeneity-pde
  - prop:xi-pick-poisson-cross-energy-exp-bound

Outputs:
  - artifacts/export/xi_pick_poisson_phi_m_homothetic_spectrum_ledger_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def cayley(z: complex) -> complex:
    # C(z) = (z - i)/(z + i)
    return (z - 1j) / (z + 1j)


def inv_cayley(w: complex) -> complex:
    # C^{-1}(w) = i (1+w)/(1-w)
    return 1j * (1 + w) / (1 - w)


def phi_m(w: complex, m: float) -> complex:
    return cayley(m * inv_cayley(w))


def rho(a: complex, b: complex) -> float:
    return abs((a - b) / (1 - np.conjugate(b) * a))


def d_hyp(a: complex, b: complex) -> float:
    r = rho(a, b)
    # d = 2 artanh(r) = log((1+r)/(1-r))
    if r >= 1:
        return float("inf")
    return float(math.log((1 + r) / (1 - r)))


def pick_poisson_gram(a: List[complex]) -> np.ndarray:
    k = len(a)
    P = np.zeros((k, k), dtype=np.complex128)
    for j in range(k):
        aj = a[j]
        for k2 in range(k):
            ak = a[k2]
            num = (1 - abs(aj) ** 2) * (1 - abs(ak) ** 2)
            den = (1 + np.conjugate(aj)) * (1 + ak) * (1 - np.conjugate(aj) * ak)
            P[j, k2] = num / den
    # Hermitian symmetrization to remove tiny numerical asymmetry
    return (P + P.conjugate().T) / 2


def principal_minor(P: np.ndarray, idx: Tuple[int, ...]) -> float:
    if not idx:
        return 1.0
    M = P[np.ix_(idx, idx)]
    return float(np.linalg.det(M).real)


def Z_r(P: np.ndarray, r: int) -> float:
    from itertools import combinations

    k = P.shape[0]
    s = 0.0
    for idx in combinations(range(k), r):
        s += principal_minor(P, idx)
    return float(s)


def schur_pi(P: np.ndarray) -> List[float]:
    # pi_r = det(P^{(r)}) / det(P^{(r-1)})
    pis: List[float] = []
    det_prev = 1.0
    for r in range(1, P.shape[0] + 1):
        det_r = float(np.linalg.det(P[:r, :r]).real)
        pis.append(det_r / det_prev)
        det_prev = det_r
    return pis


def rel_err(a: float, b: float) -> float:
    denom = max(1.0, abs(a), abs(b))
    return abs(a - b) / denom


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Pick--Poisson phi_m homothetic spectrum and ledger identities.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_pick_poisson_phi_m_homothetic_spectrum_ledger_audit.json"),
        help="Output JSON path.",
    )
    parser.add_argument("--m", type=float, default=3.0, help="Homothety parameter m>0.")
    parser.add_argument("--z", type=float, default=0.7, help="Test parameter z for Psi(z,m)=det(I-zP(m)).")
    args = parser.parse_args()

    m = float(args.m)
    z = float(args.z)

    # Deterministic configuration (inside unit disk, away from -1).
    a = [
        0.22 + 0.11j,
        -0.31 + 0.19j,
        0.17 - 0.23j,
        -0.08 - 0.27j,
    ]
    a_m = [phi_m(w, m) for w in a]

    P = pick_poisson_gram(a)
    Pm = pick_poisson_gram(a_m)

    # Spectrum scaling audit: Spec(Pm) ≈ m^{-1} Spec(P).
    evals = np.sort(np.linalg.eigvalsh(P).real)
    evals_m = np.sort(np.linalg.eigvalsh(Pm).real)
    spec_scale_err = float(np.max(np.abs(evals_m - (evals / m))))

    # Characteristic polynomial scaling audit by point evaluation.
    # chi_{Pm}(λ) ?= m^{-k} chi_P(mλ)
    k = P.shape[0]
    test_lams = [0.1, 0.3, 1.1]
    charpoly_eval_errs = []
    for lam in test_lams:
        lhs = float(np.linalg.det(lam * np.eye(k) - Pm).real)
        rhs = float((m ** (-k)) * np.linalg.det((m * lam) * np.eye(k) - P).real)
        charpoly_eval_errs.append(rel_err(lhs, rhs))

    # Z_r scaling audit: Z_r(Pm) ?= m^{-r} Z_r(P)
    Z_errs: Dict[str, float] = {}
    for r in range(0, k + 1):
        zr = Z_r(P, r)
        zrm = Z_r(Pm, r)
        Z_errs[f"Z_{r}"] = rel_err(zrm, zr / (m**r))

    # Determinant and trace scaling audit.
    detP = float(np.linalg.det(P).real)
    detPm = float(np.linalg.det(Pm).real)
    trP = float(np.trace(P).real)
    trPm = float(np.trace(Pm).real)
    det_scale_err = rel_err(detPm, detP / (m**k))
    tr_scale_err = rel_err(trPm, trP / m)

    # Ledger (Schur pi_r) scaling audit.
    pi = schur_pi(P)
    pim = schur_pi(Pm)
    pi_err = float(np.max([rel_err(pim[i], pi[i] / m) for i in range(k)]))

    # Psi identity audit: det(I - z P(m)) = det(I - (z/m) P)
    psi_lhs = float(np.linalg.det(np.eye(k) - z * Pm).real)
    psi_rhs = float(np.linalg.det(np.eye(k) - (z / m) * P).real)
    psi_err = rel_err(psi_lhs, psi_rhs)

    # Cross-energy exponential bound: construct two clusters and evaluate.
    A = [0.55 + 0.05j, 0.45 - 0.07j]
    B = [-0.55 + 0.04j, -0.42 - 0.06j]
    L = min(d_hyp(x, y) for x in A for y in B)
    cross = 2.0 * sum(-math.log(rho(x, y)) for x in A for y in B)
    bound = 8.0 * len(A) * len(B) * math.exp(-L)
    cross_bound_ok = bool((L >= math.log(2.0) - 1e-12) and (cross <= bound + 1e-10) and (cross >= -1e-12))

    payload: Dict[str, object] = {
        "meta": {"script": Path(__file__).name, "m": m, "z": z},
        "configuration": {"kappa": k, "a": [complex(w) for w in a], "a_m": [complex(w) for w in a_m]},
        "checks": {
            "spectrum_scaling_max_abs_err": spec_scale_err,
            "charpoly_pointwise_rel_errs": charpoly_eval_errs,
            "Z_r_scaling_rel_errs": Z_errs,
            "det_scaling_rel_err": det_scale_err,
            "tr_scaling_rel_err": tr_scale_err,
            "schur_pi_scaling_max_rel_err": pi_err,
            "psi_identity_rel_err": psi_err,
            "cross_energy": {"L": L, "cross": cross, "bound": bound, "ok": cross_bound_ok},
        },
        "values": {
            "detP": detP,
            "detPm": detPm,
            "trP": trP,
            "trPm": trPm,
            "evals": evals.tolist(),
            "evals_m": evals_m.tolist(),
            "pi": pi,
            "pi_m": pim,
            "psi_lhs": psi_lhs,
            "psi_rhs": psi_rhs,
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)

    # JSON doesn't support complex; stringify those fields explicitly.
    payload["configuration"]["a"] = [str(w) for w in a]
    payload["configuration"]["a_m"] = [str(w) for w in a_m]

    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-pick-poisson-phi_m-audit] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

