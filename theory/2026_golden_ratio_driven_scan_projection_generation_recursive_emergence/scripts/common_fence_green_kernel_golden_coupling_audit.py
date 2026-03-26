#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Golden-coupling (t=1) / Fibonacci / Fisher-zero audits for L_k = K_k^{-1},
where K_k(i,j)=min(i,j).

This module is invoked by exp_fence_order_poly_spectral_audit.py so the checks run
inside the existing run_all.py pipeline without adding new steps.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir


def phi() -> float:
    return float((1.0 + math.sqrt(5.0)) / 2.0)


def fib(n: int) -> int:
    """Fibonacci with F_0=0, F_1=1."""
    n = int(n)
    if n < 0:
        raise ValueError("n must be nonnegative")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return int(a)


def eta_from_t(t: float) -> float:
    if t <= 0.0:
        raise ValueError("Require t>0")
    return float(math.asinh(math.sqrt(float(t) / 4.0)))


def q_from_eta(eta: float) -> float:
    return float(math.exp(-2.0 * float(eta)))


def mu_eigenvalues(k: int) -> np.ndarray:
    """mu_p=4 sin^2((2p-1)pi/(4k+2)), p=1..k (unsorted)."""
    k = int(k)
    p = np.arange(1, k + 1, dtype=float)
    phi = (2.0 * p - 1.0) * math.pi / (4.0 * k + 2.0)
    return 4.0 * (np.sin(phi) ** 2)


def fisher_zeros(k: int) -> np.ndarray:
    """t_p = -mu_p in (-4,0), ascending."""
    t = -mu_eigenvalues(k)
    t.sort()
    return t


def arcsine_cdf_on_minus_interval(t: np.ndarray) -> np.ndarray:
    """
    CDF on [-4,0] for density 1/(pi*sqrt((-t)(4+t))).

    Using pushforward of [0,4] arcsine law under t=-mu:
    F_T(t) = 1 - (1/pi)*arccos(1 + t/2).
    """
    t = np.asarray(t, dtype=float)
    theta = np.arccos(1.0 + 0.5 * t)
    return 1.0 - (theta / math.pi)


def kolmogorov_distance_empirical_vs_arcsine_zeros(k: int) -> float:
    """Sup CDF error between empirical zeros and arcsine limit on [-4,0]."""
    z = fisher_zeros(k)
    F = arcsine_cdf_on_minus_interval(z)
    p = np.arange(1, k + 1, dtype=float)
    emp_right = p / float(k)
    emp_left = (p - 1.0) / float(k)
    err = np.maximum(np.abs(emp_right - F), np.abs(emp_left - F))
    return float(np.max(err)) if err.size else 0.0


def det_Ak_fibonacci(k: int) -> int:
    """det(L_k + I) = F_{2k+1}."""
    return fib(2 * int(k) + 1)


def det_Ak_tridiag(k: int) -> int:
    """
    Exact determinant of A_k = L_k + I using the tridiagonal recurrence.

    A_k has diagonal (3,...,3,2) and off-diagonal -1.
    """
    k = int(k)
    if k <= 0:
        raise ValueError("k must be positive")
    if k == 1:
        return 2
    # Leading principal minors for the first (k-1) steps with diagonal 3.
    d0, d1 = 1, 3  # D_0, D_1
    for _ in range(2, k):
        d0, d1 = d1, 3 * d1 - d0
    # Final step uses last diagonal 2.
    return int(2 * d1 - d0)


def Ak_inv_entry_formula(k: int, i: int, j: int) -> Fraction:
    """(L_k+I)^{-1}_{ij} as a rational Fibonacci ratio."""
    k = int(k)
    i = int(i)
    j = int(j)
    if not (1 <= i <= k and 1 <= j <= k):
        raise ValueError("indices out of range")
    if i > j:
        i, j = j, i
    num = fib(2 * i) * fib(2 * (k - j) + 1)
    den = fib(2 * k + 1)
    return Fraction(num, den)


def max_entry_error_via_inverse(k: int, pairs: List[Tuple[int, int]]) -> float:
    """Compute max |inv(A_k)_{ij} - Fibonacci formula| for selected pairs."""
    k = int(k)
    A = np.zeros((k, k), dtype=float)
    for idx in range(k):
        # A_k = L_k + I: diag = 3 except last = 2; off diag = -1.
        A[idx, idx] = 3.0 if idx < k - 1 else 2.0
        if idx + 1 < k:
            A[idx, idx + 1] = -1.0
            A[idx + 1, idx] = -1.0
    G = np.linalg.inv(A)
    err = 0.0
    for (i, j) in pairs:
        if i > k or j > k:
            continue
        a = float(G[i - 1, j - 1])
        b = float(Ak_inv_entry_formula(k=k, i=i, j=j))
        err = max(err, abs(a - b))
    return float(err)


def golden_coupling_scalars() -> Dict[str, float]:
    """Scalar identities at t=1 for eta, q, pi(1), g'(1)."""
    ph = phi()
    et = eta_from_t(1.0)
    q = q_from_eta(et)
    pi1 = 1.0 / (ph * ph + 1.0)
    return {
        "phi": float(ph),
        "eta_1": float(et),
        "log_phi": float(math.log(ph)),
        "q_1": float(q),
        "phi_inv_sq": float(ph ** (-2.0)),
        "pi1": float(pi1),
        "q_over_1plusq": float(q / (1.0 + q)),
        "pi1_over_sqrt5": float(pi1 / math.sqrt(5.0)),
    }


def riccati_qk_exact(k: int, t: int = 1) -> Fraction:
    """Compute q_k(t) from recursion exactly (for integer t)."""
    t = int(t)
    q = Fraction(1, 1 + t)
    for _ in range(1, int(k)):
        q = Fraction(1, (t + 2) - q)
    return q


def joukowsky_root_of_unity_residual(k: int) -> float:
    """Max |w^{2k+1}+1| over w=exp(i*(2p-1)pi/(2k+1))."""
    k = int(k)
    n = 2 * k + 1
    mx = 0.0
    for p in range(1, k + 1):
        theta = (2 * p - 1) * math.pi / float(n)
        w = complex(math.cos(theta), math.sin(theta))
        mx = max(mx, abs((w ** n) + 1.0))
    return float(mx)


@dataclass(frozen=True)
class Row:
    k: int
    det_ok: bool
    inv_err_abs: float
    ks_zeros: float
    riccati_err_abs: float
    joukowsky_root_resid: float

    def to_dict(self) -> Dict[str, object]:
        return {
            "k": int(self.k),
            "det_ok": bool(self.det_ok),
            "inv_err_abs": float(self.inv_err_abs),
            "ks_zeros": float(self.ks_zeros),
            "riccati_err_abs": float(self.riccati_err_abs),
            "joukowsky_root_resid": float(self.joukowsky_root_resid),
        }


def write_table(rows: List[Row], out_path: Path) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        (
            "\\caption{黄金耦合与 Fisher 零点的有限窗审计："
            "$\\det(L_k+I)=F_{2k+1}$ 与 Fibonacci 矩阵元闭式"
            "（推论~\\ref{cor:pom-Lk-t1-fibonacci-det-green}）、"
            "零点反正弦律（定理~\\ref{thm:pom-Lk-fisher-zeros-arcsine}）、"
            "Joukowsky 均匀化的奇根条件（注~\\ref{rem:pom-Lk-fisher-zeros-uniformization}）、"
            "以及 Riccati 递推的对象层一致性（命题~\\ref{prop:pom-Lk-boundary-riccati-recursion}）。}"
        )
    )
    lines.append("\\label{tab:fence_green_kernel_golden_coupling_audit}")
    lines.append("\\begin{tabular}{r c r r r r}")
    lines.append("\\toprule")
    lines.append("$k$ & det ok & $\\max|\\Delta A^{-1}_{ij}|$ & $\\|F_k-F\\|_\\infty$ & $|\\Delta q_k|$ & $\\max|w^{2k+1}+1|$\\\\")
    lines.append("\\midrule")
    for r in rows:
        det_ok = "yes" if r.det_ok else "no"
        lines.append(
            f"{r.k} & {det_ok} & {r.inv_err_abs:.2e} & {r.ks_zeros:.2e} & {r.riccati_err_abs:.2e} & {r.joukowsky_root_resid:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_audit(k_values: List[int]) -> None:
    # Scalar identities at t=1.
    scalars = golden_coupling_scalars()

    # Pairs for inverse entry checks (small k only).
    pairs = [(1, 1), (1, 2), (1, 5), (1, 10), (2, 3), (2, 7), (3, 9)]

    rows: List[Row] = []
    for k in k_values:
        k = int(k)
        det_ok = det_Ak_tridiag(k) == det_Ak_fibonacci(k)

        inv_err = 0.0
        if k <= 40:
            inv_err = max_entry_error_via_inverse(k, pairs)

        ks = kolmogorov_distance_empirical_vs_arcsine_zeros(k)

        # Riccati recursion at t=1 vs Fibonacci ratio.
        qk_rec = riccati_qk_exact(k, t=1)
        qk_fib = Fraction(fib(2 * k - 1), fib(2 * k + 1))
        riccati_err = float(abs(qk_rec - qk_fib))

        root_resid = joukowsky_root_of_unity_residual(k)

        rows.append(
            Row(
                k=k,
                det_ok=bool(det_ok),
                inv_err_abs=float(inv_err),
                ks_zeros=float(ks),
                riccati_err_abs=float(riccati_err),
                joukowsky_root_resid=float(root_resid),
            )
        )

    payload: Dict[str, object] = {
        "params": {"k_values": [int(k) for k in k_values], "t": 1.0},
        "scalars": scalars,
        "rows": [r.to_dict() for r in rows],
    }
    json_out = export_dir() / "fence_green_kernel_golden_coupling_audit.json"
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_out = generated_dir() / "tab_fence_green_kernel_golden_coupling_audit.tex"
    write_table(rows, tex_out)

