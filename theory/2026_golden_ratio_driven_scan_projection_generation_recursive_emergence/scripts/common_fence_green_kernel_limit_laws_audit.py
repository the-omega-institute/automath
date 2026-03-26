#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Limit-law audits for the mixed-boundary discrete Laplacian L_k = K_k^{-1},
where K_k(i,j)=min(i,j).

This module is used by exp_fence_order_poly_spectral_audit.py so the checks
run inside the existing run_all.py pipeline without adding new steps.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

import numpy as np

from common_paths import export_dir, generated_dir


def mu_eigenvalues(k: int) -> np.ndarray:
    """Return eigenvalues mu_p=4 sin^2((2p-1)pi/(4k+2)), ascending."""
    k = int(k)
    p = np.arange(1, k + 1, dtype=float)
    phi = (2.0 * p - 1.0) * math.pi / (4.0 * k + 2.0)
    mu = 4.0 * (np.sin(phi) ** 2)
    mu.sort()
    return mu


def arcsine_cdf(mu: np.ndarray) -> np.ndarray:
    """CDF F(mu)=theta(mu)/pi on [0,4], where theta=arccos(1-mu/2)."""
    mu = np.asarray(mu, dtype=float)
    theta = np.arccos(1.0 - 0.5 * mu)
    return theta / math.pi


def kolmogorov_distance_empirical_vs_arcsine(k: int) -> float:
    """Sup norm of CDF error between empirical mu_p and arcsine limit."""
    mu = mu_eigenvalues(k)
    F = arcsine_cdf(mu)
    p = np.arange(1, k + 1, dtype=float)
    emp_right = p / float(k)
    emp_left = (p - 1.0) / float(k)
    err = np.maximum(np.abs(emp_right - F), np.abs(emp_left - F))
    return float(np.max(err)) if err.size else 0.0


def weyl_remainder_sup(k: int) -> float:
    """Sup over mu_p of |N_k(mu_p) - ((2k+1)/(2pi))*theta(mu_p)|."""
    k = int(k)
    n = 2 * k + 1
    # At mu_p, theta(mu_p)=(2p-1)pi/n and N_k(mu_p)=p, so remainder is exactly 1/2.
    # Keep a numeric version for uniformity.
    p = np.arange(1, k + 1, dtype=float)
    theta = (2.0 * p - 1.0) * math.pi / float(n)
    rem = np.abs(p - (float(n) * theta / (2.0 * math.pi)))
    return float(np.max(rem)) if rem.size else 0.0


def heat_kernel_avg_err(k: int, t: float) -> float:
    """|H_k(t)/k - e^{-2t}I0(2t)| with H_k(t)=tr exp(-t L_k)."""
    mu = mu_eigenvalues(k)
    hk = float(np.sum(np.exp(-float(t) * mu)))
    target = float(math.exp(-2.0 * float(t)) * float(np.i0(2.0 * float(t))))
    return float(abs((hk / float(k)) - target))


def det_continuum_cosh_err(k: int, s: float) -> float:
    """|det(L_k + 4s/(2k+1)^2 I) - cosh(sqrt(s))| via Chebyshev closed form."""
    k = int(k)
    n = 2 * k + 1
    s = float(s)
    x = math.sqrt(1.0 + (s / (n * n)))
    # det = T_n(x)/x with T_n(x)=cosh(n arcosh x) for x>=1.
    det = math.cosh(float(n) * math.acosh(x)) / x
    target = math.cosh(math.sqrt(s))
    return float(abs(det - target))


@dataclass(frozen=True)
class Row:
    k: int
    ks_dist: float
    weyl_rem_sup: float
    heat_err_t1: float
    det_err_s1: float

    def to_dict(self) -> Dict[str, object]:
        return {
            "k": int(self.k),
            "ks_dist": float(self.ks_dist),
            "weyl_rem_sup": float(self.weyl_rem_sup),
            "heat_err_t1": float(self.heat_err_t1),
            "det_err_s1": float(self.det_err_s1),
        }


def write_table(rows: List[Row], out_path: Path) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{混合边界离散 Laplacian $L_k=K_k^{-1}$ 的有限窗极限律审计："
        "经验谱分布对反正弦律的 Kolmogorov 距离（定理~\\ref{thm:pom-Lk-arcsine-law}），"
        "离散 Weyl 计数余项上界（推论~\\ref{cor:pom-Lk-discrete-weyl}），"
        "热核密度对 $e^{-2t}I_0(2t)$ 的收敛（推论~\\ref{cor:pom-Lk-heat-kernel-bessel}，取 $t=1$），"
        "以及 ND 行列式极限 $\\cosh(\\sqrt{s})$ 的收敛（推论~\\ref{cor:pom-Lk-continuum-ND-det-cosh}，取 $s=1$）。}"
    )
    lines.append("\\label{tab:fence_green_kernel_spectral_limit_laws_audit}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$k$ & $\\|F_k-F\\|_{\\infty}$ & $\\sup|R_k|$ & $|H_k(1)/k- e^{-2}I_0(2)|$ & $|\\det-\\cosh(1)|$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.k} & {r.ks_dist:.2e} & {r.weyl_rem_sup:.2e} & {r.heat_err_t1:.2e} & {r.det_err_s1:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_audit(k_values: List[int]) -> None:
    rows: List[Row] = []
    for k in k_values:
        rows.append(
            Row(
                k=int(k),
                ks_dist=kolmogorov_distance_empirical_vs_arcsine(k),
                weyl_rem_sup=weyl_remainder_sup(k),
                heat_err_t1=heat_kernel_avg_err(k, t=1.0),
                det_err_s1=det_continuum_cosh_err(k, s=1.0),
            )
        )

    payload: Dict[str, object] = {"params": {"k_values": [int(k) for k in k_values], "t": 1.0, "s": 1.0}, "rows": [r.to_dict() for r in rows]}
    json_out = export_dir() / "fence_green_kernel_spectral_limit_laws_audit.json"
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_out = generated_dir() / "tab_fence_green_kernel_spectral_limit_laws_audit.tex"
    write_table(rows, tex_out)

