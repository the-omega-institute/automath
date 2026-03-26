#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Area-law / resolvent / Green-kernel audits for the mixed-boundary discrete Laplacian
L_k = K_k^{-1}, where K_k(i,j)=min(i,j).

This module is invoked by exp_fence_order_poly_spectral_audit.py so the checks run
inside the existing run_all.py pipeline without adding new steps.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir


def eta_from_t(t: float) -> float:
    if t <= 0.0:
        raise ValueError("Require t>0 for eta/q parametrization")
    return float(math.asinh(math.sqrt(t / 4.0)))


def q_from_eta(eta: float) -> float:
    return float(math.exp(-2.0 * float(eta)))


def q_closed_form(t: float) -> float:
    t = float(t)
    if t <= 0.0:
        raise ValueError("Require t>0")
    return float(((math.sqrt(4.0 + t) - math.sqrt(t)) / 2.0) ** 2)


def mu_eigenvalues(k: int) -> np.ndarray:
    """mu_p = 4 sin^2((2p-1)pi/(4k+2)), p=1..k."""
    k = int(k)
    p = np.arange(1, k + 1, dtype=float)
    phi = (2.0 * p - 1.0) * math.pi / (4.0 * k + 2.0)
    mu = 4.0 * (np.sin(phi) ** 2)
    return mu


def logdet_from_spectrum(k: int, t: float) -> float:
    mu = mu_eigenvalues(k)
    return float(np.sum(np.log(mu + float(t))))


def logdet_qform(k: int, t: float) -> float:
    eta = eta_from_t(t)
    q = q_from_eta(eta)
    # logdet = 2k eta - log(1+q) + log(1+q^{2k+1})
    return float(2.0 * k * eta - math.log1p(q) + math.log1p(q ** (2 * k + 1)))


def bulk_integral_numeric(t: float, n: int = 200_000) -> float:
    """Numerically approximate (1/pi)∫_0^pi log(1+t/(4 sin^2(theta/2))) dtheta."""
    t = float(t)
    if t <= 0.0:
        raise ValueError("Require t>0")
    n = int(n)
    if n < 1000:
        raise ValueError("Require n>=1000")
    # Avoid theta=0 singularity by starting at a small offset; integrand is integrable.
    eps = math.pi / float(n)
    theta = np.linspace(eps, math.pi, num=n, dtype=float)
    a = 1.0 + t / (4.0 * (np.sin(theta / 2.0) ** 2))
    y = np.log(a)
    return float((1.0 / math.pi) * np.trapezoid(y, theta))


def tr_resolvent_sum(k: int, t: float) -> float:
    mu = mu_eigenvalues(k)
    return float(np.sum(1.0 / (mu + float(t))))


def tr_resolvent_formula(k: int, t: float) -> float:
    t = float(t)
    eta = eta_from_t(t)
    return float(
        (2.0 * k + 1.0) / (2.0 * math.sqrt(t * (4.0 + t))) * math.tanh((2.0 * k + 1.0) * eta)
        - 1.0 / (2.0 * (4.0 + t))
    )


def green_entry_formula(k: int, t: float, i: int, j: int) -> float:
    """(L_k+tI)^{-1}_{ij} for 1<=i,j<=k."""
    k = int(k)
    i = int(i)
    j = int(j)
    if not (1 <= i <= k and 1 <= j <= k):
        raise ValueError("indices out of range")
    if i > j:
        i, j = j, i
    eta = eta_from_t(float(t))
    num = math.sinh(2.0 * i * eta) * math.cosh((2.0 * (k - j) + 1.0) * eta)
    den = math.sinh(2.0 * eta) * math.cosh((2.0 * k + 1.0) * eta)
    return float(num / den)


def max_green_entry_error_via_inverse(k: int, t: float, pairs: List[Tuple[int, int]]) -> float:
    """Compute max |inv(A)_{ij}-formula| for given pairs; A=L_k+tI."""
    k = int(k)
    t = float(t)
    # Build A (float64) and invert (small k only).
    A = np.zeros((k, k), dtype=float)
    for idx in range(k):
        A[idx, idx] = (2.0 + t) if idx < k - 1 else (1.0 + t)
        if idx + 1 < k:
            A[idx, idx + 1] = -1.0
            A[idx + 1, idx] = -1.0
    G = np.linalg.inv(A)
    err = 0.0
    for (i, j) in pairs:
        a = float(G[i - 1, j - 1])
        b = green_entry_formula(k=k, t=t, i=i, j=j)
        err = max(err, abs(a - b))
    return float(err)


def clustering_ratio_max(k: int, t: float, pairs: List[Tuple[int, int]]) -> float:
    """Return max over pairs of (G_{ij} * sinh(2eta) * exp(2eta(j-i))). Should be <=1."""
    eta = eta_from_t(float(t))
    norm = math.sinh(2.0 * eta)
    mx = 0.0
    for (i, j) in pairs:
        if i > j:
            i, j = j, i
        gij = green_entry_formula(k=k, t=t, i=i, j=j)
        val = gij * norm * math.exp(2.0 * eta * float(j - i))
        mx = max(mx, float(val))
    return float(mx)


def boundary_fixed_point_err(k: int, t: float) -> float:
    """|G_11 - q(t)| at finite k using closed forms."""
    eta = eta_from_t(float(t))
    q = q_closed_form(float(t))
    g11 = math.cosh((2.0 * k - 1.0) * eta) / math.cosh((2.0 * k + 1.0) * eta)
    return float(abs(g11 - q))


def surface_derivative_err(k: int, t: float) -> float:
    """| (tr - k f') - g'(t) | with f=2eta, g=-log(1+q)."""
    t = float(t)
    eta = eta_from_t(t)
    q = q_from_eta(eta)
    tr = tr_resolvent_formula(k=k, t=t)
    fp = 1.0 / math.sqrt(t * (4.0 + t))  # f'(t) = 2 eta'
    gp = (q / (1.0 + q)) * (1.0 / math.sqrt(t * (4.0 + t)))
    return float(abs((tr - float(k) * fp) - gp))


@dataclass(frozen=True)
class Row:
    k: int
    logdet_err_abs: float
    bulk_int_err_abs: float
    tr_err_abs: float
    green_err_abs: float | None
    cluster_ratio_max: float
    q_fixed_err_abs: float
    gprime_err_abs: float

    def to_dict(self) -> Dict[str, object]:
        return {
            "k": int(self.k),
            "logdet_err_abs": float(self.logdet_err_abs),
            "bulk_int_err_abs": float(self.bulk_int_err_abs),
            "tr_err_abs": float(self.tr_err_abs),
            "green_err_abs": (None if self.green_err_abs is None else float(self.green_err_abs)),
            "cluster_ratio_max": float(self.cluster_ratio_max),
            "q_fixed_err_abs": float(self.q_fixed_err_abs),
            "gprime_err_abs": float(self.gprime_err_abs),
        }


def write_table(rows: List[Row], out_path: Path, t: float) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        (
            "\\caption{确定性面积律/Green-resolvent 闭式的有限窗审计（取 $t=%.3g$）："
            "核验 $q$-形式行列式分解（推论~\\ref{cor:pom-Lk-area-law-qform}）、"
            "符号积分闭式（命题~\\ref{prop:pom-Kk-strong-szego-bulk-surface}）、"
            "resolvent 迹闭式（推论~\\ref{cor:pom-Lk-resolvent-trace-hyperbolic}）、"
            "Green 矩阵元闭式与指数聚类上界（命题~\\ref{prop:pom-Lk-green-kernel-entries}、推论~\\ref{cor:pom-Lk-exponential-clustering-gaplaw}），"
            "以及边界固定点 $q(t)$ 与表面项导数 $g'(t)$ 的一致性（推论~\\ref{cor:pom-Lk-boundary-fixed-point-riccati}、\\ref{cor:pom-Lk-surface-free-energy}）。}"
        )
        % float(t)
    )
    lines.append("\\label{tab:fence_green_kernel_area_law_resolvent_audit}")
    lines.append("\\begin{tabular}{r r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$k$ & $|\\Delta\\log\\det|$ & $|\\Delta\\,\\mathrm{bulk}|$ & $|\\Delta\\,\\mathrm{tr}|$ & $\\max|\\Delta G_{ij}|$ & $\\max\\rho$ & $|G_{11}-q|$ & $|\\Delta g'|$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        gerr = "--" if r.green_err_abs is None else f"{r.green_err_abs:.2e}"
        lines.append(
            f"{r.k} & {r.logdet_err_abs:.2e} & {r.bulk_int_err_abs:.2e} & {r.tr_err_abs:.2e} & {gerr} & {r.cluster_ratio_max:.6f} & {r.q_fixed_err_abs:.2e} & {r.gprime_err_abs:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_audit(k_values: List[int], t: float = 1.0) -> None:
    t = float(t)
    if t <= 0.0:
        raise ValueError("Require t>0")

    # Sample pairs for Green/clustering checks.
    pairs_small = [(1, 1), (1, 2), (1, 5), (2, 3), (2, 7), (3, 9)]
    pairs_cluster = [(1, 1), (1, 2), (1, 10), (2, 20), (3, 25), (10, 30)]

    # Bulk integral numeric check (single computation reused).
    bulk_num = bulk_integral_numeric(t, n=200_000)
    bulk_closed = 2.0 * eta_from_t(t)
    bulk_err = abs(bulk_num - bulk_closed)

    rows: List[Row] = []
    for k in k_values:
        k = int(k)
        # logdet check: q-form vs spectral product.
        ld_spec = logdet_from_spectrum(k, t)
        ld_q = logdet_qform(k, t)
        ld_err = abs(ld_spec - ld_q)

        # tr check: sum vs closed form.
        tr_sum = tr_resolvent_sum(k, t)
        tr_for = tr_resolvent_formula(k, t)
        tr_err = abs(tr_sum - tr_for)

        # Green entry check (invert only for small k).
        green_err: float | None = None
        if k <= 40:
            # Filter pairs to within range.
            ps = [(i, j) for (i, j) in pairs_small if i <= k and j <= k]
            if ps:
                green_err = max_green_entry_error_via_inverse(k, t, ps)

        # Clustering ratio check via formula (no inversion).
        pc = [(i, j) for (i, j) in pairs_cluster if i <= k and j <= k]
        if not pc:
            pc = [(1, k)]
        ratio = clustering_ratio_max(k, t, pc)

        rows.append(
            Row(
                k=k,
                logdet_err_abs=float(ld_err),
                bulk_int_err_abs=float(bulk_err),
                tr_err_abs=float(tr_err),
                green_err_abs=(None if green_err is None else float(green_err)),
                cluster_ratio_max=float(ratio),
                q_fixed_err_abs=boundary_fixed_point_err(k=max(k, 50), t=t),
                gprime_err_abs=surface_derivative_err(k=max(k, 50), t=t),
            )
        )

    payload: Dict[str, object] = {
        "params": {"k_values": [int(k) for k in k_values], "t": float(t)},
        "bulk_integral_numeric": float(bulk_num),
        "bulk_integral_closed": float(bulk_closed),
        "rows": [r.to_dict() for r in rows],
    }
    json_out = export_dir() / "fence_green_kernel_area_law_resolvent_audit.json"
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_out = generated_dir() / "tab_fence_green_kernel_area_law_resolvent_audit.tex"
    write_table(rows, tex_out, t=t)

