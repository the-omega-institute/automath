#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Rotation scan: microstate empirical law vs true law (TV/KL) with a KL certificate.

Outputs:
- artifacts/export/rotation_microstate_kl_certificate.csv
- sections/generated/tab_rotation_microstate_kl_certificate.tex

This script targets the deterministic rotation model but uses the unique ergodicity
limit (Lebesgue) as the "true" distribution of length-m microstates.

We focus on the canonical Sturmian window beta=alpha where the endpoint set
collapses to { -k alpha } and admits a simple lower bound on the minimum atom.
"""

from __future__ import annotations

import csv
import math
import time
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress, fold_m


def _pack_bits_to_int(bits: Iterable[int], m: int) -> int:
    x = 0
    for b in bits:
        x = (x << 1) | (1 if b else 0)
    return x & ((1 << m) - 1)


def _int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def rotation_bits(alpha: float, x0: float, beta: float, n: int) -> np.ndarray:
    ts = np.arange(n, dtype=np.float64)
    xs = (x0 + alpha * ts) % 1.0
    return (xs < beta).astype(np.uint8)


def count_micro_hist(s: np.ndarray, m: int, N: int, prog: Progress) -> Dict[int, int]:
    if N + m - 1 > len(s):
        raise ValueError("s too short for requested N,m")
    mask = (1 << m) - 1
    w = _pack_bits_to_int(s[:m], m)
    counts: Dict[int, int] = {}
    for t in range(N):
        if t > 0:
            w = ((w << 1) & mask) | int(s[t + m - 1])
        counts[w] = counts.get(w, 0) + 1
        prog.tick(f"count_micro m={m} t={t}/{N}")
    return counts


def _normalize_counts(counts: Dict[int, int], N: int) -> Dict[int, float]:
    out: Dict[int, float] = {}
    for k, c in counts.items():
        out[k] = float(c) / float(N)
    return out


def tv_distance_int(p: Dict[int, float], q: Dict[int, float]) -> float:
    keys = set(p.keys()) | set(q.keys())
    s = 0.0
    for k in keys:
        s += abs(p.get(k, 0.0) - q.get(k, 0.0))
    return 0.5 * s


def kl_divergence_int(
    p: Dict[int, float], q: Dict[int, float], eps: float = 1e-300
) -> float:
    s = 0.0
    for k, pk in p.items():
        if pk <= 0.0:
            continue
        qk = q.get(k, 0.0)
        qk = qk if qk > 0.0 else eps
        s += pk * math.log(pk / qk)
    return s


def _golden_discrepancy_upper_bound_explicit(N: int) -> float:
    """Appendix-H explicit bound for alpha=phi^{-1}, valid for N>=2."""
    if N < 2:
        return 1.0
    return (3.0 + math.ceil(math.log((5.0**0.5) * N) / math.log(PHI))) / float(N)


def _unique_sorted(values: List[float], eps: float = 1e-15) -> List[float]:
    values_sorted = sorted(values)
    out: List[float] = []
    for v in values_sorted:
        if not out:
            out.append(v)
            continue
        if abs(v - out[-1]) > eps:
            out.append(v)
    return out


def true_microstate_distribution(alpha: float, beta: float, m: int) -> Dict[int, float]:
    """Compute the true (Lebesgue) distribution of length-m microstates.

    For the rotation readout s_t(x)=1_{[0,beta)}({x+t alpha}), the length-m microstate
    is locally constant on a finite partition of the circle with endpoints among
    { -k alpha } and { beta - k alpha }, k=0..m. We enumerate those endpoints, and
    for each interval take a midpoint to identify the microstate.
    """
    endpoints: List[float] = []
    for k in range(m + 1):
        endpoints.append((-float(k) * alpha) % 1.0)
        endpoints.append((beta - float(k) * alpha) % 1.0)

    pts = _unique_sorted(endpoints)
    if len(pts) < 2:
        raise ValueError("unexpected: partition endpoints too small")

    dist: Dict[int, float] = {}
    for i in range(len(pts)):
        a = pts[i]
        b = pts[(i + 1) % len(pts)]
        if i == len(pts) - 1:
            b = pts[0] + 1.0
        length = float(b - a)
        if length <= 0.0:
            continue
        mid = a + 0.5 * length
        x = mid % 1.0

        bits: List[int] = []
        xt = x
        for _ in range(m):
            bits.append(1 if xt < beta else 0)
            xt = (xt + alpha) % 1.0
        w = _pack_bits_to_int(bits, m)
        dist[w] = dist.get(w, 0.0) + length

    # Normalize (robust to floating drift).
    total = sum(dist.values())
    if total <= 0.0:
        raise ValueError("unexpected: empty true distribution")
    for k in list(dist.keys()):
        dist[k] /= total
    return dist


def min_positive_mass(q: Dict[int, float]) -> float:
    vals = [v for v in q.values() if v > 0.0]
    if not vals:
        return 0.0
    return min(vals)


def folded_distribution_from_micro(
    q_micro: Dict[int, float], m: int
) -> Dict[int, float]:
    """Push forward a length-m microstate distribution through Fold_m.

    Keys are packed integers of length-m 0/1 words.
    """
    out: Dict[int, float] = {}
    for w, mass in q_micro.items():
        if mass <= 0.0:
            continue
        micro_bits = _int_to_bits(int(w), m)
        folded_bits = fold_m(micro_bits)
        key = _pack_bits_to_int(folded_bits, m)
        out[key] = out.get(key, 0.0) + float(mass)

    total = sum(out.values())
    if total <= 0.0:
        return {}
    for k in list(out.keys()):
        out[k] /= total
    return out


def write_table(rows: List[Dict[str, object]], out_path: str) -> None:
    # A small, audit-friendly table: show (m,N), empirical TV/KL, and certificate upper bounds.
    lines: List[str] = []
    lines.append("\\begin{table}[H]\n")
    lines.append("\\centering\n")
    lines.append("\\small\n")
    lines.append("\\begin{tabular}{rrrrrr}\n")
    lines.append("\\toprule\n")
    lines.append(
        "$m$ & $N$ & $D_{\\mathrm{TV}}$ & $D_{\\mathrm{KL}}$ & TV cert ub & KL cert ub\\\\\n"
    )
    lines.append("\\midrule\n")
    for r in rows:
        m = int(r["m"])  # type: ignore[arg-type]
        N = int(r["N"])  # type: ignore[arg-type]
        tv = float(r["tv"])  # type: ignore[arg-type]
        kl = float(r["kl"])  # type: ignore[arg-type]
        tv_ub = float(r["tv_cert_ub"])  # type: ignore[arg-type]
        kl_ub = float(r["kl_cert_ub"])  # type: ignore[arg-type]
        lines.append(
            f"{m} & {N} & {tv:.3g} & {kl:.3g} & {tv_ub:.3g} & {kl_ub:.3g}\\\\\n"
        )
    lines.append("\\bottomrule\n")
    lines.append("\\end{tabular}\n")
    lines.append(
        "\\caption{旋转扫描（黄金分支、规范窗 $\\beta=\\alpha$）下，长度-$m$ 微态经验分布到其 Lebesgue 极限分布的 TV/KL 偏差，以及由差异度证书与最小原子下界导出的 KL 证书上界。}\n"
    )
    lines.append("\\label{tab:rotation-microstate-kl-certificate}\n")
    lines.append("\\end{table}\n")

    p = generated_dir() / out_path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(lines), encoding="utf-8")


def write_table_folded(rows: List[Dict[str, object]], out_path: str) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]\n")
    lines.append("\\centering\n")
    lines.append("\\small\n")
    lines.append("\\begin{tabular}{rrrrrr}\n")
    lines.append("\\toprule\n")
    lines.append(
        "$m$ & $N$ & $D_{\\mathrm{TV}}$ (fold) & $D_{\\mathrm{KL}}$ (fold) & TV cert ub & KL cert ub\\\\\n"
    )
    lines.append("\\midrule\n")
    for r in rows:
        m = int(r["m"])  # type: ignore[arg-type]
        N = int(r["N"])  # type: ignore[arg-type]
        tv = float(r["tv_fold"])  # type: ignore[arg-type]
        kl = float(r["kl_fold"])  # type: ignore[arg-type]
        tv_ub = float(r["tv_cert_ub"])  # type: ignore[arg-type]
        kl_ub = float(r["kl_cert_ub"])  # type: ignore[arg-type]
        lines.append(
            f"{m} & {N} & {tv:.3g} & {kl:.3g} & {tv_ub:.3g} & {kl_ub:.3g}\\\\\n"
        )
    lines.append("\\bottomrule\n")
    lines.append("\\end{tabular}\n")
    lines.append(
        "\\caption{旋转扫描（黄金分支、规范窗 $\\beta=\\alpha$）下，折叠后稳定类型经验分布到其 Lebesgue 极限分布（推前分布）的 TV/KL 偏差；证书上界与微态层面一致，并通过 KL 的推前单调性保持有效。}\n"
    )
    lines.append("\\label{tab:rotation-folded-kl-certificate}\n")
    lines.append("\\end{table}\n")

    p = generated_dir() / out_path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(lines), encoding="utf-8")


@dataclass(frozen=True)
class RunCfg:
    m: int
    N: int


def main() -> None:
    out_csv = export_dir() / "rotation_microstate_kl_certificate.csv"
    out_csv.parent.mkdir(parents=True, exist_ok=True)

    alpha = 1.0 / PHI
    beta = alpha  # canonical Sturmian window
    x0 = 0.123

    # Keep runtime small: true distribution uses O(m) endpoints; empirical uses O(N).
    runs = [
        RunCfg(m=8, N=10_000),
        RunCfg(m=12, N=30_000),
        RunCfg(m=16, N=100_000),
        RunCfg(m=18, N=300_000),
    ]

    prog = Progress("exp_rotation_microstate_kl_certificate", every_seconds=20.0)
    t0_all = time.time()

    rows: List[Dict[str, object]] = []
    for cfg in runs:
        m = cfg.m
        N = cfg.N
        prog.tick(f"start m={m} N={N}")

        true_q = true_microstate_distribution(alpha=alpha, beta=beta, m=m)
        true_pi_fold = folded_distribution_from_micro(true_q, m=m)
        qmin_true = min_positive_mass(true_q)
        # Lower bound on the minimum partition atom from the Markov constant:
        # every gap is >= min_{1<=k<=m} ||k alpha||, and ||k alpha|| >= c(alpha)/k.
        qmin_lb = (1.0 / (5.0**0.5)) / float(
            m
        )  # c(alpha)=1/sqrt(5) for the golden branch

        s = rotation_bits(alpha=alpha, x0=x0, beta=beta, n=N + m)
        counts = count_micro_hist(s=s, m=m, N=N, prog=prog)
        emp_p = _normalize_counts(counts, N=N)
        emp_pi_fold = folded_distribution_from_micro(emp_p, m=m)

        tv = tv_distance_int(emp_p, true_q)
        kl = kl_divergence_int(emp_p, true_q)

        tv_fold = tv_distance_int(emp_pi_fold, true_pi_fold)
        kl_fold = kl_divergence_int(emp_pi_fold, true_pi_fold)

        DN_ub = _golden_discrepancy_upper_bound_explicit(N)
        tv_cert_ub = float(m + 1) * DN_ub
        # KL <= (1/(2 q_min)) * ||p-q||_1^2 = (2/q_min) * TV^2.
        kl_cert_ub = (2.0 * (tv_cert_ub * tv_cert_ub)) / max(qmin_lb, 1e-300)

        rows.append(
            {
                "alpha": alpha,
                "beta": beta,
                "x0": x0,
                "m": m,
                "N": N,
                "tv": tv,
                "kl": kl,
                "tv_fold": tv_fold,
                "kl_fold": kl_fold,
                "DN_star_ub": DN_ub,
                "qmin_true": qmin_true,
                "qmin_lowerbound": qmin_lb,
                "tv_cert_ub": tv_cert_ub,
                "kl_cert_ub": kl_cert_ub,
            }
        )

    # Write CSV (auditable raw data).
    with out_csv.open("w", encoding="utf-8", newline="") as f:
        fieldnames = [
            "alpha",
            "beta",
            "x0",
            "m",
            "N",
            "tv",
            "kl",
            "tv_fold",
            "kl_fold",
            "DN_star_ub",
            "qmin_true",
            "qmin_lowerbound",
            "tv_cert_ub",
            "kl_cert_ub",
        ]
        wr = csv.DictWriter(f, fieldnames=fieldnames)
        wr.writeheader()
        for r in rows:
            wr.writerow(r)

    # Write LaTeX fragment.
    write_table(rows, out_path="tab_rotation_microstate_kl_certificate.tex")
    write_table_folded(rows, out_path="tab_rotation_folded_kl_certificate.tex")

    dt = time.time() - t0_all
    print(
        f"[exp_rotation_microstate_kl_certificate] WROTE {out_csv} in {dt:.1f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
