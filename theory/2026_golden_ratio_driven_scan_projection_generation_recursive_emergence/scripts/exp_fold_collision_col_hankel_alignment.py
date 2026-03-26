#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Align Fold collision scaling with a local Hankel conditioning profile.

Context (paper, main_fast.pdf):
  - Collision probability (Fold output distribution pi_m):
      Col_m = sum_x pi_m(x)^2 = S2(m) / 4^m,
    where S2(m) = sum_x d_m(x)^2.
    A useful "uniformity-scaled" quantity is F_{m+2} * Col_m.

  - For higher moments S_q(m), audited integer recurrences imply a minimal order d_q,
    and Hankel blocks built from a_n := S_q(n+2) become rank-deficient at the nominal
    dimension 2*floor(q/2)+1 for q>=9.

This script produces a lightweight, auditable alignment plot:
  - x-axis: m (audit window)
  - left y-axis: F_{m+2} * Col_m
  - right y-axis: log10(cond(H_m)), where H_m is a local d_q-by-d_q Hankel block
                  from a_n=S_q(n+2) at shift t=m-2.
  - points with (m+2) % 3 == 0 are highlighted (parity-induced Fourier zero regime).

Artifacts:
  - artifacts/export/fold_collision_col_hankel_alignment_q{q}.json
  - artifacts/export/fold_collision_col_hankel_alignment_q{q}.png
  - sections/generated/fig_fold_collision_col_hankel_alignment_q{q}.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_paths import export_dir, generated_dir
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17, counts_mod_fib


def fib_0_1_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [0]
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def _moment_from_counts(c: np.ndarray, q: int) -> int:
    """Compute S_q = sum_r c[r]^q exactly as a Python int."""
    vals, freq = np.unique(c, return_counts=True)
    s = 0
    for v, f in zip(vals.tolist(), freq.tolist(), strict=True):
        s += int(f) * (int(v) ** int(q))
    return int(s)


def _rec_spec_by_q() -> Dict[int, Dict[str, object]]:
    by_q: Dict[int, Dict[str, object]] = {}
    for r in PRECOMPUTED_RECS_9_17:
        by_q[int(r["k"])] = r
    return by_q


def compute_Sq_from_recurrence(q: int, m_max: int) -> Dict[int, int]:
    """Compute S_q(m) for m=2..m_max using audited recurrence + small-m mod DP init."""
    spec = _rec_spec_by_q().get(int(q))
    if spec is None:
        raise ValueError(f"Unsupported q={q}; expected q in {sorted(_rec_spec_by_q().keys())}")
    d = int(spec["order"])
    m0 = int(spec["m0"])
    coeffs = [int(x) for x in spec["coeffs"]]  # type: ignore[index]
    if len(coeffs) != d:
        raise RuntimeError("Bad recurrence spec: coeff length != order")
    if m_max < 2:
        raise ValueError("m_max must be >= 2")

    S: Dict[int, int] = {}
    # Small-m init via modular DP (cheap: modulus is tiny for m<m0<=15).
    for m in range(2, min(m0, m_max + 1)):
        c = counts_mod_fib(m, prog=None)
        S[m] = _moment_from_counts(c, q=q)

    # Extend via recurrence.
    for m in range(max(m0, 2), m_max + 1):
        if m < m0:
            continue
        s = 0
        for i, c_i in enumerate(coeffs, start=1):
            s += int(c_i) * int(S[m - i])
        S[m] = int(s)
    return S


def compute_S2(m_max: int) -> Dict[int, int]:
    """Compute S2(m) exactly from the verified order-3 recurrence."""
    if m_max < 2:
        raise ValueError("m_max must be >= 2")
    S2: Dict[int, int] = {2: 6, 3: 14, 4: 36}
    for m in range(5, m_max + 1):
        S2[m] = 2 * S2[m - 1] + 2 * S2[m - 2] - 2 * S2[m - 3]
    # Trim if caller asks for smaller.
    return {m: v for m, v in S2.items() if m <= m_max}


def hankel_cond_profile(a: List[int], d: int, m_min: int, m_max: int) -> Dict[int, float]:
    """Compute cond(H_m) for H_m = (a_{t+i+j})_{0<=i,j<d}, t=m-2."""
    if d <= 0:
        raise ValueError("d must be positive")
    out: Dict[int, float] = {}
    for m in range(m_min, m_max + 1):
        t = m - 2
        need = t + 2 * (d - 1)
        if need >= len(a):
            out[m] = float("nan")
            continue
        a_t = float(a[t])
        if a_t == 0.0:
            out[m] = float("nan")
            continue
        H = np.empty((d, d), dtype=np.float64)
        for i in range(d):
            for j in range(d):
                H[i, j] = float(a[t + i + j]) / a_t  # scale-invariant normalization
        try:
            out[m] = float(np.linalg.cond(H))
        except np.linalg.LinAlgError:
            out[m] = float("nan")
    return out


@dataclass(frozen=True)
class Row:
    m: int
    F_m2: int
    col_scaled: float
    beat_mod3: bool
    hankel_cond: float
    hankel_log10_cond: float


def write_figure_tex(path: Path, png_rel_path: str, q: int, d_q: int) -> None:
    lines: List[str] = []
    lines.append("\\begin{figure}[H]")
    lines.append("\\centering")
    lines.append(f"\\includegraphics[width=0.95\\linewidth]{{{png_rel_path}}}")
    lines.append(
        "\\caption{Alignment diagnostic in the $m$ audit window: "
        f"left axis is $F_{{m+2}}\\,\\mathsf{{Col}}_m$ (Fold collision scaling), "
        f"right axis is $\\log_{{10}}\\kappa(H_m)$ for a local Hankel block from $a_n:=S_{q}(n+2)$ "
        f"(here $q={q}$, block size $d_q={d_q}$). "
        "Points with $m+2\\equiv 0\\ (\\mathrm{mod}\\ 3)$ are highlighted.}"
    )
    lines.append(f"\\label{{fig:fold-collision-col-hankel-alignment-q{q}}}")
    lines.append("\\end{figure}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Plot F_{m+2}*Col_m aligned with a local Hankel conditioning profile.")
    parser.add_argument("--q", type=int, default=9, help="Moment order q (supported: 9..17).")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=26)
    args = parser.parse_args()

    q = int(args.q)
    m_min = int(args.m_min)
    m_max = int(args.m_max)
    if m_min < 2:
        raise ValueError("m_min must be >= 2")
    if m_max < m_min:
        raise ValueError("m_max must be >= m_min")

    rec = _rec_spec_by_q()[q]
    d_q = int(rec["order"])

    # Need S_q up to m_max + 2(d_q-1) to build local Hankel blocks at m_max.
    m_need = m_max + 2 * (d_q - 1)
    Sq = compute_Sq_from_recurrence(q=q, m_max=m_need)

    # a_n := S_q(n+2) for n=0..(m_need-2).
    a: List[int] = [Sq[m] for m in range(2, m_need + 1)]

    cond_by_m = hankel_cond_profile(a=a, d=d_q, m_min=m_min, m_max=m_max)

    # Collision scaling from S2.
    S2 = compute_S2(m_max=m_max)
    F = fib_0_1_upto(m_max + 2)

    rows: List[Row] = []
    ms = list(range(m_min, m_max + 1))
    col_scaled_vals: List[float] = []
    log10_cond_vals: List[float] = []
    beat_mask: List[bool] = []

    for m in ms:
        M = int(F[m + 2])  # F_{m+2}
        s2 = int(S2[m])
        # Col_m = S2(m)/4^m (float is fine at audit-window scales).
        col_scaled = float(M) * (float(s2) / float(4**m))
        beat = ((m + 2) % 3 == 0)
        cond = float(cond_by_m.get(m, float("nan")))
        log10_cond = float("nan") if (not math.isfinite(cond) or cond <= 0.0) else float(math.log10(cond))
        rows.append(
            Row(
                m=m,
                F_m2=M,
                col_scaled=col_scaled,
                beat_mod3=beat,
                hankel_cond=cond,
                hankel_log10_cond=log10_cond,
            )
        )
        col_scaled_vals.append(col_scaled)
        log10_cond_vals.append(log10_cond)
        beat_mask.append(bool(beat))

    # Write JSON.
    export_dir().mkdir(parents=True, exist_ok=True)
    jout = export_dir() / f"fold_collision_col_hankel_alignment_q{q}.json"
    payload = {
        "q": q,
        "d_q": d_q,
        "m_min": m_min,
        "m_max": m_max,
        "rows": [asdict(r) for r in rows],
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Plot.
    fig, ax1 = plt.subplots(figsize=(10, 4.2))
    ax1.plot(ms, col_scaled_vals, color="#1f77b4", marker="o", linewidth=1.6, markersize=4, label=r"$F_{m+2}\,\mathsf{Col}_m$")
    # Highlight beat points.
    ms_beat = [m for m, b in zip(ms, beat_mask, strict=True) if b]
    col_beat = [y for y, b in zip(col_scaled_vals, beat_mask, strict=True) if b]
    ax1.scatter(ms_beat, col_beat, color="#d62728", s=28, zorder=5, label=r"$m+2\equiv 0\ (\mathrm{mod}\ 3)$")
    ax1.set_xlabel("m")
    ax1.set_ylabel(r"$F_{m+2}\,\mathsf{Col}_m$")
    ax1.grid(True, alpha=0.25)

    ax2 = ax1.twinx()
    ax2.plot(
        ms,
        log10_cond_vals,
        color="#2ca02c",
        marker="s",
        linewidth=1.4,
        markersize=3.5,
        label=r"$\log_{10}\kappa(H_m)$",
    )
    ax2.set_ylabel(r"$\log_{10}\kappa(H_m)$")

    # Combined legend.
    h1, l1 = ax1.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax1.legend(h1 + h2, l1 + l2, loc="upper left", fontsize=9, frameon=True)

    ax1.set_title(f"Fold: collision scaling vs local Hankel conditioning (q={q}, d_q={d_q})")
    fig.tight_layout()

    png = export_dir() / f"fold_collision_col_hankel_alignment_q{q}.png"
    fig.savefig(png, dpi=160)
    plt.close(fig)

    # Write TeX snippet.
    tex = generated_dir() / f"fig_fold_collision_col_hankel_alignment_q{q}.tex"
    # Use path relative to paper root (main.tex location).
    png_rel = f"artifacts/export/{png.name}"
    write_figure_tex(tex, png_rel_path=png_rel, q=q, d_q=d_q)

    print(f"[col-hankel-align] wrote {jout}", flush=True)
    print(f"[col-hankel-align] wrote {png}", flush=True)
    print(f"[col-hankel-align] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

