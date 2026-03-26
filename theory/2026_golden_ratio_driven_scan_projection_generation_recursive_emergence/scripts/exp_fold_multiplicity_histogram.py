#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute Fold_m fiber multiplicity histograms for small m.

All code is English-only by repository convention.

This script is deterministic and produces:
- artifacts/export/fold_multiplicity_histogram.json
- sections/generated/tab_fold_multiplicity_histogram.tex
"""

from __future__ import annotations

import json
import math
import time
from collections import Counter
from dataclasses import dataclass
from typing import Dict, List, Sequence

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, is_golden_legal


def int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def bits_to_key(bits: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in bits)


@dataclass(frozen=True)
class Row:
    m: int
    omega: int
    X: int
    d_min: int
    d_max: int
    size_hist: Dict[int, int]
    E_log2_d: float
    I_bits: float
    log2_X: float
    gap_to_capacity: float
    col: float
    c_col: float
    log2_c_col: float


def compute_row(m: int, prog: Progress) -> Row:
    fibers: Dict[str, int] = {}

    for idx in range(1 << m):
        if idx % (1 << 14) == 0:
            prog.tick(f"m={m} enumerate idx={idx}/{1<<m}")
        micro = int_to_bits(idx, m)
        x_bits = fold_m(micro)
        if not is_golden_legal(x_bits):
            raise RuntimeError("Fold_m produced an illegal golden word")
        x = bits_to_key(x_bits)
        fibers[x] = fibers.get(x, 0) + 1

    sizes = list(fibers.values())
    d_min = min(sizes)
    d_max = max(sizes)
    hist = dict(sorted(Counter(sizes).items()))

    Z = 1 << m
    # Uniform micro distribution: pi(x)=d(x)/2^m, hence E[log2 d(X)] = sum_x d(x)/2^m * log2 d(x).
    E_log2_d = sum((d / Z) * math.log2(d) for d in sizes)
    I_bits = float(m) - E_log2_d
    log2_X = math.log2(len(fibers))
    gap_to_capacity = log2_X - I_bits

    # Collision probability and its inflation factor relative to uniform on X_m.
    sum_d2 = sum(d * d for d in sizes)
    col = sum_d2 / float(Z * Z)
    c_col = float(len(fibers)) * col
    log2_c_col = math.log2(c_col)

    return Row(
        m=m,
        omega=Z,
        X=len(fibers),
        d_min=d_min,
        d_max=d_max,
        size_hist=hist,
        E_log2_d=E_log2_d,
        I_bits=I_bits,
        log2_X=log2_X,
        gap_to_capacity=gap_to_capacity,
        col=col,
        c_col=c_col,
        log2_c_col=log2_c_col,
    )


def hist_to_tex(hist: Dict[int, int]) -> str:
    # Format like: 1:2, 2:4, 3:8
    parts = [f"{k}:{v}" for k, v in hist.items()]
    return "$" + ",\\, ".join(parts) + "$"


def write_table(rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{折叠纤维多重度的尺寸直方图与“隐藏比特预算”（均匀微态口径）。对每个 $m$：枚举 $\\Omega_m=\\{0,1\\}^m$，计算 $d_m(x)=|\\Fold_m^{-1}(x)|$ 的直方图；并在微态均匀分布下（故 $\\pi(x)=d_m(x)/2^m$）给出 $\\mathbb{E}[\\log_2 d_m(X)]$（隐藏比特）、$I(A;X)=m-\\mathbb{E}[\\log_2 d_m(X)]$（可见比特）、与容量 $\\log_2|X_m|$ 的差距（gap），以及二阶均匀性指纹 $C_{\\mathrm{col}}(m):=|X_m|\\sum_x\\pi(x)^2$ 与其对数。}"
    )
    lines.append("\\label{tab:fold_multiplicity_histogram}")
    lines.append("\\begin{tabular}{rrrrrlrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $|\\Omega_m|$ & $|X_m|$ & $d_{\\min}$ & $d_{\\max}$ & size hist $\\{d: \\#x\\}$ & $\\mathbb{E}[\\log_2 d]$ & $I(A;X)$ & $\\log_2|X_m|$ & gap & $C_{\\mathrm{col}}$ & $\\log_2 C_{\\mathrm{col}}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.omega} & {r.X} & {r.d_min} & {r.d_max} & {hist_to_tex(r.size_hist)} & {r.E_log2_d:.6f} & {r.I_bits:.6f} & {r.log2_X:.6f} & {r.gap_to_capacity:.6f} & {r.c_col:.6f} & {r.log2_c_col:.6f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    out = generated_dir() / "tab_fold_multiplicity_histogram.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_mult_hist")
    ms = [4, 6, 8, 10, 12, 14, 16]

    rows: List[Row] = []
    for m in ms:
        rows.append(compute_row(m, prog))
        prog.tick(f"completed m={m}")

    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "ms": ms,
        "rows": [
            {
                "m": r.m,
                "omega": r.omega,
                "X": r.X,
                "d_min": r.d_min,
                "d_max": r.d_max,
                "size_hist": r.size_hist,
                "E_log2_d": r.E_log2_d,
                "I_bits": r.I_bits,
                "log2_X": r.log2_X,
                "gap_to_capacity": r.gap_to_capacity,
                "col": r.col,
                "c_col": r.c_col,
                "log2_c_col": r.log2_c_col,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_multiplicity_histogram.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    write_table(rows)
    print(
        f"[fold_mult_hist] OK rows={len(rows)} wall={time.time() - t0:.2f}s", flush=True
    )


if __name__ == "__main__":
    main()

