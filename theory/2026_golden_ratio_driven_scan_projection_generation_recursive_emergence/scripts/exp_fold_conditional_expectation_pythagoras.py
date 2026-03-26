#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify the L2 Pythagoras identity for Fold-induced conditional expectation.

All code is English-only by repository convention.

This script is deterministic and produces:
- artifacts/export/fold_conditional_expectation_pythagoras.json
- sections/generated/tab_fold_conditional_expectation_pythagoras.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, PHI, fib_upto, fold_m, is_golden_legal, parry_pi_m


def int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def bits_to_key(bits: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in bits)


def fib_weights_for_value(m: int) -> List[int]:
    """Return weights w_k = F_{k+1} for k=1..m as a list of length m."""
    fib = fib_upto(m + 2)
    return [fib[k] for k in range(1, m + 1)]


def micro_value(micro: Sequence[int], w: Sequence[int]) -> int:
    return sum(int(b) * int(wi) for b, wi in zip(micro, w))


@dataclass(frozen=True)
class Row:
    m: int
    omega: int
    X: int
    d_min: int
    d_max: int
    mean_f: float
    mean_Ef: float
    l2_f: float
    l2_Ef: float
    l2_res: float
    pyth_err: float
    ortho_max_inner: float


def compute_for_m(m: int, prog: Progress) -> Row:
    w = fib_weights_for_value(m)

    fibers: Dict[str, List[int]] = {}
    micro_to_x: List[str] = [""] * (1 << m)
    f_vals: List[float] = [0.0] * (1 << m)

    # Normalize micro-value to O(1) range.
    # Max sum of weights is F_{m+3}-1, so divide by F_{m+3}.
    fib = fib_upto(m + 3)
    scale = float(fib[m + 2])  # F_{m+3}

    for idx in range(1 << m):
        if idx % (1 << 14) == 0:
            prog.tick(f"m={m} enumerate idx={idx}/{1 << m}")

        micro = int_to_bits(idx, m)
        x_bits = fold_m(micro)
        if not is_golden_legal(x_bits):
            raise RuntimeError("Fold_m produced an illegal golden word")
        x = bits_to_key(x_bits)

        micro_to_x[idx] = x
        fibers.setdefault(x, []).append(idx)

        N = micro_value(micro, w)
        f_vals[idx] = float(N) / scale

    X = len(fibers)
    d_sizes = [len(v) for v in fibers.values()]
    d_min = min(d_sizes)
    d_max = max(d_sizes)

    # Parry (max-entropy) cylinder distribution over X_m.
    pi_x: Dict[str, float] = {}
    pi_sum = 0.0
    for x in fibers.keys():
        bits = [1 if c == "1" else 0 for c in x]
        px = parry_pi_m(bits)
        pi_x[x] = px
        pi_sum += px
    if not math.isfinite(pi_sum) or abs(pi_sum - 1.0) > 1e-10:
        raise RuntimeError(f"Parry cylinder mass mismatch at m={m}: sum={pi_sum}")

    # Fiber-uniform lifted micro distribution: mu(a)=pi(Fold(a))/d(Fold(a)).
    mu: List[float] = [0.0] * (1 << m)
    for x, idxs in fibers.items():
        px = pi_x[x]
        d = float(len(idxs))
        for idx in idxs:
            mu[idx] = px / d
    mu_sum = sum(mu)
    if abs(mu_sum - 1.0) > 1e-12:
        raise RuntimeError(f"mu mass mismatch at m={m}: sum={mu_sum}")

    # E_m f = fiber average (uniform within fiber).
    Ef: List[float] = [0.0] * (1 << m)
    for x, idxs in fibers.items():
        avg = sum(f_vals[i] for i in idxs) / float(len(idxs))
        for i in idxs:
            Ef[i] = avg

    # Compute means and L2 norms.
    mean_f = sum(mu[i] * f_vals[i] for i in range(1 << m))
    mean_Ef = sum(mu[i] * Ef[i] for i in range(1 << m))

    l2_f = math.sqrt(sum(mu[i] * (f_vals[i] ** 2) for i in range(1 << m)))
    l2_Ef = math.sqrt(sum(mu[i] * (Ef[i] ** 2) for i in range(1 << m)))
    l2_res = math.sqrt(sum(mu[i] * ((f_vals[i] - Ef[i]) ** 2) for i in range(1 << m)))
    pyth_err = abs((l2_f**2) - (l2_Ef**2 + l2_res**2))

    # Orthogonality check against a spanning family of B_m: indicators of fibers.
    # For each x, g=1_{Fold=a->x} is constant on fiber. We test <f-Ef, g>.
    ortho_max_inner = 0.0
    for x, idxs in fibers.items():
        inner = sum(mu[i] * (f_vals[i] - Ef[i]) for i in idxs)
        ortho_max_inner = max(ortho_max_inner, abs(inner))

    return Row(
        m=m,
        omega=(1 << m),
        X=X,
        d_min=d_min,
        d_max=d_max,
        mean_f=mean_f,
        mean_Ef=mean_Ef,
        l2_f=l2_f,
        l2_Ef=l2_Ef,
        l2_res=l2_res,
        pyth_err=pyth_err,
        ortho_max_inner=ortho_max_inner,
    )


def write_tex_table(rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{折叠条件期望 $E_m$ 的 $L^2$ 正交分解数值核对。对每个 $m$：取 $\\pi$ 为黄金均值 Parry 最大熵测度在 $X_m$ 上的柱分布，取 $\\mu=Q_m\\pi$ 为纤维均匀提升到 $\\Omega_m$ 的分布；令 $f(a)$ 为窗口值 $N(a)$ 的归一化（除以 $F_{m+3}$），计算 $\\|f\\|_2^2$、$\\|E_m f\\|_2^2$ 与残差 $\\|f-E_m f\\|_2^2$，并报告毕达哥拉斯误差 $\\bigl|\\|f\\|_2^2-(\\|E_m f\\|_2^2+\\|f-E_m f\\|_2^2)\\bigr|$ 与正交性核对 $\\max_x|\\langle f-E_m f,\\ind_{\\Fold_m^{-1}(x)}\\rangle|$。}"
    )
    lines.append("\\label{tab:fold_conditional_expectation_pythagoras}")
    lines.append("\\begin{tabular}{rrrrrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $|\\Omega_m|$ & $|X_m|$ & $d_{\\min}$ & $d_{\\max}$ & $\\|f\\|_2$ & $\\|E_m f\\|_2$ & $\\|f-E_m f\\|_2$ & pyth err & ortho err\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.omega} & {r.X} & {r.d_min} & {r.d_max} & {r.l2_f:.6g} & {r.l2_Ef:.6g} & {r.l2_res:.6g} & {r.pyth_err:.3g} & {r.ortho_max_inner:.3g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    out = generated_dir() / "tab_fold_conditional_expectation_pythagoras.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_condexp")
    ms = [4, 6, 8, 10, 12, 14, 16]

    rows: List[Row] = []
    for m in ms:
        rows.append(compute_for_m(m, prog))
        prog.tick(f"completed m={m}")

    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "phi": PHI,
        "ms": ms,
        "rows": [
            {
                "m": r.m,
                "omega": r.omega,
                "X": r.X,
                "d_min": r.d_min,
                "d_max": r.d_max,
                "mean_f": r.mean_f,
                "mean_Ef": r.mean_Ef,
                "l2_f": r.l2_f,
                "l2_Ef": r.l2_Ef,
                "l2_res": r.l2_res,
                "pyth_err": r.pyth_err,
                "ortho_max_inner": r.ortho_max_inner,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_conditional_expectation_pythagoras.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    write_tex_table(rows)
    print(
        f"[fold_condexp] OK rows={len(rows)} wall={time.time() - t0:.2f}s", flush=True
    )


if __name__ == "__main__":
    main()
