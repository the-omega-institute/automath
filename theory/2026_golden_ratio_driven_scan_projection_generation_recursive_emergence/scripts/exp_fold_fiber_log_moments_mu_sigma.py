#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute the mean-rate and variance-rate of log Fold fiber multiplicities.

We work with the Fold_m fibers of the Zeckendorf canonical projection:
  d_m(x) = |Fold_m^{-1}(x)|,   x in X_m.

Let X be sampled from the Fold output distribution pi_m(x) = d_m(x) / 2^m.
We compute the low-order cumulants of log d_m(X) under pi_m:
  mu_m      = (1/m) E[log d_m(X)],
  sigma2_m  = (1/m) Var(log d_m(X)).

We use modular DP on Z / F_{m+2} Z:
  c_m(r) = #{ omega in {0,1}^m : sum_{i=1..m} omega_i F_{i+1} == r (mod F_{m+2}) }.
Under the Fold congruence model, c_m(r) is exactly the fiber size d_m(x) for the
unique stable type x whose value is r mod F_{m+2}. Hence:
  E[log d_m(X)] = (1/2^m) sum_r c_m(r) log c_m(r),
and similarly for the second moment.

Outputs:
- artifacts/export/fold_fiber_log_moments_mu_sigma.json
- sections/generated/tab_fold_fiber_log_moments_mu_sigma.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from typing import Dict, List

import numpy as np

from common_mod_fib_dp import counts_mod_fib
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Row:
    m: int
    mu_m: float
    sigma2_m: float
    elog: float
    varlog: float
    min_c: int
    max_c: int


def summarize_c(m: int, c: np.ndarray) -> Row:
    total = float(1 << m)
    cf = c.astype(np.float64)
    mask = cf > 0.0
    if not bool(np.all(mask)):
        # In principle should not happen for Fold_m (|X_m|=F_{m+2} types).
        cf = cf[mask]

    logc = np.log(cf)
    elog = float(np.sum(cf * logc) / total)
    elog2 = float(np.sum(cf * (logc**2)) / total)
    varlog = float(max(0.0, elog2 - elog * elog))

    mu_m = elog / float(m) if m > 0 else 0.0
    sigma2_m = varlog / float(m) if m > 0 else 0.0
    return Row(
        m=m,
        mu_m=mu_m,
        sigma2_m=sigma2_m,
        elog=elog,
        varlog=varlog,
        min_c=int(np.min(c)),
        max_c=int(np.max(c)),
    )


def write_tex_table(path: str, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{折叠纤维对数多重度 $\\log d_m(X)$ 的均值率 $\\mu_m=(1/m)\\,\\mathbb{E}_{\\pi_m}[\\log d_m(X)]$ 与方差率 $\\sigma_m^2=(1/m)\\,\\mathrm{Var}_{\\pi_m}(\\log d_m(X))$（$X\\sim\\pi_m$，其中 $\\pi_m(x)=d_m(x)/2^m$）。数值由模 $F_{m+2}$ 的 residue DP 精确计算。}"
    )
    lines.append("\\label{tab:fold_fiber_log_moments_mu_sigma}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $\\mu_m$ & $\\sigma_m^2$ & $\\mathbb{E}[\\log d]$ & $\\mathrm{Var}(\\log d)$ & $d_{\\min}$ & $d_{\\max}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.mu_m:.6f} & {r.sigma2_m:.6f} & {r.elog:.6f} & {r.varlog:.6f} & {r.min_c} & {r.max_c}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    p = generated_dir() / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    ap = argparse.ArgumentParser()
    ap.add_argument("--m-min", type=int, default=8)
    ap.add_argument("--m-max", type=int, default=30)
    ap.add_argument("--m-step", type=int, default=2)
    args = ap.parse_args()

    if args.m_min < 1 or args.m_max < args.m_min or args.m_step <= 0:
        raise ValueError("Invalid m range/step")

    prog = Progress("fold_logmom", every_seconds=20.0)
    rows: List[Row] = []

    for m in range(args.m_min, args.m_max + 1, args.m_step):
        c = counts_mod_fib(m, prog)
        rows.append(summarize_c(m, c))

    export_dir().mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "m_min": args.m_min,
        "m_max": args.m_max,
        "m_step": args.m_step,
        "rows": [
            {
                "m": r.m,
                "mu_m": r.mu_m,
                "sigma2_m": r.sigma2_m,
                "E_log_d": r.elog,
                "Var_log_d": r.varlog,
                "d_min": r.min_c,
                "d_max": r.max_c,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_fiber_log_moments_mu_sigma.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    write_tex_table("tab_fold_fiber_log_moments_mu_sigma.tex", rows)
    dt = time.time() - t0
    print(f"[fold_logmom] done in {dt:.2f}s, rows={len(rows)}", flush=True)


if __name__ == "__main__":
    main()

