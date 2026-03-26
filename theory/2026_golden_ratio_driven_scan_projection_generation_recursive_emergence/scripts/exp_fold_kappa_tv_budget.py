#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Deterministic budget formulas: TV confidence -> sample complexity -> kappa radius.

We only compute the closed-form RHS quantities (budgets). This is intended as an
auditable engineering table for the manuscript (no stochastic claims are
validated here).

Model parameters:
- state size: |X_m| = F_{m+2} (golden-mean length-m language)
- max fiber multiplicity D_m from the closed form in the paper
- Markov pseudo spectral gap gamma_ps (user-supplied; baseline default 1/phi)

Given (tau, delta), the sufficient sample size from the Markov TV envelope:
  N >= (|X_m|^2 / (2 * gamma_ps * tau^2)) * log( 2|X_m| / delta )

If D_TV <= tau, then for kappa_m(pi) = E_pi[log d_m(X)]:
  |kappa_m(hat pi) - kappa_m(pi)| <= 2 * ||log d_m||_inf * D_TV
                               <= 2 * log D_m * tau.

Outputs:
- artifacts/export/fold_kappa_tv_budget.json
- sections/generated/tab_fold_kappa_tv_budget.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir


PHI = (1.0 + 5.0**0.5) / 2.0


def fib0_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [0]
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def X_size(m: int) -> int:
    """|X_m| for golden-mean length-m words: F_{m+2}."""
    F = fib0_upto(m + 2)
    return int(F[m + 2])


def D_max_fiber(m: int) -> int:
    """Closed form for D_m from the manuscript theorem (max Fold fiber).

    Uses F_0=0,F_1=1.
    For m=2k:   D_{2k}   = F_{k+2}
    For m=2k+1: D_{2k+1} = 2 F_{k+1}
    """
    if m < 2:
        raise ValueError("m must be >= 2 for D_m formula")
    k = m // 2
    # Need Fibonacci up to k+2.
    F = fib0_upto(k + 2)
    if m % 2 == 0:
        return int(F[k + 2])
    return int(2 * F[k + 1])


@dataclass(frozen=True)
class Row:
    m: int
    X: int
    D: int
    logD: float
    tau: float
    delta: float
    gamma_ps: float
    N_min: int
    kappa_radius: float


def N_min_for_tv(X: int, tau: float, delta: float, gamma_ps: float) -> int:
    if not (0.0 < tau < 1.0):
        raise ValueError("tau must be in (0,1)")
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must be in (0,1)")
    if not (0.0 < gamma_ps <= 1.0):
        raise ValueError("gamma_ps must be in (0,1]")
    rhs = (float(X) ** 2) / (2.0 * gamma_ps * (tau**2)) * math.log((2.0 * float(X)) / delta)
    return int(math.ceil(rhs))


def write_tex_table(rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Markov-TV 置信包络下的样本预算与 $\\kappa_m$ 置信半径（确定性右端）。设 $|X_m|=F_{m+2}$，$D_m=\\max_x d_m(x)$，并给定伪谱隙参数 $\\gamma^{(m)}_{\\mathrm{ps}}$。若希望以置信度 $1-\\delta$ 达到 $D_{\\mathrm{TV}}(\\hat\\pi_{m,N},\\pi)\\le \\tau$，则充分条件为 $N\\ge \\frac{|X_m|^2}{2\\gamma^{(m)}_{\\mathrm{ps}}\\tau^2}\\log\\frac{2|X_m|}{\\delta}$；并且在同一事件下 $|\\kappa_m(\\hat\\pi)-\\kappa_m(\\pi)|\\le 2\\log D_m\\cdot \\tau$。本表取一组示例参数（仅计算右端，不对概率事件做数值验证）。}"
    )
    lines.append("\\label{tab:fold_kappa_tv_budget}")
    lines.append("\\begin{tabular}{r r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $|X_m|$ & $D_m$ & $\\log D_m$ & $\\tau$ & $\\delta$ & $\\gamma_{\\mathrm{ps}}$ & $N_{\\min}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.X} & {r.D} & {r.logD:.6f} & {r.tau:.3g} & {r.delta:.1g} & {r.gamma_ps:.6f} & {r.N_min}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out = generated_dir() / "tab_fold_kappa_tv_budget.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    ap = argparse.ArgumentParser()
    ap.add_argument("--m-list", type=str, default="8,10,12,14,16")
    ap.add_argument("--tau", type=float, default=0.02)
    ap.add_argument("--delta", type=float, default=1e-6)
    ap.add_argument("--gamma-ps", type=float, default=1.0 / PHI)  # baseline
    args = ap.parse_args()

    ms = [int(x.strip()) for x in args.m_list.split(",") if x.strip()]
    rows: List[Row] = []
    for m in ms:
        X = X_size(m)
        D = D_max_fiber(m)
        logD = math.log(float(D))
        Nmin = N_min_for_tv(X=X, tau=args.tau, delta=args.delta, gamma_ps=args.gamma_ps)
        kappa_radius = 2.0 * logD * args.tau
        rows.append(
            Row(
                m=m,
                X=X,
                D=D,
                logD=logD,
                tau=args.tau,
                delta=args.delta,
                gamma_ps=args.gamma_ps,
                N_min=Nmin,
                kappa_radius=kappa_radius,
            )
        )

    export_dir().mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "params": {
            "m_list": ms,
            "tau": args.tau,
            "delta": args.delta,
            "gamma_ps": args.gamma_ps,
        },
        "rows": [
            {
                "m": r.m,
                "X": r.X,
                "D": r.D,
                "logD": r.logD,
                "tau": r.tau,
                "delta": r.delta,
                "gamma_ps": r.gamma_ps,
                "N_min": r.N_min,
                "kappa_radius": r.kappa_radius,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_kappa_tv_budget.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_tex_table(rows)
    dt = time.time() - t0
    print(f"[fold_kappa_tv_budget] done in {dt:.2f}s rows={len(rows)}", flush=True)


if __name__ == "__main__":
    main()

