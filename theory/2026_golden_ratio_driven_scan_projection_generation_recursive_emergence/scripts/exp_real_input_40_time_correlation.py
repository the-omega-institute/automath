#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Time correlation and intrinsic mixing scale for the real-input 40-state kernel.

We focus on the arity-charge slice theta(t)=(t,0,-t), where the edge weight is
exp(t * chi) with chi = e - 1_{d=2} in {-1,0,1}.

Outputs (default tag=""):
- artifacts/export/real_input_40_time_correlation.json
- artifacts/export/real_input_40_time_correlation.png
- sections/generated/fig_real_input_40_time_correlation.tex

With --tag TAG (non-empty), outputs are suffixed by _TAG.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix,
)


def _pick_pf_eigpair(B: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray, np.ndarray]:
    eigvals, eigvecs = np.linalg.eig(B)
    k = int(np.argmax(np.abs(eigvals)))
    lam = float(np.real(eigvals[k]))
    v = np.real(eigvecs[:, k])

    eigvals_t, eigvecs_t = np.linalg.eig(B.T)
    kt = int(np.argmax(np.abs(eigvals_t)))
    u = np.real(eigvecs_t[:, kt])

    if float(np.sum(v)) < 0:
        v = -v
    if float(np.sum(u)) < 0:
        u = -u
    return lam, eigvals, v, u


def parry_markov(
    B: np.ndarray, lam: float, v: np.ndarray, u: np.ndarray
) -> Tuple[np.ndarray, np.ndarray]:
    n = B.shape[0]
    v = np.maximum(v, 1e-300)
    u = np.maximum(u, 1e-300)
    pi_unnorm = u * v
    pi = pi_unnorm / float(np.sum(pi_unnorm))

    P = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            if B[i, j] == 0.0:
                continue
            P[i, j] = (B[i, j] * v[j]) / (lam * v[i])
    rs = np.sum(P, axis=1)
    P = (P.T / rs).T
    return pi, P


def chi_conditional_mean(
    t: float,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    lam: float,
    v: np.ndarray,
) -> np.ndarray:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    out = np.zeros(n, dtype=float)
    denom = np.maximum(v, 1e-300)

    for s, px, py in states:
        i = idx[(s, px, py)]
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                j = idx[(dst_state, x, y)]
                two = 1 if d == 2 else 0
                chi = int(e) - int(two)
                w = math.exp(float(t) * float(chi))
                out[i] += w * float(chi) * float(v[j])

    out = out / (lam * denom)
    return out


def autocorr(
    pi: np.ndarray, P: np.ndarray, f: np.ndarray, n_max: int
) -> Tuple[List[int], List[float]]:
    mu = float(np.dot(pi, f))
    fc = f - mu
    var0 = float(np.dot(pi, fc * fc))
    if var0 <= 0.0:
        return list(range(n_max + 1)), [0.0] * (n_max + 1)

    cur = fc.copy()
    out: List[float] = []
    for _ in range(n_max + 1):
        c = float(np.dot(pi, fc * cur))
        out.append(c / var0)
        cur = P @ cur
    return list(range(n_max + 1)), out


def write_fig_tex(fig_name: str, png_rel: str, caption: str, label: str) -> None:
    p = generated_dir() / f"{fig_name}.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n",
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Time correlation for real-input 40-state kernel (chi slice)"
    )
    parser.add_argument("--t-min", type=float, default=-1.0)
    parser.add_argument("--t-max", type=float, default=1.0)
    parser.add_argument("--t-steps", type=int, default=61)
    parser.add_argument("--corr-n", type=int, default=80)
    parser.add_argument("--tag", type=str, default="")
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    prog = Progress(label="real-input-40-time-corr", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    ts = (
        [0.0]
        if args.t_steps <= 1
        else [
            args.t_min + (args.t_max - args.t_min) * i / float(args.t_steps - 1)
            for i in range(args.t_steps)
        ]
    )

    grid: List[Dict[str, float]] = []
    for t in ts:
        B = build_weighted_matrix(
            theta_e=t, theta_neg=0.0, theta_2=-t, states=states, kernel_map=kernel_map
        )
        lam, eigvals, v, u = _pick_pf_eigpair(B)
        mags = np.sort(np.abs(eigvals))[::-1]
        lam2 = float(mags[1]) if len(mags) >= 2 else 0.0
        r = float(lam2 / lam) if lam > 0.0 else 0.0
        r = min(max(r, 0.0), 1.0)
        gap = float(-math.log(r)) if 0.0 < r < 1.0 else float("inf")
        tau = float(1.0 / gap) if math.isfinite(gap) and gap > 0.0 else float("inf")
        half = (
            float(math.log(2.0) / gap)
            if math.isfinite(gap) and gap > 0.0
            else float("inf")
        )
        grid.append(
            {
                "t": float(t),
                "lambda1": float(lam),
                "lambda2_abs": float(lam2),
                "r": r,
                "gap": gap,
                "tau": tau,
                "half": half,
            }
        )
        prog.tick(f"grid t={t:.4g}")

    # Autocorrelation at t=0 (chi observable).
    t0 = 0.0
    B0 = build_weighted_matrix(
        theta_e=t0, theta_neg=0.0, theta_2=-t0, states=states, kernel_map=kernel_map
    )
    lam0, eigvals0, v0, u0 = _pick_pf_eigpair(B0)
    pi0, P0 = parry_markov(B0, lam=lam0, v=v0, u=u0)
    f0 = chi_conditional_mean(
        t=t0, states=states, kernel_map=kernel_map, lam=lam0, v=v0
    )
    ns, corr = autocorr(pi0, P0, f0, n_max=args.corr_n)

    r0 = next((x["r"] for x in grid if abs(x["t"]) < 1e-12), 0.0)
    env = [(r0**n) for n in ns]

    tag = str(args.tag).strip()
    suffix = f"_{tag}" if tag else ""
    out_png = export_dir() / f"real_input_40_time_correlation{suffix}.png"
    fig, ax = plt.subplots(1, 2, figsize=(10.8, 4.2))

    ax[0].plot([g["t"] for g in grid], [g["tau"] for g in grid], lw=2.0)
    ax[0].set_xlabel(r"$t$")
    ax[0].set_ylabel(r"$\tau(t)=1/(-\log(\Lambda/\lambda_1))$")
    ax[0].set_title("chi-slice correlation time")
    ax[0].grid(True, alpha=0.3)

    ax[1].plot(ns, [abs(x) for x in corr], lw=2.0, label=r"$|\mathrm{Corr}(n)|$")
    ax[1].plot(ns, env, lw=1.5, ls="--", label=r"$(\Lambda/\lambda_1)^n$")
    ax[1].set_yscale("log")
    ax[1].set_xlabel("n")
    ax[1].set_ylabel("abs correlation (log scale)")
    ax[1].set_title("t=0 (Parry measure)")
    ax[1].grid(True, alpha=0.3)
    ax[1].legend(loc="upper right", fontsize=9)

    plt.tight_layout()
    if not args.no_output:
        out_png.parent.mkdir(parents=True, exist_ok=True)
        plt.savefig(out_png, dpi=160)
    plt.close(fig)

    out_json = export_dir() / f"real_input_40_time_correlation{suffix}.json"
    payload: Dict[str, object] = {
        "model": "real_input_40",
        "slice": "chi",
        "theta_map": "theta(t)=(t,0,-t)",
        "grid": grid,
        "t0": {
            "t": 0.0,
            "lambda1": float(lam0),
            "eigvals_abs_sorted": [
                float(x) for x in np.sort(np.abs(eigvals0))[::-1][:12]
            ],
        },
        "corr": {"n": ns, "corr": corr, "r": float(r0)},
    }
    if not args.no_output:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(
            json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
        )
        fig_name = f"fig_real_input_40_time_correlation{suffix}"
        png_rel = f"artifacts/export/real_input_40_time_correlation{suffix}.png"
        fig_label = (
            f"fig:real-input-40-time-correlation-{tag}"
            if tag
            else "fig:real-input-40-time-correlation"
        )
        write_fig_tex(
            fig_name=fig_name,
            png_rel=png_rel,
            caption=(
                "真实输入 40 状态核在 arity-charge 切片 $\\theta(t)=(t,0,-t)$ 下的内生时间尺度读出："
                "左为谱隙比 $\\Lambda/\\lambda_1$ 导出的相关时间 $\\tau_{\\mathrm{corr}}(t)$；右为 $t=0$ 的 Parry 测度下，"
                "一步势 $\\chi=e-\\mathbf{1}_{\\{d=2\\}}$ 的状态条件均值自相关的指数衰减（取绝对值），并与 "
                "$(\\Lambda/\\lambda_1)^n$ 的指数包络一致。"
            ),
            label=fig_label,
        )

    print(f"[real-input-40-time-corr] wrote {out_json}", flush=True)
    print(f"[real-input-40-time-corr] wrote {out_png}", flush=True)
    print("[real-input-40-time-corr] done", flush=True)


if __name__ == "__main__":
    main()
