#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Time correlation and intrinsic mixing scale for the 10-state sync-kernel.

Goal: provide a purely internal (no external input) time-scale readout.

We use the weighted transfer matrix family B_theta induced by the output-bit
observable e (edge label), and compute:
- Perron root lambda1(theta)
- subdominant modulus |lambda2(theta)|
- gap exponent g(theta) := -log(|lambda2|/lambda1)
- correlation time tau(theta) := 1/g(theta)

We also compute the state-level autocorrelation of the conditional mean
f(i) = E[e | X_t=i] under the equilibrium (Parry) Markov chain induced by B_theta.

Outputs:
- artifacts/export/sync_kernel_time_correlation.json
- artifacts/export/sync_kernel_time_correlation.png
- sections/generated/fig_sync_kernel_time_correlation.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Edge:
    src: str
    dst: str
    d: int
    e: int


STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]


def build_edges() -> List[Edge]:
    edges: List[Edge] = []
    for d in (0, 1, 2):
        edges.append(Edge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(Edge("100", f"00{d}", d, 1))
    edges += [
        Edge("001", "010", 0, 0),
        Edge("001", "100", 1, 0),
        Edge("001", "101", 2, 0),
        Edge("002", "11-1", 0, 0),
        Edge("002", "000", 1, 1),
        Edge("002", "001", 2, 1),
        Edge("010", "100", 0, 0),
        Edge("010", "101", 1, 0),
        Edge("010", "0-12", 2, 1),
        Edge("101", "010", 0, 1),
        Edge("101", "100", 1, 1),
        Edge("101", "101", 2, 1),
        Edge("0-12", "01-1", 0, 0),
        Edge("0-12", "010", 1, 0),
        Edge("0-12", "100", 2, 0),
        Edge("1-12", "01-1", 0, 1),
        Edge("1-12", "010", 1, 1),
        Edge("1-12", "100", 2, 1),
        Edge("01-1", "001", 0, 0),
        Edge("01-1", "002", 1, 0),
        Edge("01-1", "1-12", 2, 0),
        Edge("11-1", "001", 0, 1),
        Edge("11-1", "002", 1, 1),
        Edge("11-1", "1-12", 2, 1),
    ]
    return edges


def weighted_matrix(theta: float, edges: List[Edge]) -> np.ndarray:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    B = np.zeros((n, n), dtype=float)
    for edge in edges:
        i = idx[edge.src]
        j = idx[edge.dst]
        B[i, j] += math.exp(theta * float(edge.e))
    return B


def _pick_pf_eigpair(B: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray, np.ndarray]:
    """Return (lambda1, eigvals, right_vec, left_vec) for the Perron root."""
    eigvals, eigvecs = np.linalg.eig(B)
    k = int(np.argmax(np.abs(eigvals)))
    lam = float(np.real(eigvals[k]))
    v = np.real(eigvecs[:, k])

    eigvals_t, eigvecs_t = np.linalg.eig(B.T)
    kt = int(np.argmax(np.abs(eigvals_t)))
    u = np.real(eigvecs_t[:, kt])

    # Fix signs.
    if float(np.sum(v)) < 0:
        v = -v
    if float(np.sum(u)) < 0:
        u = -u
    return lam, eigvals, v, u


def parry_markov(
    B: np.ndarray, lam: float, v: np.ndarray, u: np.ndarray
) -> Tuple[np.ndarray, np.ndarray]:
    """Return (pi, P) for the Parry chain induced by primitive nonnegative B."""
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
    # Normalize rows to protect against drift.
    rs = np.sum(P, axis=1)
    P = (P.T / rs).T
    return pi, P


def output_bit_conditional_mean(
    theta: float, edges: List[Edge], lam: float, v: np.ndarray
) -> np.ndarray:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    out = np.zeros(n, dtype=float)
    denom = np.maximum(v, 1e-300)
    for edge in edges:
        i = idx[edge.src]
        j = idx[edge.dst]
        w = math.exp(theta * float(edge.e))
        out[i] += w * float(edge.e) * float(v[j])
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

    cur = fc.copy()  # P^n fc
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
        description="Time correlation scale for sync-kernel (10-state)"
    )
    parser.add_argument("--theta-min", type=float, default=-2.0)
    parser.add_argument("--theta-max", type=float, default=2.0)
    parser.add_argument("--theta-steps", type=int, default=81)
    parser.add_argument("--corr-n", type=int, default=60)
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-time-corr", every_seconds=20.0)
    edges = build_edges()

    thetas = (
        [0.0]
        if args.theta_steps <= 1
        else [
            args.theta_min
            + (args.theta_max - args.theta_min) * i / float(args.theta_steps - 1)
            for i in range(args.theta_steps)
        ]
    )

    grid: List[Dict[str, float]] = []
    for th in thetas:
        B = weighted_matrix(theta=th, edges=edges)
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
                "theta": float(th),
                "lambda1": float(lam),
                "lambda2_abs": float(lam2),
                "r": r,
                "gap": gap,
                "tau": tau,
                "half": half,
            }
        )
        prog.tick(f"grid theta={th:.4g}")

    # A representative autocorrelation at theta=0.
    th0 = 0.0
    B0 = weighted_matrix(theta=th0, edges=edges)
    lam0, _, v0, u0 = _pick_pf_eigpair(B0)
    pi0, P0 = parry_markov(B0, lam=lam0, v=v0, u=u0)
    f0 = output_bit_conditional_mean(theta=th0, edges=edges, lam=lam0, v=v0)
    ns, corr = autocorr(pi0, P0, f0, n_max=args.corr_n)

    # Pull r(0) for the envelope.
    r0 = next((x["r"] for x in grid if abs(x["theta"]) < 1e-12), 0.0)
    env = [(r0**n) for n in ns]

    # Plot.
    out_png = export_dir() / "sync_kernel_time_correlation.png"
    fig, ax = plt.subplots(1, 2, figsize=(10.8, 4.2))

    ax[0].plot([g["theta"] for g in grid], [g["tau"] for g in grid], lw=2.0)
    ax[0].set_xlabel(r"$\theta$")
    ax[0].set_ylabel(r"$\tau(\theta)=1/(-\log(|\lambda_2|/\lambda_1))$")
    ax[0].set_title("Correlation time from spectral gap")
    ax[0].grid(True, alpha=0.3)

    ax[1].plot(ns, [abs(x) for x in corr], lw=2.0, label=r"$|\mathrm{Corr}(n)|$")
    ax[1].plot(ns, env, lw=1.5, ls="--", label=r"$(|\lambda_2|/\lambda_1)^n$")
    ax[1].set_yscale("log")
    ax[1].set_xlabel("n")
    ax[1].set_ylabel("abs correlation (log scale)")
    ax[1].set_title("theta=0 (Parry measure)")
    ax[1].grid(True, alpha=0.3)
    ax[1].legend(loc="upper right", fontsize=9)

    plt.tight_layout()
    if not args.no_output:
        out_png.parent.mkdir(parents=True, exist_ok=True)
        plt.savefig(out_png, dpi=160)
    plt.close(fig)

    payload: Dict[str, object] = {
        "model": "sync_kernel_10_state",
        "observable": "output_bit",
        "theta_grid": grid,
        "theta0": {
            "theta": 0.0,
            "corr_n": ns,
            "corr": corr,
            "r": r0,
        },
    }

    out_json = export_dir() / "sync_kernel_time_correlation.json"
    if not args.no_output:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(
            json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
        )
        write_fig_tex(
            fig_name="fig_sync_kernel_time_correlation",
            png_rel="artifacts/export/sync_kernel_time_correlation.png",
            caption=(
                "无外部输入（核内在动力学）下的时间尺度读出：左为输出位势 $e$ 的一维倾斜族 "
                "$B_\\theta$ 的谱隙给出的相关时间 $\\tau(\\theta)$；右为 $\\theta=0$ 的 Parry 测度下，"
                "状态条件均值 $f(i)=\\mathbb{E}[e\\mid X_t=i]$ 的归一化自相关随 $n$ 衰减，并与 "
                "$(|\\lambda_2|/\\lambda_1)^n$ 的指数包络一致。"
            ),
            label="fig:sync-kernel-time-correlation",
        )

    print(f"[sync-kernel-time-corr] wrote {out_json}", flush=True)
    print(f"[sync-kernel-time-corr] wrote {out_png}", flush=True)
    print("[sync-kernel-time-corr] done", flush=True)


if __name__ == "__main__":
    main()
