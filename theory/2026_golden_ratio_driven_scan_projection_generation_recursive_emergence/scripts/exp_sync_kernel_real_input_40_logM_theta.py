#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute a phase diagram for log(Mfrak(theta)) on the real-input 40-state kernel.

This implements the Abel finite-part interface using the closed Möbius tail:

  P_theta(z) = sum_{k>=1} mu(k)/k * log zeta_theta(z^k)

  log Mfrak(theta) = log C(theta) + sum_{k>=2} mu(k)/k * log zeta_theta(z_star(theta)^k)

where z_star(theta)=1/lambda(theta), and C(theta) is the residue constant at the simple pole.

Outputs (default):
- artifacts/export/sync_kernel_real_input_40_logM_theta.json
- artifacts/export/sync_kernel_real_input_40_logM_theta.png
- sections/generated/fig_real_input_40_logM_theta.tex
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
from exp_sync_kernel_real_input_40 import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix,
    mobius,
    spectral_radius,
)


@dataclass(frozen=True)
class GridSpec:
    theta_e_min: float
    theta_e_max: float
    theta_e_steps: int
    theta_2_min: float
    theta_2_max: float
    theta_2_steps: int
    theta_neg: float


def linspace(min_val: float, max_val: float, steps: int) -> List[float]:
    if steps <= 1:
        return [0.5 * (min_val + max_val)]
    return [min_val + (max_val - min_val) * i / float(steps - 1) for i in range(steps)]


def log_zeta_from_matrix(M: np.ndarray, z: float) -> float:
    """Return log(zeta(z)) = -log(det(I - z M)), using slogdet."""
    n = M.shape[0]
    sign, logabs = np.linalg.slogdet(np.eye(n) - z * M)
    if sign == 0:
        raise ValueError("singular det in log_zeta_from_matrix")
    return -float(logabs)


def logC_from_eigvals(eigs: np.ndarray, lam_idx: int) -> float:
    """Compute log C(theta) from eigenvalues of M_theta.

    For a simple PF eigenvalue lambda, we have
      det(I - z M) = Π_j (1 - z λ_j),
    so at z_star = 1/lambda,
      C = lim_{z->z_star} (1 - lambda z) ζ(z)
        = 1 / Π_{j≠PF} (1 - λ_j / lambda).
    """
    lam = eigs[lam_idx]
    prod = 1.0 + 0.0j
    for j, ev in enumerate(eigs):
        if j == lam_idx:
            continue
        prod *= (1.0 - ev / lam)
    C = 1.0 / prod
    C_re = float(np.real(C))
    if not math.isfinite(C_re) or C_re <= 0.0:
        raise ValueError("invalid C(theta) from eigvals")
    return math.log(C_re)


def logM_theta(
    theta_e: float,
    theta_neg: float,
    theta_2: float,
    k_max: int,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    prog: Progress,
    tag: str,
) -> Tuple[float, float]:
    """Return (lambda(theta), log Mfrak(theta))."""
    M1 = build_weighted_matrix(theta_e, theta_neg, theta_2, states, kernel_map)
    eigs = np.linalg.eigvals(M1)
    lam_idx = int(np.argmax(np.abs(eigs)))
    lam = float(np.real(eigs[lam_idx]))
    if lam <= 0.0 or not math.isfinite(lam):
        # fallback to spectral radius helper (should not happen for positive matrices)
        lam = spectral_radius(M1)
    if lam <= 0.0 or not math.isfinite(lam):
        raise ValueError("invalid spectral radius")

    logC = logC_from_eigvals(eigs, lam_idx=lam_idx)

    z_star = 1.0 / lam
    s = 0.0
    for k in range(2, k_max + 1):
        mu = mobius(k)
        if mu == 0:
            continue
        log_zeta = log_zeta_from_matrix(M1, z_star**k)
        s += (float(mu) / float(k)) * log_zeta

    prog.tick(f"logM {tag} k_max={k_max}")
    return lam, (logC + s)


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


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
    parser = argparse.ArgumentParser(description="Phase diagram for log Mfrak(theta) (real-input-40)")
    parser.add_argument("--theta-e-min", type=float, default=-1.0)
    parser.add_argument("--theta-e-max", type=float, default=1.0)
    parser.add_argument("--theta-e-steps", type=int, default=41)
    parser.add_argument("--theta-2-min", type=float, default=-1.0)
    parser.add_argument("--theta-2-max", type=float, default=1.0)
    parser.add_argument("--theta-2-steps", type=int, default=41)
    parser.add_argument("--theta-neg", type=float, default=0.0)
    parser.add_argument("--k-max", type=int, default=200, help="Max k for Möbius tail series")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_logM_theta.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="real-input-40-logM-theta", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    grid = GridSpec(
        theta_e_min=args.theta_e_min,
        theta_e_max=args.theta_e_max,
        theta_e_steps=args.theta_e_steps,
        theta_2_min=args.theta_2_min,
        theta_2_max=args.theta_2_max,
        theta_2_steps=args.theta_2_steps,
        theta_neg=args.theta_neg,
    )

    xs = linspace(grid.theta_e_min, grid.theta_e_max, grid.theta_e_steps)
    ys = linspace(grid.theta_2_min, grid.theta_2_max, grid.theta_2_steps)

    lam_grid = np.zeros((len(ys), len(xs)), dtype=float)
    logM_grid = np.zeros((len(ys), len(xs)), dtype=float)

    for j, th2 in enumerate(ys):
        for i, the in enumerate(xs):
            tag = f"i={i+1}/{len(xs)} j={j+1}/{len(ys)}"
            lam, logm = logM_theta(
                theta_e=the,
                theta_neg=grid.theta_neg,
                theta_2=th2,
                k_max=args.k_max,
                states=states,
                kernel_map=kernel_map,
                prog=prog,
                tag=tag,
            )
            lam_grid[j, i] = lam
            logM_grid[j, i] = logm

    # Always print a representative value for quick sanity checks.
    print(
        f"[real-input-40-logM-theta] sample theta_e={xs[0]:.6g} theta_2={ys[0]:.6g} "
        f"lambda={lam_grid[0,0]:.12g} logM={logM_grid[0,0]:.12g}",
        flush=True,
    )

    # Plot heatmap (skip degenerate 1x1 to avoid warnings).
    out_png = export_dir() / "sync_kernel_real_input_40_logM_theta.png"
    if len(xs) > 1 and len(ys) > 1:
        plt.figure(figsize=(7.0, 5.4))
        im = plt.imshow(
            logM_grid,
            origin="lower",
            aspect="auto",
            extent=[xs[0], xs[-1], ys[0], ys[-1]],
            cmap="viridis",
        )
        plt.colorbar(im, label="log Mfrak(theta)")
        plt.xlabel("theta_e (output-bit weight)")
        plt.ylabel("theta_2 (collision weight)")
        plt.title("Real-input-40: log Mfrak(theta_e, theta_2), theta_neg fixed")
        plt.tight_layout()
        out_png.parent.mkdir(parents=True, exist_ok=True)
        plt.savefig(out_png, dpi=200)
        plt.close()

    payload: Dict[str, object] = {
        "theta_neg": grid.theta_neg,
        "theta_e_values": xs,
        "theta_2_values": ys,
        "lambda_grid": lam_grid.tolist(),
        "logM_grid": logM_grid.tolist(),
        "k_max": args.k_max,
        # Euler–Mascheroni constant (avoid version-dependent stdlib availability).
        "gamma": 0.5772156649015329,
    }

    if not args.no_output:
        out_json = Path(args.output) if args.output else export_dir() / "sync_kernel_real_input_40_logM_theta.json"
        write_json(out_json, payload)
        write_fig_tex(
            fig_name="fig_real_input_40_logM_theta",
            png_rel="artifacts/export/sync_kernel_real_input_40_logM_theta.png",
            caption="真实输入 40 状态核下，按输出位势 $\\theta_e$ 与碰撞势 $\\theta_2$ 加权得到的 Abel 常数函数 $\\log\\mathfrak{M}(\\theta_e,\\theta_2)$ 相图（固定 $\\theta_-=0$；脚本生成）。",
            label="fig:real_input_40_logM_theta",
        )
        print(f"[real-input-40-logM-theta] wrote {out_json}", flush=True)
        print(f"[real-input-40-logM-theta] wrote {out_png}", flush=True)
        print(
            f"[real-input-40-logM-theta] wrote {generated_dir() / 'fig_real_input_40_logM_theta.tex'}",
            flush=True,
        )

    print("[real-input-40-logM-theta] done", flush=True)


if __name__ == "__main__":
    main()

