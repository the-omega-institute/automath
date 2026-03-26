#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate reproducible plots for parallel-addition kernel fingerprints (A-route).

Inputs:
- artifacts/export/parallel_addition_kernels_bfs.json  (from exp_parallel_addition_kernels_bfs.py)

Outputs (default):
- artifacts/export/parallel_addition_kernels_Bn0.png
- sections/generated/fig_parallel_addition_kernels_Bn0.tex
- artifacts/export/parallel_addition_kernels_lambda_u.png
- sections/generated/fig_parallel_addition_kernels_lambda_u.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class KernelSeries:
    name: str
    name_tex: str
    u_grid: List[float]
    lam: List[float]
    p_n0: List[int]  # carry-free primitive spectrum p_n(A0)


def _write_fig_tex(fig_name: str, png_rel: str, caption: str, label: str) -> None:
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


def _name_tex(name: str) -> str:
    if "9-local" in name:
        return r"$K_{9}$"
    if "13-local" in name:
        return r"$K_{13}$"
    return r"$K_{21}$"


def _load_series(path: Path) -> List[KernelSeries]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    u_grid = [float(x) for x in payload["u_grid"]]

    out: List[KernelSeries] = []
    for k in payload["kernels"]:
        lams = k["lambda_u"]
        lam = []
        for u in u_grid:
            # JSON keys are strings; accept both "0" and "0.0" style.
            key1 = str(u)
            key2 = f"{u:.6g}"
            if key1 in lams:
                lam.append(float(lams[key1]))
            elif key2 in lams:
                lam.append(float(lams[key2]))
            else:
                # Fallback: scan keys by numeric parse (robust against formatting).
                found = None
                for kk, vv in lams.items():
                    try:
                        if abs(float(kk) - u) < 1e-12:
                            found = float(vv)
                            break
                    except Exception:
                        continue
                if found is None:
                    raise RuntimeError(f"missing lambda(u) for u={u} in kernel {k['name']}")
                lam.append(found)

        p_n0 = [int(x) for x in k["carry_free"]["primitive_p_n"]]
        out.append(
            KernelSeries(
                name=str(k["name"]),
                name_tex=_name_tex(str(k["name"])),
                u_grid=u_grid,
                lam=lam,
                p_n0=p_n0,
            )
        )
    return out


def _material_palette() -> Dict[str, str]:
    # Material-ish tones (high contrast).
    return {
        "K9": "#1E88E5",   # blue
        "K13": "#E53935",  # red
        "K21": "#43A047",  # green
    }


def _kernel_key(name: str) -> str:
    if "9-local" in name:
        return "K9"
    if "13-local" in name:
        return "K13"
    return "K21"


def plot_bn0(series: List[KernelSeries], out_png: Path, *, n_max: int) -> None:
    colors = _material_palette()

    fig = plt.figure(figsize=(9.2, 5.2))
    ax = plt.gca()

    for s in series:
        key = _kernel_key(s.name)
        ns = list(range(1, min(n_max, len(s.p_n0)) + 1))
        ys = [max(1, s.p_n0[n - 1]) for n in ns]
        ax.plot(ns, ys, marker="o", linewidth=2.0, markersize=4.0, color=colors[key], label=s.name_tex)

    ax.set_yscale("log")
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"$B_{K,n}(0)=p_n(A_0)$ (log scale)")
    ax.grid(True, which="both", linestyle="--", linewidth=0.6, alpha=0.5)
    ax.legend(loc="best", frameon=True)
    plt.tight_layout()

    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_png, dpi=180)
    plt.close(fig)


def plot_lambda_u(series: List[KernelSeries], out_png: Path) -> None:
    colors = _material_palette()

    fig = plt.figure(figsize=(9.2, 5.2))
    ax = plt.gca()

    for s in series:
        key = _kernel_key(s.name)
        ax.plot(s.u_grid, s.lam, linewidth=2.2, color=colors[key], label=s.name_tex)

    ax.set_xlim(0.0, 1.0)
    ax.set_xlabel(r"$u\in[0,1]$")
    ax.set_ylabel(r"$\lambda_K(u)=\rho(M_K(u))$")
    ax.grid(True, linestyle="--", linewidth=0.6, alpha=0.5)
    ax.legend(loc="best", frameon=True)
    plt.tight_layout()

    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_png, dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description="Plots for parallel-addition kernel fingerprints (B_n(0) and lambda(u))")
    parser.add_argument(
        "--input",
        type=str,
        default="",
        help="Input JSON path (default: artifacts/export/parallel_addition_kernels_bfs.json)",
    )
    parser.add_argument("--nmax", type=int, default=20, help="Max n for B_{K,n}(0) plot")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    in_path = Path(args.input) if args.input else (export_dir() / "parallel_addition_kernels_bfs.json")
    series = _load_series(in_path)

    if args.no_output:
        return

    # Figure 1: primitive skeleton spectrum B_{K,n}(0)
    out_bn0 = export_dir() / "parallel_addition_kernels_Bn0.png"
    plot_bn0(series, out_bn0, n_max=int(args.nmax))
    _write_fig_tex(
        "fig_parallel_addition_kernels_Bn0",
        "artifacts/export/parallel_addition_kernels_Bn0.png",
        r"carry-free 骨架的 primitive 谱：$n\mapsto B_{K,n}(0)$（其中 $B_{K,n}(0)=p_n(A_0)$，见命题/定义链）。",
        "fig:parallel-addition-kernels-bn0",
    )

    # Figure 2: pressure curve u -> lambda(u)
    out_lam = export_dir() / "parallel_addition_kernels_lambda_u.png"
    plot_lambda_u(series, out_lam)
    _write_fig_tex(
        "fig_parallel_addition_kernels_lambda_u",
        "artifacts/export/parallel_addition_kernels_lambda_u.png",
        r"带权压力曲线：$u\mapsto \lambda_K(u)=\rho(M_K(u))$（单流；全局块级由张量积提升）。",
        "fig:parallel-addition-kernels-lambda-u",
    )


if __name__ == "__main__":
    main()

