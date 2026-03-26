#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate reproducible visualizations for sync kernels.

Outputs (default):
- artifacts/export/sync_kernel_10_state_graph.png
- sections/generated/fig_sync_kernel_10_state_graph.tex
- artifacts/export/sync_kernel_real_input_40_matrix.png
- sections/generated/fig_sync_kernel_real_input_40_matrix.tex

No external deps beyond numpy/matplotlib (per requirements.txt).
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import matplotlib.pyplot as plt

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int  # input digit in {0,1,2}
    e: int  # output digit in {0,1}


KERNEL_STATES: List[str] = [
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


def build_sync10_edges() -> List[KernelEdge]:
    # Matches the transition list in sections/07_emergent_arithmetic.tex (Theorem online-delay-fold)
    # and scripts/exp_sync_kernel_real_input_40.py (build_kernel_edges()).
    edges: List[KernelEdge] = []
    for d in (0, 1, 2):
        edges.append(KernelEdge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(KernelEdge("100", f"00{d}", d, 1))
    edges += [
        KernelEdge("001", "010", 0, 0),
        KernelEdge("001", "100", 1, 0),
        KernelEdge("001", "101", 2, 0),
        KernelEdge("002", "11-1", 0, 0),
        KernelEdge("002", "000", 1, 1),
        KernelEdge("002", "001", 2, 1),
        KernelEdge("010", "100", 0, 0),
        KernelEdge("010", "101", 1, 0),
        KernelEdge("010", "0-12", 2, 1),
        KernelEdge("101", "010", 0, 1),
        KernelEdge("101", "100", 1, 1),
        KernelEdge("101", "101", 2, 1),
        KernelEdge("0-12", "01-1", 0, 0),
        KernelEdge("0-12", "010", 1, 0),
        KernelEdge("0-12", "100", 2, 0),
        KernelEdge("1-12", "01-1", 0, 1),
        KernelEdge("1-12", "010", 1, 1),
        KernelEdge("1-12", "100", 2, 1),
        KernelEdge("01-1", "001", 0, 0),
        KernelEdge("01-1", "002", 1, 0),
        KernelEdge("01-1", "1-12", 2, 0),
        KernelEdge("11-1", "001", 0, 1),
        KernelEdge("11-1", "002", 1, 1),
        KernelEdge("11-1", "1-12", 2, 1),
    ]
    return edges


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


def _edge_color(d: int) -> str:
    # Material-ish tones (no emoji); keep high contrast in print.
    if d == 0:
        return "#546E7A"  # blue-grey
    if d == 1:
        return "#1E88E5"  # blue
    return "#E53935"  # red


def _edge_rad(src: str, dst: str, d: int) -> float:
    # Deterministic curvature to reduce overlap between parallel edges.
    if src == dst:
        return 0.35
    h = (hash((src, dst)) % 3) - 1  # -1,0,1
    base = 0.0 if h == 0 else (0.18 * float(h))
    tweak = {0: -0.06, 1: 0.0, 2: 0.06}[d]
    return base + tweak


def plot_sync10_graph(out_png: Path, prog: Progress) -> None:
    edges = build_sync10_edges()
    idx = {s: i for i, s in enumerate(KERNEL_STATES)}
    n = len(KERNEL_STATES)

    # Fixed circle layout (deterministic, dependency-free).
    angles = np.linspace(0.0, 2.0 * math.pi, n, endpoint=False)
    # Rotate so "000" starts at top.
    angles = angles + math.pi / 2.0
    pos: Dict[str, Tuple[float, float]] = {}
    r = 1.0
    for s, a in zip(KERNEL_STATES, angles):
        pos[s] = (r * float(math.cos(a)), r * float(math.sin(a)))

    fig = plt.figure(figsize=(8.0, 8.0))
    ax = plt.gca()
    ax.set_aspect("equal")
    ax.axis("off")

    # Nodes.
    for s in KERNEL_STATES:
        x, y = pos[s]
        ax.scatter([x], [y], s=900, color="#F5F5F5", edgecolors="#263238", linewidths=1.6, zorder=3)
        ax.text(x, y, s, ha="center", va="center", fontsize=10.5, color="#263238", zorder=4)

    # Edges (directed).
    for e in edges:
        x1, y1 = pos[e.src]
        x2, y2 = pos[e.dst]

        # Shrink arrow so it doesn't touch node centers.
        dx, dy = x2 - x1, y2 - y1
        dist = math.hypot(dx, dy)
        if dist < 1e-9:
            # self-loop: draw a small arc above the node
            rad = _edge_rad(e.src, e.dst, e.d)
            ax.annotate(
                "",
                xy=(x1 + 0.01, y1 + 0.01),
                xytext=(x1 - 0.01, y1 - 0.01),
                arrowprops=dict(
                    arrowstyle="-|>",
                    color=_edge_color(e.d),
                    linewidth=1.2,
                    shrinkA=30,
                    shrinkB=30,
                    connectionstyle=f"arc3,rad={rad}",
                ),
                zorder=2,
            )
            lx, ly = x1 + 0.10, y1 + 0.16
        else:
            shrink = 0.18
            sx, sy = x1 + shrink * dx, y1 + shrink * dy
            tx, ty = x2 - shrink * dx, y2 - shrink * dy
            rad = _edge_rad(e.src, e.dst, e.d)
            ax.annotate(
                "",
                xy=(tx, ty),
                xytext=(sx, sy),
                arrowprops=dict(
                    arrowstyle="-|>",
                    color=_edge_color(e.d),
                    linewidth=1.2,
                    shrinkA=0,
                    shrinkB=0,
                    connectionstyle=f"arc3,rad={rad}",
                ),
                zorder=1,
            )
            mx, my = (sx + tx) / 2.0, (sy + ty) / 2.0
            # Offset label along a normal direction based on rad.
            nx, ny = -dy, dx
            nrm = math.hypot(nx, ny)
            if nrm > 1e-9:
                nx, ny = nx / nrm, ny / nrm
            lx, ly = mx + 0.09 * rad * nx, my + 0.09 * rad * ny

        ax.text(
            lx,
            ly,
            f"{e.d}/{e.e}",
            fontsize=8.5,
            ha="center",
            va="center",
            color=_edge_color(e.d),
            bbox=dict(boxstyle="round,pad=0.16", fc="white", ec="none", alpha=0.85),
            zorder=5,
        )
        prog.tick(f"sync10 edge {e.src}->{e.dst} d={e.d}")

    # Minimal legend in-canvas.
    ax.text(-1.15, 1.15, "Edge label: d/e", fontsize=10, color="#263238", ha="left", va="center")
    ax.text(-1.15, 1.05, "d=0", fontsize=9.5, color=_edge_color(0), ha="left", va="center")
    ax.text(-0.95, 1.05, "d=1", fontsize=9.5, color=_edge_color(1), ha="left", va="center")
    ax.text(-0.75, 1.05, "d=2", fontsize=9.5, color=_edge_color(2), ha="left", va="center")

    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png, dpi=220)
    plt.close(fig)


def build_real_input_states() -> List[Tuple[str, int, int]]:
    out: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                out.append((s, px, py))
    return out


def build_kernel_map(edges: List[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(e.src, e.d): (e.dst, e.e) for e in edges}


def build_real_input_matrix_int(
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    idx = {st: i for i, st in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=int)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _ = kernel_map[(s, d)]
                nxt = (dst_state, x, y)
                M[idx[(s, px, py)], idx[nxt]] += 1
    return M


def plot_real_input_40_matrix(out_png: Path, prog: Progress) -> None:
    edges = build_sync10_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    M = build_real_input_matrix_int(states, kernel_map)

    fig = plt.figure(figsize=(8.2, 7.2))
    ax = plt.gca()
    im = ax.imshow(M, cmap="Blues", interpolation="nearest")

    ax.set_title("Real-input 40-state kernel adjacency matrix (block structure)")
    ax.set_xlabel("to-state index")
    ax.set_ylabel("from-state index")

    # Block separators for (px,py) in order 00,01,10,11 (each block size 10).
    for k in (10, 20, 30):
        ax.axhline(k - 0.5, color="#263238", linewidth=1.0, alpha=0.7)
        ax.axvline(k - 0.5, color="#263238", linewidth=1.0, alpha=0.7)
        prog.tick(f"draw block line at {k}")

    # Label block centers.
    centers = [5, 15, 25, 35]
    labels = ["00", "01", "10", "11"]
    ax.set_xticks(centers, labels)
    ax.set_yticks(centers, labels)
    ax.tick_params(axis="both", which="major", labelsize=10)

    cbar = fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    cbar.set_label("edge multiplicity (count of allowed (x,y) pairs)")

    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png, dpi=220)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate sync-kernel visualization figures")
    parser.add_argument("--no-40", action="store_true", help="Skip 40-state matrix heatmap")
    parser.add_argument("--no-10", action="store_true", help="Skip 10-state graph")
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-viz", every_seconds=20.0)
    print("[sync-kernel-viz] start", flush=True)

    if not args.no_10:
        png10 = export_dir() / "sync_kernel_10_state_graph.png"
        plot_sync10_graph(png10, prog=prog)
        write_fig_tex(
            fig_name="fig_sync_kernel_10_state_graph",
            png_rel="artifacts/export/sync_kernel_10_state_graph.png",
            caption=(
                "10 状态同步核的同步图 $\\Gamma$（节点为同步状态；每条边对应输入 $d\\in\\{0,1,2\\}$ 的确定性转移；"
                "边标签为 $d/e$；其中 $-1$ 记号对应正文中的 $\\overline{1}$）。"
            ),
            label="fig:sync_kernel_10_state_graph",
        )

    if not args.no_40:
        png40 = export_dir() / "sync_kernel_real_input_40_matrix.png"
        plot_real_input_40_matrix(png40, prog=prog)
        write_fig_tex(
            fig_name="fig_sync_kernel_real_input_40_matrix",
            png_rel="artifacts/export/sync_kernel_real_input_40_matrix.png",
            caption=(
                "真实输入 40 状态核的邻接矩阵热力图（状态按 $\\Sigma=Q\\times\\{0,1\\}^2$ 排列；"
                "按 $(p_x,p_y)=00,01,10,11$ 分成 $4\\times 4$ 个 $10\\times 10$ 块，展示输入约束与 10 状态同步核的 skew-product 块结构）。"
            ),
            label="fig:sync_kernel_real_input_40_matrix",
        )

    print("[sync-kernel-viz] done", flush=True)


if __name__ == "__main__":
    main()

