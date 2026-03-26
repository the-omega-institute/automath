#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Ihara geometry phase diagram for 9/13/21-local kernels (single-flow).

We work on the undirected skeleton graph built from the deterministic online state
transition graph (single-flow):
  - vertices: reachable states
  - undirected edge {i,j}: exists iff i->j or j->i exists in the deterministic graph

On this skeleton we compute:
  - rho(A): adjacency spectral radius (ordinary closed-walk growth)
  - rho(B): Hashimoto (non-backtracking) spectral radius
  - Delta_reg := rho(A) - rho(B) - 1
  - eps_reg   := Delta_reg / (rho(A)-1)
  - Delta_h   := log(rho(A)/rho(B))

And we compute the Hashimoto kernel-RH / Ramanujan-quality indicator (u=1, unweighted):
  - Lambda := max_{mu in spec(B)\\{rho(B)}} |mu|  (sub-spectral radius)
  - R      := Lambda / sqrt(rho(B))
  - beta   := log(Lambda) / log(rho(B))
  - delta  := log(Lambda^2 / rho(B))  (RH iff <= 0 in the idealized model)

Outputs:
  - artifacts/export/parallel_addition_kernels_ihara_phase.json
  - sections/generated/tab_parallel_addition_kernels_ihara_rh_scan.tex
  - artifacts/export/parallel_addition_kernels_ihara_phase.png
  - sections/generated/fig_parallel_addition_kernels_ihara_phase.tex
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
from common_phi_fold import Progress


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _fmt(x: float, digits: int = 12) -> str:
    return f"{x:.{digits}g}"


def _name_tex(name: str) -> str:
    if "9-local" in name:
        return r"$K_{9}$"
    if "13-local" in name:
        return r"$K_{13}$"
    return r"$K_{21}$"


def build_undirected_neighbors(n: int, edges: List[List[int]]) -> List[List[int]]:
    nbr_sets: List[set[int]] = [set() for _ in range(n)]
    for src, dst, _kA, _kB in edges:
        if src == dst:
            continue
        nbr_sets[int(src)].add(int(dst))
        nbr_sets[int(dst)].add(int(src))
    return [sorted(s) for s in nbr_sets]


def count_undirected_edges(nbrs: List[List[int]]) -> int:
    s = sum(len(v) for v in nbrs)
    if s % 2 != 0:
        raise ValueError("odd total degree sum; invalid undirected graph")
    return s // 2


def _power_iteration_pf(
    n: int,
    mul_inplace,
    *,
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> Tuple[float, np.ndarray]:
    """PF power iteration for nonnegative operators, returning (lambda, right-eigenvector)."""
    x = np.full(n, 1.0 / n, dtype=float)
    y = np.zeros(n, dtype=float)
    lam = 0.0
    for it in range(1, itmax + 1):
        mul_inplace(x, y)
        s = float(np.sum(y))
        if not (s > 0.0):
            return 0.0, x
        x[:] = y / s
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} pf it={it} lam~{lam_new:.12g}")
            return lam_new, x
        lam = lam_new
        if it % 600 == 0:
            prog.tick(f"{label} pf it={it} lam~{lam_new:.12g}")
    return lam, x


@dataclass(frozen=True)
class HashimotoOps:
    n_nodes: int
    src: np.ndarray  # oriented edge sources, shape (m_or,)
    dst: np.ndarray  # oriented edge destinations, shape (m_or,)
    rev: np.ndarray  # reverse-edge index, shape (m_or,)

    def mul_B_inplace(self, x: np.ndarray, out: np.ndarray, work_nodes: np.ndarray) -> None:
        """out[:] = B x (Hashimoto / non-backtracking operator), no allocations."""
        work_nodes.fill(0)
        # work_nodes[u] = sum_{e: src(e)=u} x[e]
        np.add.at(work_nodes, self.src, x)
        out[:] = work_nodes[self.dst] - x[self.rev]

    def mul_Bt_inplace(self, x: np.ndarray, out: np.ndarray, work_nodes: np.ndarray) -> None:
        """out[:] = B^T x, no allocations."""
        work_nodes.fill(0)
        # work_nodes[v] = sum_{e: dst(e)=v} x[e]
        np.add.at(work_nodes, self.dst, x)
        out[:] = work_nodes[self.src] - x[self.rev]


def build_hashimoto_ops(nbrs: List[List[int]]) -> HashimotoOps:
    src_list: List[int] = []
    dst_list: List[int] = []
    for u, ns in enumerate(nbrs):
        for v in ns:
            src_list.append(int(u))
            dst_list.append(int(v))
    src = np.asarray(src_list, dtype=np.int64)
    dst = np.asarray(dst_list, dtype=np.int64)
    m_or = int(src.shape[0])

    idx: Dict[Tuple[int, int], int] = {(int(u), int(v)): i for i, (u, v) in enumerate(zip(src_list, dst_list, strict=True))}
    rev = np.zeros(m_or, dtype=np.int64)
    for i in range(m_or):
        rev[i] = idx[(int(dst[i]), int(src[i]))]
    return HashimotoOps(
        n_nodes=len(nbrs),
        src=src,
        dst=dst,
        rev=rev,
    )


def spectral_radius_adjacency(nbrs: List[List[int]], prog: Progress, label: str) -> float:
    n = len(nbrs)
    src_list: List[int] = []
    dst_list: List[int] = []
    for i, ns in enumerate(nbrs):
        for j in ns:
            src_list.append(int(i))
            dst_list.append(int(j))
    src = np.asarray(src_list, dtype=np.int64)
    dst = np.asarray(dst_list, dtype=np.int64)

    def mul_inplace(x: np.ndarray, out: np.ndarray) -> None:
        out.fill(0.0)
        np.add.at(out, dst, x[src])

    lam, _vec = _power_iteration_pf(n, mul_inplace, itmax=8000, tol=1e-12, prog=prog, label=label)
    return lam


def spectral_radius_hashimoto(ops: HashimotoOps, prog: Progress, label: str) -> Tuple[float, np.ndarray, np.ndarray]:
    """Return (rho(B), right PF vector r, left PF vector l) with l^T r = 1."""
    n = int(ops.src.shape[0])
    work_nodes = np.zeros(ops.n_nodes, dtype=float)

    def mul_B_real_inplace(x: np.ndarray, out: np.ndarray) -> None:
        ops.mul_B_inplace(x, out, work_nodes)

    def mul_Bt_real_inplace(x: np.ndarray, out: np.ndarray) -> None:
        ops.mul_Bt_inplace(x, out, work_nodes)

    lam1, r = _power_iteration_pf(n, mul_B_real_inplace, itmax=16000, tol=1e-13, prog=prog, label=f"{label} rho(B)")
    lam1_t, l = _power_iteration_pf(n, mul_Bt_real_inplace, itmax=16000, tol=1e-13, prog=prog, label=f"{label} rho(B)^T")
    # lam1_t should match lam1; keep lam1.
    _ = lam1_t

    # Normalize left eigenvector so that l^T r = 1.
    alpha = float(np.dot(l, r))
    if not (alpha > 0.0):
        raise ValueError("failed to normalize PF eigenvectors for Hashimoto operator")
    l = l / alpha
    return lam1, r, l


def sub_spectral_radius_hashimoto(
    ops: HashimotoOps,
    *,
    lam1: float,
    r_pf: np.ndarray,
    l_pf: np.ndarray,
    seed: int,
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> float:
    """Approximate Lambda = max_{mu != lam1} |mu| for Hashimoto B via projected complex power iteration."""
    n = int(ops.src.shape[0])
    rng = np.random.default_rng(int(seed))

    def proj_inplace(x: np.ndarray) -> None:
        # P = I - r l^T with l^T r = 1. Works for complex x.
        x -= r_pf * np.dot(l_pf, x)

    # Complex random start, projected to the non-PF subspace.
    x = rng.normal(size=n) + 1j * rng.normal(size=n)
    proj_inplace(x)
    nx = float(np.linalg.norm(x))
    if nx == 0.0:
        # Extremely unlikely; retry with a different seed.
        x = (rng.normal(size=n) + 1j * rng.normal(size=n)) * (1.0 + 1j)
        proj_inplace(x)
        nx = float(np.linalg.norm(x))
    x = x / nx

    work_nodes = np.zeros(ops.n_nodes, dtype=complex)
    y = np.zeros(n, dtype=complex)
    lam = 0.0
    for it in range(1, itmax + 1):
        ops.mul_B_inplace(x, y, work_nodes)
        proj_inplace(y)
        ny = float(np.linalg.norm(y))
        if ny == 0.0:
            return 0.0
        x[:] = y / ny
        lam_new = ny
        if it > 80 and abs(lam_new - lam) / max(1.0, lam_new) < tol:
            prog.tick(f"{label} Lambda it={it} ~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        if it % 800 == 0:
            prog.tick(f"{label} Lambda it={it} ~{lam_new:.12g}")
    return lam


@dataclass(frozen=True)
class Row:
    name: str
    name_tex: str
    nV: int
    nE: int
    rho_A: float
    rho_B: float
    delta_reg: float
    eps_reg: float
    delta_h: float
    Lambda: float
    R: float
    beta: float
    delta: float


def make_table(rows: List[Row]) -> str:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_parallel_addition_kernels_ihara_phase.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\begin{tabular}{@{}lrrrrr@{}}")
    lines.append("\\toprule")
    lines.append("Kernel & $\\rho(B)$ & $\\Lambda$ & $\\Lambda/\\sqrt{\\rho(B)}$ & $\\beta$ & $\\delta$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.name_tex} & {_fmt(r.rho_B, 12)} & {_fmt(r.Lambda, 12)} & {_fmt(r.R, 12)} & {_fmt(r.beta, 12)} & {_fmt(r.delta, 12)}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{Kernel-RH scan on the Hashimoto operator of the undirected skeleton (single-flow). "
        "We report $\\rho(B)$, the sub-spectral radius $\\Lambda=\\max_{\\mu\\in\\mathrm{spec}(B)\\setminus\\{\\rho(B)\\}}|\\mu|$, "
        "the Ramanujan ratio $\\Lambda/\\sqrt{\\rho(B)}$, the induced pole exponent $\\beta=\\log\\Lambda/\\log\\rho(B)$, "
        "and the Newman-style offset $\\delta=\\log(\\Lambda^2/\\rho(B))$.}"
    )
    lines.append("\\label{tab:parallel_addition_kernels_ihara_rh_scan}")
    lines.append("\\end{table}")
    lines.append("")
    return "\n".join(lines)


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


def plot_phase(rows: List[Row], out_png: Path) -> None:
    # Material-ish tones (match exp_parallel_addition_kernels_fingerprint_figs.py).
    colors = {"K9": "#1E88E5", "K13": "#E53935", "K21": "#43A047"}

    def key(name: str) -> str:
        if "9-local" in name:
            return "K9"
        if "13-local" in name:
            return "K13"
        return "K21"

    fig = plt.figure(figsize=(9.2, 5.2))
    ax = plt.gca()

    for r in rows:
        k = key(r.name)
        ax.scatter([r.eps_reg], [r.R], s=90, color=colors[k], edgecolor="black", linewidth=0.6, zorder=3)
        ax.annotate(
            r.name_tex,
            (r.eps_reg, r.R),
            textcoords="offset points",
            xytext=(8, 6),
            fontsize=11,
            ha="left",
            va="bottom",
        )

    ax.set_xscale("log")
    ax.axhline(1.0, color="#555555", linestyle="--", linewidth=1.2, alpha=0.9, zorder=2)
    ax.set_xlabel(r"$\varepsilon_{\mathrm{reg}}=\Delta_{\mathrm{reg}}/(\rho(A)-1)$ (log scale)")
    ax.set_ylabel(r"$R_K(1)=\Lambda/\sqrt{\rho(B)}$")
    ax.grid(True, which="both", linestyle="--", linewidth=0.6, alpha=0.5)
    plt.tight_layout()

    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_png, dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description="Ihara phase diagram for 9/13/21-local kernels (single-flow).")
    parser.add_argument(
        "--input",
        type=str,
        default="",
        help="Input BFS JSON (default: artifacts/export/parallel_addition_kernels_bfs.json)",
    )
    parser.add_argument("--seed", type=int, default=12345, help="RNG seed for sub-spectral radius estimation.")
    parser.add_argument("--itmax", type=int, default=12000, help="Max iterations for Lambda power iteration.")
    parser.add_argument("--tol", type=float, default=1e-12, help="Relative tolerance for Lambda iteration.")
    parser.add_argument("--no-output", action="store_true", help="Do not write outputs")
    args = parser.parse_args()

    prog = Progress(label="par-add-ihara-phase", every_seconds=20.0)
    in_path = Path(args.input) if args.input else (export_dir() / "parallel_addition_kernels_bfs.json")
    payload = _read_json(in_path)

    out_rows: List[Row] = []
    for k in payload.get("kernels", []):
        name = str(k.get("name", "")).strip() or "unknown"
        nV = int(k.get("states_reachable", 0))
        edges = k.get("edges", None)
        if edges is None:
            raise SystemExit(f"[par-add-ihara-phase] missing edges for kernel: {name}")
        prog.tick(f"{name} build skeleton + Hashimoto ops")
        nbrs = build_undirected_neighbors(nV, edges)
        nE = int(count_undirected_edges(nbrs))

        rho_A = spectral_radius_adjacency(nbrs, prog=prog, label=f"{name} rho(A)")
        ops = build_hashimoto_ops(nbrs)
        rho_B, r_pf, l_pf = spectral_radius_hashimoto(ops, prog=prog, label=name)

        delta_reg = float(rho_A - rho_B - 1.0)
        eps_reg = float(delta_reg / (rho_A - 1.0)) if rho_A > 1.0 else 0.0
        delta_h = float(math.log(rho_A) - math.log(rho_B)) if (rho_A > 0 and rho_B > 0) else 0.0

        prog.tick(f"{name} estimate Lambda (sub-spectral radius)")
        Lambda = float(
            sub_spectral_radius_hashimoto(
                ops,
                lam1=float(rho_B),
                r_pf=r_pf,
                l_pf=l_pf,
                seed=int(args.seed),
                itmax=int(args.itmax),
                tol=float(args.tol),
                prog=prog,
                label=name,
            )
        )

        if rho_B > 0:
            R = float(Lambda / math.sqrt(rho_B))
            beta = float(math.log(Lambda) / math.log(rho_B)) if (Lambda > 0 and rho_B > 1.0) else 0.0
            delta = float(math.log((Lambda * Lambda) / rho_B)) if (Lambda > 0 and rho_B > 0) else 0.0
        else:
            R, beta, delta = 0.0, 0.0, 0.0

        # Basic sanity check: projected Lambda should be strictly below rho(B) for aperiodic graphs.
        if rho_B > 0 and Lambda >= rho_B * (1.0 - 1e-8):
            prog.tick(f"[warn] {name} Lambda ~= rho(B); projection may be under-resolved")

        out_rows.append(
            Row(
                name=name,
                name_tex=_name_tex(name),
                nV=nV,
                nE=nE,
                rho_A=float(rho_A),
                rho_B=float(rho_B),
                delta_reg=delta_reg,
                eps_reg=eps_reg,
                delta_h=delta_h,
                Lambda=Lambda,
                R=R,
                beta=beta,
                delta=delta,
            )
        )
        prog.tick(f"{name} done rho(B)~{rho_B:.6g} Lambda~{Lambda:.6g} R~{R:.6g}")

    # Stable ordering: K9, K13, K21.
    def _ord_key(r: Row) -> int:
        if "9-local" in r.name:
            return 9
        if "13-local" in r.name:
            return 13
        return 21

    out_rows.sort(key=_ord_key)

    if args.no_output:
        return

    # JSON export (auditable reproduction).
    out_json = export_dir() / "parallel_addition_kernels_ihara_phase.json"
    _write_text(out_json, json.dumps({"rows": [asdict(r) for r in out_rows]}, indent=2, sort_keys=True) + "\n")
    print(f"[par-add-ihara-phase] wrote {out_json}", flush=True)

    # TeX table (committed).
    out_tex = generated_dir() / "tab_parallel_addition_kernels_ihara_rh_scan.tex"
    _write_text(out_tex, make_table(out_rows))
    print(f"[par-add-ihara-phase] wrote {out_tex}", flush=True)

    # Phase diagram plot + TeX include.
    out_png = export_dir() / "parallel_addition_kernels_ihara_phase.png"
    plot_phase(out_rows, out_png)
    _write_fig_tex(
        "fig_parallel_addition_kernels_ihara_phase",
        "artifacts/export/parallel_addition_kernels_ihara_phase.png",
        r"Ihara 二轴相图（单流）：横轴为归一化近正则缺陷 $\varepsilon_{\mathrm{reg}}$（对数刻度），纵轴为 Hashimoto 谱隙质量指标 $R_K(1)=\Lambda/\sqrt{\rho(B)}$。虚线 $R=1$ 对应平方根级误差阈值（Ramanujan/RH 型界）。",
        "fig:parallel-addition-kernels-ihara-phase",
    )
    print(f"[par-add-ihara-phase] wrote {out_png}", flush=True)

    print("[par-add-ihara-phase] done", flush=True)


if __name__ == "__main__":
    main()

