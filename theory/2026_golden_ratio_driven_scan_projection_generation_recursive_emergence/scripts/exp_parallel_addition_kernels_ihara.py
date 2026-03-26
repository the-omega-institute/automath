#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Ihara–Bass–Hashimoto fingerprints for the 9/13/21-local kernels (single-flow).

We build an undirected simple graph from the deterministic state transition graph:
  - vertices: reachable online states (single-flow)
  - undirected edge {i,j}: exists iff there is at least one transition i->j or j->i

On this undirected graph we compute:
  - n = |V|, m = |E|, cyclomatic number g = m - n + 1 (assuming connected)
  - degree statistics
  - spectral radius of adjacency A via power iteration
  - spectral radius of the non-backtracking (Hashimoto) operator B via power iteration

Outputs:
  - artifacts/export/parallel_addition_kernels_ihara.json
  - sections/generated/tab_parallel_addition_kernels_ihara_fingerprint.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _fmt(x: float, digits: int = 6) -> str:
    return f"{x:.{digits}g}"


def _power_iteration_nonneg(
    n: int,
    mul,
    *,
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> float:
    x = np.full(n, 1.0 / n, dtype=float)
    lam = 0.0
    for it in range(1, itmax + 1):
        y = mul(x)
        s = float(np.sum(y))
        if not (s > 0.0):
            return 0.0
        y = y / s
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} it={it} lam~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        x = y
        if it % 300 == 0:
            prog.tick(f"{label} it={it} lam~{lam_new:.12g}")
    return lam


def _power_iteration_nonneg_inplace(
    n: int,
    mul_inplace,
    *,
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> float:
    """Power iteration for nonnegative operators with reusable buffers.

    mul_inplace(x, y) must write y := M x (no allocation required).
    """
    x = np.full(n, 1.0 / n, dtype=float)
    y = np.empty_like(x)
    lam = 0.0
    for it in range(1, itmax + 1):
        mul_inplace(x, y)
        s = float(np.sum(y))
        if not (s > 0.0):
            return 0.0
        y *= 1.0 / s
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} it={it} lam~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        x, y = y, x
        if it % 300 == 0:
            prog.tick(f"{label} it={it} lam~{lam_new:.12g}")
    return lam


@dataclass(frozen=True)
class IharaFingerprint:
    name: str
    n: int
    m: int
    g: int
    deg_min: int
    deg_max: int
    deg_mean: float
    rho_A: float
    rho_B: float
    delta_reg: float
    eps_reg: float
    pi_bt: float


def build_undirected_neighbors(n: int, edges: List[List[int]]) -> List[List[int]]:
    nbr_sets: List[set[int]] = [set() for _ in range(n)]
    for src, dst, _kA, _kB in edges:
        if src == dst:
            continue
        nbr_sets[src].add(dst)
        nbr_sets[dst].add(src)
    return [sorted(s) for s in nbr_sets]


def count_undirected_edges(nbrs: List[List[int]]) -> int:
    s = sum(len(v) for v in nbrs)
    if s % 2 != 0:
        raise ValueError("odd total degree sum; invalid undirected graph")
    return s // 2


def spectral_radius_adjacency(nbrs: List[List[int]], prog: Progress, label: str) -> float:
    n = len(nbrs)
    if n == 0:
        return 0.0

    # Build oriented adjacency edges once: (src -> dst) for every neighbor link.
    src: List[int] = []
    dst: List[int] = []
    for i, ns in enumerate(nbrs):
        for j in ns:
            src.append(i)
            dst.append(j)
    src_a = np.asarray(src, dtype=np.int64)
    dst_a = np.asarray(dst, dtype=np.int64)

    def mul_inplace(x: np.ndarray, y: np.ndarray) -> None:
        y.fill(0.0)
        np.add.at(y, dst_a, x[src_a])

    return _power_iteration_nonneg_inplace(n, mul_inplace, itmax=8000, tol=1e-12, prog=prog, label=label)


def spectral_radius_hashimoto(nbrs: List[List[int]], prog: Progress, label: str) -> float:
    # Oriented edges: for each undirected {u,v} include (u->v) and (v->u).
    n = len(nbrs)
    oriented: List[Tuple[int, int]] = []
    for u, ns in enumerate(nbrs):
        for v in ns:
            oriented.append((u, v))
    m_or = len(oriented)
    if m_or == 0 or n == 0:
        return 0.0

    idx: Dict[Tuple[int, int], int] = {e: i for i, e in enumerate(oriented)}
    src = np.empty(m_or, dtype=np.int64)
    dst = np.empty(m_or, dtype=np.int64)
    rev = np.empty(m_or, dtype=np.int64)
    for i, (u, v) in enumerate(oriented):
        src[i] = int(u)
        dst[i] = int(v)
        rev[i] = int(idx[(v, u)])  # undirected graph => reverse always exists

    out_sum = np.empty(n, dtype=float)

    def mul_inplace(x: np.ndarray, y: np.ndarray) -> None:
        # out_sum[u] = sum_{u->w} x_{u->w}
        out_sum.fill(0.0)
        np.add.at(out_sum, src, x)
        # (Bx)_{u->v} = out_sum[v] - x_{v->u}
        y[:] = out_sum[dst] - x[rev]

    return _power_iteration_nonneg_inplace(
        m_or, mul_inplace, itmax=12000, tol=1e-12, prog=prog, label=label
    )


def make_table(rows: List[IharaFingerprint]) -> str:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_parallel_addition_kernels_ihara.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\begin{tabular}{@{}lrrrrrrrrrrr@{}}")
    lines.append("\\toprule")
    lines.append(
        "核 & $|V|$ & $|E|$ & $g$ & $\\min\\deg$ & $\\max\\deg$ & $\\overline{\\deg}$ & $\\rho(A)$ & $\\rho(B)$ & $\\Delta_{\\mathrm{reg}}$ & $\\varepsilon_{\\mathrm{reg}}$ & $\\pi_{\\mathrm{bt}}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.name} & {r.n} & {r.m} & {r.g} & {r.deg_min} & {r.deg_max} & {_fmt(r.deg_mean,6)} & {_fmt(r.rho_A,8)} & {_fmt(r.rho_B,8)} & {_fmt(r.delta_reg,8)} & {_fmt(r.eps_reg,8)} & {_fmt(r.pi_bt,6)}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{Ihara--Bass--Hashimoto 无回溯素回路指纹（单流：由在线机状态图生成无向骨架，并在其上计算邻接谱半径 $\\rho(A)$ 与无回溯算子（Hashimoto）谱半径 $\\rho(B)$。"
        "并定义近正则缺陷 $\\Delta_{\\mathrm{reg}}:=\\rho(A)-\\rho(B)-1$、归一化近正则缺陷 $\\varepsilon_{\\mathrm{reg}}:=\\Delta_{\\mathrm{reg}}/(\\rho(A)-1)$ 与回溯惩罚 $\\pi_{\\mathrm{bt}}:=1-\\rho(B)/\\rho(A)$，用于量化 ordinary walk 与 non-backtracking walk 的增长率脱钩程度）。}"
    )
    lines.append("\\label{tab:parallel-addition-kernels-ihara-fingerprint}")
    lines.append("\\end{table}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=str, default="", help="Input BFS JSON (default: artifacts/export/parallel_addition_kernels_bfs.json)")
    parser.add_argument("--no-output", action="store_true", help="Do not write outputs")
    args = parser.parse_args()

    prog = Progress(label="par-add-ihara", every_seconds=20.0)
    in_path = Path(args.input) if args.input else (export_dir() / "parallel_addition_kernels_bfs.json")
    payload = _read_json(in_path)

    out_rows: List[IharaFingerprint] = []
    out_json_rows: List[dict] = []

    for k in payload.get("kernels", []):
        name = str(k.get("name", ""))
        n = int(k.get("states_reachable", 0))
        edges = k.get("edges", None)
        if edges is None:
            raise SystemExit(f"[par-add-ihara] missing edges in BFS json for kernel: {name}")
        prog.tick(f"{name} build undirected graph")
        nbrs = build_undirected_neighbors(n, edges)
        m = int(count_undirected_edges(nbrs))
        g = int(m - n + 1) if n > 0 else 0
        degs = [len(ns) for ns in nbrs]
        deg_min = int(min(degs)) if degs else 0
        deg_max = int(max(degs)) if degs else 0
        deg_mean = (2.0 * m / n) if n > 0 else 0.0

        rho_A = spectral_radius_adjacency(nbrs, prog=prog, label=f"{name} rho(A)")
        rho_B = spectral_radius_hashimoto(nbrs, prog=prog, label=f"{name} rho(B)")
        delta_reg = float(rho_A - rho_B - 1.0)
        eps_reg = float(delta_reg / (rho_A - 1.0)) if rho_A > 1.0 else 0.0
        pi_bt = float(1.0 - (rho_B / rho_A)) if rho_A > 0 else 0.0

        out_rows.append(
            IharaFingerprint(
                name=name,
                n=n,
                m=m,
                g=g,
                deg_min=deg_min,
                deg_max=deg_max,
                deg_mean=deg_mean,
                rho_A=rho_A,
                rho_B=rho_B,
                delta_reg=delta_reg,
                eps_reg=eps_reg,
                pi_bt=pi_bt,
            )
        )
        out_json_rows.append(
            {
                "name": name,
                "n": n,
                "m": m,
                "g": g,
                "deg_min": deg_min,
                "deg_max": deg_max,
                "deg_mean": deg_mean,
                "rho_A": rho_A,
                "rho_B": rho_B,
                "delta_reg": delta_reg,
                "eps_reg": eps_reg,
                "pi_bt": pi_bt,
            }
        )
        prog.tick(f"{name} done rho(A)~{rho_A:.6g} rho(B)~{rho_B:.6g}")

    if not args.no_output:
        out_json = export_dir() / "parallel_addition_kernels_ihara.json"
        _write_text(out_json, json.dumps({"rows": out_json_rows}, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-ihara] wrote {out_json}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_ihara_fingerprint.tex"
        _write_text(out_tex, make_table(out_rows))
        print(f"[par-add-ihara] wrote {out_tex}", flush=True)

    print("[par-add-ihara] done", flush=True)


if __name__ == "__main__":
    main()

