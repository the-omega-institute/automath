#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Rotation polytope sampling for the real-input 40-state kernel.

We treat the real-input kernel graph as an edge shift (SFT). For each directed edge e
we define a vector-valued observable Phi(e) in Z^d (locally constant potential).

By Ziemian (1995), for a transitive SFT and Phi depending only on length-2 cylinders
(i.e. edge labels), the rotation set Rot(Phi) is a convex polytope and periodic
rotation vectors are dense. Exposed faces can be probed by scalarization:

  phi_theta(e) = <theta, Phi(e)>

and minimizing the cycle mean of phi_theta (a min-mean-cycle problem).

This script produces a *reproducible* table by sampling a small family of directions
theta and computing, for each theta, a witness periodic cycle and its average vector.

Outputs:
  - sections/generated/tab_real_input_40_rotation_polytope_sample.tex
  - artifacts/export/real_input_40_rotation_polytope_sample.json
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Edge:
    src: int
    dst: int
    # Observable vector Phi = (chi, nu, xi)
    chi: int
    nu: int
    xi: int


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _build_kernel_edges_raw() -> List[Tuple[str, str, int, int]]:
    """Return raw labeled edges as (src_state, dst_state, d, e)."""
    # Keep consistent with exp_sync_kernel_real_input_40_arity_3d.py.
    from exp_sync_kernel_real_input_40_arity_3d import build_kernel_edges

    out: List[Tuple[str, str, int, int]] = []
    for edge in build_kernel_edges():
        out.append((edge.src, edge.dst, int(edge.d), int(edge.e)))
    return out


def _build_real_input_states() -> List[Tuple[str, int, int]]:
    from exp_sync_kernel_real_input_40_arity_3d import build_real_input_states

    return list(build_real_input_states())


def _build_graph_edges() -> Tuple[List[Tuple[str, int, int]], List[Edge]]:
    """Build the 40-state directed graph and return (states, edges)."""
    raw_kernel_edges = _build_kernel_edges_raw()
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]] = {(s, d): (t, e) for s, t, d, e in raw_kernel_edges}

    states = _build_real_input_states()  # (s, px, py)
    idx: Dict[Tuple[str, int, int], int] = {st: i for i, st in enumerate(states)}

    edges: List[Edge] = []
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                # Observables (one-step):
                xi = 1 if d == 2 else 0
                chi = int(e) - xi
                nu = 1 if "-" in dst_state else 0
                u = idx[(s, px, py)]
                v = idx[(dst_state, x, y)]
                edges.append(Edge(src=u, dst=v, chi=chi, nu=nu, xi=xi))
    return states, edges


def _scc_kosaraju(n: int, edges: List[Edge]) -> List[List[int]]:
    g: List[List[int]] = [[] for _ in range(n)]
    gr: List[List[int]] = [[] for _ in range(n)]
    for e in edges:
        g[e.src].append(e.dst)
        gr[e.dst].append(e.src)

    seen = [False] * n
    order: List[int] = []

    def dfs(v: int) -> None:
        seen[v] = True
        for u in g[v]:
            if not seen[u]:
                dfs(u)
        order.append(v)

    for v in range(n):
        if not seen[v]:
            dfs(v)

    comp = [-1] * n
    comps: List[List[int]] = []

    def dfs2(v: int, cid: int) -> None:
        comp[v] = cid
        comps[cid].append(v)
        for u in gr[v]:
            if comp[u] == -1:
                dfs2(u, cid)

    for v in reversed(order):
        if comp[v] == -1:
            comps.append([])
            dfs2(v, len(comps) - 1)
    return comps


def _extract_essential_scc(n: int, edges: List[Edge]) -> Tuple[List[int], List[Edge]]:
    """Pick the (unique) essential SCC (largest SCC with a cycle) and restrict."""
    comps = _scc_kosaraju(n, edges)
    comps_sorted = sorted(comps, key=len, reverse=True)
    # Heuristic: the essential SCC is the unique largest SCC (paper proves it is size 20).
    ess_nodes = comps_sorted[0]
    ess_set = set(ess_nodes)
    new_id = {v: i for i, v in enumerate(sorted(ess_nodes))}
    edges2: List[Edge] = []
    for e in edges:
        if e.src in ess_set and e.dst in ess_set:
            edges2.append(
                Edge(
                    src=new_id[e.src],
                    dst=new_id[e.dst],
                    chi=e.chi,
                    nu=e.nu,
                    xi=e.xi,
                )
            )
    return sorted(ess_nodes), edges2


def _min_cycle_mean_karp(n: int, edges: List[Tuple[int, int, float]]) -> Tuple[float, List[int]]:
    """Karp O(nm) minimum cycle mean value, plus a witness cycle (best effort).

    Returns:
      mu: minimum mean weight
      cycle: list of vertices in order (v0,v1,...,v_{L-1}) with edges vi->v_{i+1 mod L}
    """
    # DP for shortest paths with exactly k edges.
    inf = 1e100
    d: List[List[float]] = [[inf] * n for _ in range(n + 1)]
    pred: List[List[int]] = [[-1] * n for _ in range(n + 1)]
    d[0] = [0.0] * n
    # Build incoming adjacency for relaxation.
    inc: List[List[Tuple[int, float]]] = [[] for _ in range(n)]
    for u, v, w in edges:
        inc[v].append((u, w))
    for k in range(1, n + 1):
        dk = d[k]
        dkm1 = d[k - 1]
        pk = pred[k]
        for v in range(n):
            best = inf
            bestu = -1
            for u, w in inc[v]:
                cand = dkm1[u] + w
                if cand < best:
                    best = cand
                    bestu = u
            dk[v] = best
            pk[v] = bestu

    # Karp formula.
    mu = inf
    arg_v = 0
    for v in range(n):
        if d[n][v] >= inf / 10:
            continue
        mx = -inf
        for k in range(n):
            if d[k][v] >= inf / 10:
                continue
            mx = max(mx, (d[n][v] - d[k][v]) / float(n - k))
        if mx < mu:
            mu = mx
            arg_v = v

    # Witness cycle extraction: backtrack a long path ending at arg_v, find best cycle in it.
    L = 2 * n
    # Extend DP one more time to length L for the selected endpoint.
    # Reuse relaxation to compute pred up to L for all nodes; n is small (<=20 here).
    d2: List[List[float]] = [[inf] * n for _ in range(L + 1)]
    pred2: List[List[int]] = [[-1] * n for _ in range(L + 1)]
    d2[0] = [0.0] * n
    for k in range(1, L + 1):
        dk = d2[k]
        dkm1 = d2[k - 1]
        pk = pred2[k]
        for v in range(n):
            best = inf
            bestu = -1
            for u, w in inc[v]:
                cand = dkm1[u] + w
                if cand < best:
                    best = cand
                    bestu = u
            dk[v] = best
            pk[v] = bestu

    # Reconstruct path nodes backward.
    path: List[int] = [arg_v]
    cur = arg_v
    for k in range(L, 0, -1):
        cur = pred2[k][cur]
        if cur < 0:
            break
        path.append(cur)
    path = list(reversed(path))
    if len(path) < 3:
        return mu, []

    # Need quick access to weight for a specific chosen edge (u->v). Use dict of min weight.
    w_min: Dict[Tuple[int, int], float] = {}
    for u, v, w in edges:
        key = (u, v)
        if key not in w_min or w < w_min[key]:
            w_min[key] = w

    best_cycle: List[int] = []
    best_mean = inf
    first_pos: Dict[int, int] = {}
    for j, v in enumerate(path):
        if v in first_pos:
            i = first_pos[v]
            if j - i >= 1:
                cyc_nodes = path[i:j]
                # Compute mean along consecutive edges plus closing edge.
                s = 0.0
                ok = True
                for t in range(len(cyc_nodes)):
                    a = cyc_nodes[t]
                    b = cyc_nodes[(t + 1) % len(cyc_nodes)]
                    ww = w_min.get((a, b), None)
                    if ww is None:
                        ok = False
                        break
                    s += ww
                if ok:
                    m = s / float(len(cyc_nodes))
                    if m < best_mean:
                        best_mean = m
                        best_cycle = cyc_nodes
        else:
            first_pos[v] = j

    return mu, best_cycle


def _cycle_mean_phi(cycle: List[int], phi_edges: Dict[Tuple[int, int], Tuple[int, int, int]]) -> Tuple[float, float, float]:
    if not cycle:
        return (float("nan"), float("nan"), float("nan"))
    s_chi = 0
    s_nu = 0
    s_xi = 0
    L = len(cycle)
    for t in range(L):
        a = cycle[t]
        b = cycle[(t + 1) % L]
        chi, nu, xi = phi_edges[(a, b)]
        s_chi += chi
        s_nu += nu
        s_xi += xi
    return (s_chi / L, s_nu / L, s_xi / L)


def main() -> None:
    prog = Progress(label="real-input-40-rotation-polytope", every_seconds=20.0)
    _states40, edges40 = _build_graph_edges()
    n40 = 40
    ess_nodes, ess_edges = _extract_essential_scc(n40, edges40)
    n = max([e.src for e in ess_edges] + [e.dst for e in ess_edges] + [-1]) + 1
    prog.tick(f"essential SCC: |V|={n} (from 40), |E|={len(ess_edges)}")

    # Build scalar-weight edges for each theta and a (u,v)->Phi map (choose one representative).
    phi_map: Dict[Tuple[int, int], Tuple[int, int, int]] = {}
    for e in ess_edges:
        key = (e.src, e.dst)
        # If multiple edges exist between same (src,dst), keep one (they share labels in practice).
        if key not in phi_map:
            phi_map[key] = (e.chi, e.nu, e.xi)

    # Sample directions theta in Z^3 (small set, reviewer-friendly).
    thetas: List[Tuple[int, int, int]] = [
        (1, 0, 0),
        (-1, 0, 0),
        (0, 1, 0),
        (0, -1, 0),
        (0, 0, 1),
        (0, 0, -1),
        (1, 0, 1),
        (1, 0, -1),
        (-1, 0, 1),
        (-1, 0, -1),
        (0, 1, 1),
        (0, 1, -1),
        (1, 1, 0),
        (1, -1, 0),
        (1, 1, 1),
        (1, 1, -1),
    ]

    rows: List[dict] = []
    for th in thetas:
        t1, t2, t3 = th
        # Build weighted edges list (u,v,w).
        w_edges: List[Tuple[int, int, float]] = []
        for e in ess_edges:
            w = float(t1 * e.chi + t2 * e.nu + t3 * e.xi)
            w_edges.append((e.src, e.dst, w))
        mu, cyc = _min_cycle_mean_karp(n, w_edges)
        mchi, mnu, mxi = _cycle_mean_phi(cyc, phi_map) if cyc else (float("nan"), float("nan"), float("nan"))
        rows.append(
            {
                "theta": list(th),
                "mu": mu,
                "cycle_len": len(cyc),
                "mean_chi": mchi,
                "mean_nu": mnu,
                "mean_xi": mxi,
            }
        )
        prog.tick(f"theta={th} mu~{mu:.6g} cycle_len={len(cyc)}")

    out_json = export_dir() / "real_input_40_rotation_polytope_sample.json"
    _write_text(out_json, json.dumps({"thetas": [list(t) for t in thetas], "rows": rows}, indent=2, sort_keys=True) + "\n")

    # TeX table.
    def fmt(x: float) -> str:
        if not math.isfinite(x):
            return "\\text{nan}"
        return f"{x:.6g}"

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_rotation_polytope.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\begin{tabular}{@{}rrrrrrrr@{}}")
    lines.append("\\toprule")
    lines.append("$\\theta_\\chi$ & $\\theta_-$ & $\\theta_2$ & $\\mu(\\theta)$ & $|\\gamma|$ & $\\overline{\\chi}$ & $\\overline{\\nu}$ & $\\overline{\\xi}$\\\\")
    lines.append("\\midrule")
    for r in rows:
        t1, t2, t3 = r["theta"]
        lines.append(
            f"{t1} & {t2} & {t3} & {fmt(float(r['mu']))} & {int(r['cycle_len'])} & {fmt(float(r['mean_chi']))} & {fmt(float(r['mean_nu']))} & {fmt(float(r['mean_xi']))}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{真实输入 40 状态核（取 essential 20 状态核心）上，向量观测量 $\\Phi=(\\chi,\\nu,\\xi)$ 的 rotation polytope 采样：对若干方向 $\\theta$，以 $\\phi_\\theta=\\langle\\theta,\\Phi\\rangle$ 标量化，并在图上求最小平均回路权 $\\mu(\\theta)$ 及其见证周期轨道 $\\gamma$（输出其周期均值 $(\\overline\\chi,\\overline\\nu,\\overline\\xi)$）。}"
    )
    lines.append("\\label{tab:real-input-40-rotation-polytope-sample}")
    lines.append("\\end{table}")
    lines.append("")

    out_tex = generated_dir() / "tab_real_input_40_rotation_polytope_sample.tex"
    _write_text(out_tex, "\n".join(lines))

    print(f"[real-input-40-rotation-polytope] wrote {out_json}", flush=True)
    print(f"[real-input-40-rotation-polytope] wrote {out_tex}", flush=True)
    print("[real-input-40-rotation-polytope] done", flush=True)


if __name__ == "__main__":
    main()

