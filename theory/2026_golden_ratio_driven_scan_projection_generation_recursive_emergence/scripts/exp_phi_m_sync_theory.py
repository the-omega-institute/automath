#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit synchronization constants for the Phi_m subset-filter automaton.

We build the right-resolving determinization H_det (subset construction) induced by
the labeled graph G_m (states are (m-1)-bit suffixes; edges labeled by Fold_m on windows).

From H_det we extract the ambiguous (non-singleton) induced subgraph H_amb:
  - If H_amb contains a directed cycle, then there exist output sequences that never
    synchronize (Y_m^{amb} is nonempty) and the worst-case sync delay is infinite.
  - If H_amb is acyclic (a DAG), then all outputs synchronize in finite time and the
    worst-case sync delay equals the longest path length in H_amb (DAG DP).

When H_amb has a recurrent cycle, we also compute the entropy gap exponent
  eps_m = log 2 - h_top(Y_m^{amb}),
by taking the maximum spectral radius among SCCs inside H_amb.

In addition, when the maximal ambiguity SCC is primitive, the same finite-state
mechanism yields a sharp Perron--Frobenius asymptotic for the *count* of
non-resolving prefixes. We therefore also export:
  - rho_amb = spectral radius of the maximal ambiguity SCC,
  - rho_amb2 = second spectral radius (max |lambda| < rho_amb; 0 if none),
  - Delta_amb = log(rho_amb / rho_amb2) when rho_amb2 > 0,
  - c_amb = PF leading constant for prefix counts when start lies in that SCC.

Outputs:
  - artifacts/export/phi_m_sync_theory.json
  - sections/generated/tab_phi_m_sync_theory.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m


def _int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def _pack_bits_to_int(bits: Iterable[int], m: int) -> int:
    x = 0
    for b in bits:
        x = (x << 1) | (1 if b else 0)
    return x & ((1 << m) - 1)


def build_fold_map(m: int, prog: Progress) -> List[int]:
    size = 1 << m
    out = [0] * size
    for w in range(size):
        bits = _int_to_bits(w, m)
        folded = fold_m(bits)
        out[w] = _pack_bits_to_int(folded, m)
        prog.tick(f"build_fold_map m={m} w={w}/{size}")
    return out


def build_Gm_edges(m: int, fold_map: List[int]) -> Tuple[int, List[Dict[int, int]]]:
    """Return (num_vertices, trans[v][label] = bitmask-of-target-vertices)."""
    if m <= 1:
        nV = 1
    else:
        nV = 1 << (m - 1)
    maskV = nV - 1

    trans: List[Dict[int, int]] = [dict() for _ in range(nV)]
    for v in range(nV):
        for b in (0, 1):
            if m <= 1:
                window = b
                tgt = 0
            else:
                window = ((v << 1) | b) & ((1 << m) - 1)
                tgt = ((v << 1) | b) & maskV
            a = fold_map[window] if m >= 1 else 0
            trans[v][a] = trans[v].get(a, 0) | (1 << tgt)
    return nV, trans


def determinize(nV: int, trans: List[Dict[int, int]], prog: Progress) -> Tuple[List[int], List[Dict[int, int]]]:
    """Determinize G_m into the subset-filter automaton.

    Returns (subset_masks, det) where:
      subset_masks[sid] is a bitmask of V_m representing the subset state,
      det[sid][label] = sid' is the deterministic transition on that label.
    """
    start_mask = (1 << nV) - 1
    q: List[int] = [start_mask]
    qi = 0
    id_of: Dict[int, int] = {start_mask: 0}
    masks: List[int] = [start_mask]
    det: List[Dict[int, int]] = []

    t0 = time.time()
    while qi < len(q):
        S = q[qi]
        qi += 1
        sid = id_of[S]
        while len(det) <= sid:
            det.append({})

        next_by_label: Dict[int, int] = {}
        vv = S
        while vv:
            lsb = vv & -vv
            v = lsb.bit_length() - 1
            vv -= lsb
            for a, tgt_mask in trans[v].items():
                next_by_label[a] = next_by_label.get(a, 0) | tgt_mask

        for a, T in next_by_label.items():
            if T not in id_of:
                id_of[T] = len(masks)
                masks.append(T)
                q.append(T)
            det[sid][a] = id_of[T]

        if sid % 400 == 0:
            elapsed = time.time() - t0
            prog.tick(f"determinize nV={nV} states={len(masks)} queue={len(q)-qi} elapsed={elapsed:.1f}s")

    return masks, det


def _is_singleton_mask(mask: int) -> bool:
    return mask != 0 and (mask & (mask - 1)) == 0


def _scc_kosaraju(adj: List[List[int]]) -> List[List[int]]:
    n = len(adj)
    radj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        for j in adj[i]:
            radj[j].append(i)

    seen = [False] * n
    order: List[int] = []

    def dfs1(v: int) -> None:
        seen[v] = True
        for u in adj[v]:
            if not seen[u]:
                dfs1(u)
        order.append(v)

    for v in range(n):
        if not seen[v]:
            dfs1(v)

    comp = [-1] * n
    comps: List[List[int]] = []

    def dfs2(v: int, cid: int) -> None:
        comp[v] = cid
        comps[cid].append(v)
        for u in radj[v]:
            if comp[u] == -1:
                dfs2(u, cid)

    for v in reversed(order):
        if comp[v] == -1:
            comps.append([])
            dfs2(v, len(comps) - 1)

    return comps


def _spectral_radius_dense(nodes: List[int], adj_mult: List[Dict[int, int]]) -> float:
    """Spectral radius of adjacency with multiplicities restricted to `nodes`.

    nodes are local indices (0..n-1) into `adj_mult` (already local).
    """
    k = len(nodes)
    if k == 0:
        return 0.0
    if k == 1:
        u = nodes[0]
        return float(adj_mult[u].get(u, 0))

    pos = {nodes[i]: i for i in range(k)}
    M = np.zeros((k, k), dtype=np.float64)
    node_set = set(nodes)
    for u in nodes:
        iu = pos[u]
        for v, c in adj_mult[u].items():
            if v in node_set:
                iv = pos[v]
                M[iu, iv] += float(c)
    vals = np.linalg.eigvals(M)
    return float(max(abs(v) for v in vals)) if len(vals) else 0.0


def _longest_path_dag(start: int, adj: List[List[int]]) -> int:
    """Longest path length in edges from start in a DAG (unweighted)."""
    n = len(adj)
    indeg = [0] * n
    for u in range(n):
        for v in adj[u]:
            indeg[v] += 1

    # Kahn topo order
    q: List[int] = [i for i in range(n) if indeg[i] == 0]
    qi = 0
    topo: List[int] = []
    while qi < len(q):
        u = q[qi]
        qi += 1
        topo.append(u)
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)

    if len(topo) != n:
        raise ValueError("Graph is not a DAG")

    neg_inf = -(1 << 60)
    dist = [neg_inf] * n
    dist[start] = 0
    for u in topo:
        du = dist[u]
        if du == neg_inf:
            continue
        for v in adj[u]:
            if du + 1 > dist[v]:
                dist[v] = du + 1
    return int(max(d for d in dist if d != neg_inf))


@dataclass(frozen=True)
class Row:
    m: int
    det_states: int
    det_edges: int
    amb_states: int
    amb_edges: int
    amb_cycle: bool
    D_sync: Optional[int]
    L_sync: Optional[int]
    h_amb: Optional[float]
    epsilon: Optional[float]
    rho_amb: Optional[float]
    rho_amb2: Optional[float]
    Delta_amb: Optional[float]
    c_amb: Optional[float]


def write_table_tex(path: Path, rows: List[Row]) -> None:
    def fmt_int_or_inf(x: Optional[int]) -> str:
        if x is None:
            return "$\\infty$"
        return str(int(x))

    def fmt_float(x: Optional[float]) -> str:
        if x is None:
            return "--"
        return f"{x:.6g}"

    def fmt_yesno(b: bool) -> str:
        return "yes" if b else "no"

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Synchronization constants from the subset-filter automaton for $\\Phi_m$. "
        "$H_m^{\\mathrm{amb}}$ is the induced subgraph on non-singleton filter states. "
        "If $H_m^{\\mathrm{amb}}$ has a directed cycle, then $Y_m^{\\mathrm{amb}}\\neq\\varnothing$ and the worst-case "
        "sync delay is infinite; otherwise $H_m^{\\mathrm{amb}}$ is a DAG and $D_{\\mathrm{sync}}$ is obtained by a "
        "longest-path DP, with $L_m=D_{\\mathrm{sync}}+1$. When $Y_m^{\\mathrm{amb}}\\neq\\varnothing$, we also report "
        "$h_{\\mathrm{top}}(Y_m^{\\mathrm{amb}})$ and the entropy gap $\\varepsilon_m=\\log 2-h_{\\mathrm{top}}(Y_m^{\\mathrm{amb}})$.}"
    )
    lines.append("\\label{tab:phi_m_sync_theory}")
    lines.append("\\begin{tabular}{r r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & det states & amb states & amb cycle? & $D_{\\mathrm{sync}}$ & $L_m$ & $h_{\\mathrm{top}}(Y_m^{\\mathrm{amb}})$ & $\\varepsilon_m$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.det_states} & {r.amb_states} & {fmt_yesno(r.amb_cycle)} & "
            f"{fmt_int_or_inf(r.D_sync)} & {fmt_int_or_inf(r.L_sync)} & {fmt_float(r.h_amb)} & {fmt_float(r.epsilon)}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit: synchronization constants for Phi_m.")
    parser.add_argument("--m-min", type=int, default=2, help="Minimum m (>=1).")
    parser.add_argument("--m-max", type=int, default=12, help="Maximum m.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "phi_m_sync_theory.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_phi_m_sync_theory.tex"),
    )
    args = parser.parse_args()

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    if m_min < 1:
        raise SystemExit("Require m_min >= 1")
    if m_max < m_min:
        raise SystemExit("Require m_max >= m_min")

    prog = Progress("exp_phi_m_sync_theory", every_seconds=20.0)
    rows: List[Row] = []

    t0_all = time.time()
    for m in range(m_min, m_max + 1):
        t0 = time.time()
        fold_map = build_fold_map(m, prog)
        nV, trans = build_Gm_edges(m, fold_map)
        masks, det = determinize(nV, trans, prog)

        det_edges = sum(len(d) for d in det)
        det_states = len(det)

        # Ambiguous (non-singleton) states.
        amb_ids = [sid for sid, mask in enumerate(masks) if not _is_singleton_mask(mask)]
        amb_states = len(amb_ids)
        amb_index = {sid: i for i, sid in enumerate(amb_ids)}

        # Build ambiguous adjacency (local indices) and multiplicities.
        adj_simple: List[List[int]] = [[] for _ in range(amb_states)]
        adj_mult: List[Dict[int, int]] = [dict() for _ in range(amb_states)]
        amb_edges = 0
        for sid in amb_ids:
            u = amb_index[sid]
            counts: Dict[int, int] = {}
            for tid in det[sid].values():
                if tid in amb_index:
                    v = amb_index[tid]
                    counts[v] = counts.get(v, 0) + 1
            adj_mult[u] = counts
            adj_simple[u] = list(counts.keys())
            amb_edges += sum(counts.values())

        # SCCs on ambiguous subgraph, and cycle detection.
        comps = _scc_kosaraju(adj_simple) if amb_states > 0 else []
        has_cycle = False
        for comp in comps:
            if len(comp) >= 2:
                has_cycle = True
                break
            if len(comp) == 1:
                u = comp[0]
                if u in adj_mult[u]:
                    has_cycle = True
                    break

        D_sync: Optional[int]
        L_sync: Optional[int]
        h_amb: Optional[float]
        eps: Optional[float]

        if amb_states == 0:
            # Already synchronized at time 0.
            D_sync = 0
            L_sync = 0
            h_amb = None
            eps = None
            rho_amb = None
            rho_amb2 = None
            Delta_amb = None
            c_amb = None
        elif not has_cycle:
            # Finite worst-case sync delay: longest path length in DAG.
            start_local = amb_index.get(0, 0)
            D_sync = _longest_path_dag(start_local, adj_simple)
            L_sync = D_sync + 1
            h_amb = None
            eps = None
            rho_amb = None
            rho_amb2 = None
            Delta_amb = None
            c_amb = None
        else:
            # Infinite worst-case sync delay; compute h_top on the ambiguous recurrent part.
            D_sync = None
            L_sync = None
            rho_best = 0.0
            comp_best: Optional[List[int]] = None
            for comp in comps:
                if len(comp) == 1:
                    u = comp[0]
                    if u not in adj_mult[u]:
                        continue
                rho = _spectral_radius_dense(comp, adj_mult)
                if rho > rho_best + 1e-12:
                    rho_best = rho
                    comp_best = comp
                elif abs(rho - rho_best) <= 1e-12 and comp_best is not None:
                    # Prefer a component containing the start state (if possible), otherwise larger.
                    start_local = amb_index.get(0, -1)
                    if (start_local in comp) and (start_local not in comp_best):
                        comp_best = comp
                    elif (len(comp) > len(comp_best)) and (start_local not in comp_best):
                        comp_best = comp

            rho_amb = float(rho_best) if rho_best > 0.0 else None
            h_amb = float(math.log(rho_best)) if rho_best > 0.0 else None
            eps = float(math.log(2.0) - h_amb) if h_amb is not None else None

            # Second spectral radius + PF constant on the maximal SCC, when feasible.
            rho_amb2 = None
            Delta_amb = None
            c_amb = None
            if rho_amb is not None and comp_best is not None:
                k = len(comp_best)
                # Dense eigen-decomposition is only reasonable for modest SCC sizes.
                if k <= 512:
                    pos = {comp_best[i]: i for i in range(k)}
                    M = np.zeros((k, k), dtype=np.float64)
                    comp_set = set(comp_best)
                    for u in comp_best:
                        iu = pos[u]
                        for v, c in adj_mult[u].items():
                            if v in comp_set:
                                M[iu, pos[v]] += float(c)

                    vals, vecs = np.linalg.eig(M)
                    # PF eigenvalue is the one with maximal real part for nonnegative matrices.
                    i_pf = int(np.argmax(np.real(vals)))
                    rho_pf = float(np.real(vals[i_pf]))

                    abs_vals = np.abs(vals)
                    tol = 1e-10 * max(1.0, rho_pf)
                    mask = abs_vals < (abs(rho_pf) - tol)
                    rho2 = float(np.max(abs_vals[mask])) if np.any(mask) else 0.0
                    rho_amb2 = rho2
                    if rho2 > 0.0:
                        Delta_amb = float(math.log(rho_pf / rho2))

                    # Right/left PF eigenvectors (use transpose for left).
                    v = np.real_if_close(vecs[:, i_pf]).astype(np.float64)
                    valsL, vecsL = np.linalg.eig(M.T)
                    i_pf_L = int(np.argmax(np.real(valsL)))
                    w = np.real_if_close(vecsL[:, i_pf_L]).astype(np.float64)

                    if float(np.sum(v)) < 0.0:
                        v = -v
                    if float(np.sum(w)) < 0.0:
                        w = -w

                    dot = float(np.dot(w, v))
                    if dot < 0.0:
                        w = -w
                        dot = -dot
                    if abs(dot) > 0.0:
                        v = v / dot  # normalize so w^T v == 1

                        start_local = amb_index.get(0, -1)
                        if start_local in pos:
                            c_amb = float(v[pos[start_local]] * float(np.sum(w)))

        rows.append(
            Row(
                m=m,
                det_states=det_states,
                det_edges=det_edges,
                amb_states=amb_states,
                amb_edges=amb_edges,
                amb_cycle=bool(has_cycle),
                D_sync=D_sync,
                L_sync=L_sync,
                h_amb=h_amb,
                epsilon=eps,
                rho_amb=rho_amb,
                rho_amb2=rho_amb2,
                Delta_amb=Delta_amb,
                c_amb=c_amb,
            )
        )

        dt = time.time() - t0
        print(
            f"[exp_phi_m_sync_theory] m={m} det={det_states} amb={amb_states} cycle={has_cycle} "
            f"D_sync={D_sync} L={L_sync} eps={eps} dt={dt:.2f}s",
            flush=True,
        )

    payload = {"rows": [asdict(r) for r in rows], "args": {"m_min": m_min, "m_max": m_max}}
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[exp_phi_m_sync_theory] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[exp_phi_m_sync_theory] wrote {tout}", flush=True)

    dt_all = time.time() - t0_all
    print(f"[exp_phi_m_sync_theory] DONE in {dt_all:.2f}s", flush=True)


if __name__ == "__main__":
    main()

