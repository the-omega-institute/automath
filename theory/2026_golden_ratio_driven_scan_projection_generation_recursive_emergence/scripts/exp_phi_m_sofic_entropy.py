#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute a right-resolving presentation and entropy for Y_m = Phi_m({0,1}^Z).

We build:
1) The labeled graph G_m from the paper (states are (m-1)-bit suffixes; edges labeled by Fold_m on windows).
2) Determinize it by subset construction to get a right-resolving labeled graph H_det.
3) Minimize H_det by right-language equivalence (coarsest congruence with a rejecting dead state).
4) Extract an essential strongly connected component and compute its adjacency spectral radius.

Outputs:
- artifacts/export/phi_m_sofic_entropy.csv
"""

from __future__ import annotations

import csv
import math
import time
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

import numpy as np

from common_paths import export_dir
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


def build_Gm_edges(m: int, fold_map: List[int]) -> Tuple[int, Dict[int, Dict[int, int]]]:
    """Return (num_vertices, transitions) for G_m in packed-int form.

    Vertices: v in [0, 2^(m-1)) representing (m-1)-bit suffix.
    For each vertex v, there are two outgoing edges b in {0,1}:
      v -> v' where v' is shift-left append b,
      labeled by a = Fold_m(v||b) as a packed m-bit int in X_m.

    transitions[v][a] is a bitmask of target vertices (could be multiple targets for same label).
    """
    if m <= 1:
        # Convention: V_m has size 1 when m-1==0.
        nV = 1
    else:
        nV = 1 << (m - 1)
    maskV = nV - 1

    trans: Dict[int, Dict[int, int]] = {v: {} for v in range(nV)}
    for v in range(nV):
        for b in (0, 1):
            if m <= 1:
                window = b
                tgt = 0
            else:
                window = ((v << 1) | b) & ((1 << m) - 1)  # m bits
                tgt = ((v << 1) | b) & maskV
            a = fold_map[window] if m >= 1 else 0
            # accumulate possibly multiple targets for the same label
            d = trans[v]
            d[a] = d.get(a, 0) | (1 << tgt)
    return nV, trans


def determinize(nV: int, trans: Dict[int, Dict[int, int]], prog: Progress) -> Tuple[int, List[Dict[int, int]]]:
    """Determinize to get right-resolving graph states as subsets of V.

    Returns (start_state_id, det_transitions) where det_transitions[sid][label] = sid'.
    """
    # subset bitmask uses nV bits
    start_mask = (1 << nV) - 1  # all vertices
    q: deque[int] = deque([start_mask])
    id_of: Dict[int, int] = {start_mask: 0}
    masks: List[int] = [start_mask]
    det: List[Dict[int, int]] = []

    while q:
        S = q.popleft()
        sid = id_of[S]
        while len(det) <= sid:
            det.append({})

        # collect label -> next subset
        next_by_label: Dict[int, int] = {}
        # iterate vertices in S
        vv = S
        while vv:
            lsb = vv & -vv
            v = (lsb.bit_length() - 1)
            vv -= lsb
            for a, tgt_mask in trans[v].items():
                next_by_label[a] = next_by_label.get(a, 0) | tgt_mask
        # create transitions
        for a, T in next_by_label.items():
            if T not in id_of:
                id_of[T] = len(masks)
                masks.append(T)
                q.append(T)
            det[sid][a] = id_of[T]
        prog.tick(f"determinize nV={nV} states={len(masks)} queue={len(q)}")

    return 0, det


def minimize_right_language(
    det: List[Dict[int, int]],
) -> Tuple[int, List[Dict[int, int]]]:
    """Minimize deterministic partial automaton by right-language equivalence.

    We add a rejecting dead state (id = n) and treat missing labels as transitions to dead.
    All non-dead states are accepting; dead is rejecting.
    """
    n = len(det)
    dead = n

    # Initial partition: dead vs others.
    cls = [0] * (n + 1)
    for i in range(n):
        cls[i] = 1
    cls[dead] = 0

    changed = True
    while changed:
        changed = False
        sig_to_new: Dict[Tuple[int, Tuple[Tuple[int, int], ...]], int] = {}
        new_cls = [0] * (n + 1)

        for i in range(n + 1):
            acc = 1 if i != dead else 0
            if i == dead:
                items: Tuple[Tuple[int, int], ...] = tuple()
            else:
                # signature over defined labels only; missing labels implicitly go to dead-class
                items = tuple(sorted((a, cls[j]) for a, j in det[i].items()))
            sig = (acc, items)
            if sig not in sig_to_new:
                sig_to_new[sig] = len(sig_to_new)
            new_cls[i] = sig_to_new[sig]

        if new_cls != cls:
            cls = new_cls
            changed = True

    # Build quotient transitions (keep dead class too, then drop later)
    num_classes = max(cls) + 1
    rep: List[int] = [-1] * num_classes
    for i in range(n + 1):
        c = cls[i]
        if rep[c] == -1:
            rep[c] = i

    out: List[Dict[int, int]] = [defaultdict(int) for _ in range(num_classes)]
    for c in range(num_classes):
        i = rep[c]
        if i == -1 or i == dead:
            continue
        for a, j in det[i].items():
            out[c][a] = cls[j]

    start_class = cls[0]
    # convert defaultdict to dict
    out2: List[Dict[int, int]] = [dict(d) for d in out]
    return start_class, out2


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


def compute_entropy_from_det(start: int, det_min: List[Dict[int, int]]) -> Tuple[int, int, float]:
    """Return (num_states, num_edges, entropy_log_rho) for the essential component."""
    n = len(det_min)

    # Build adjacency with multiplicities (count of labels leading to the same next state).
    adj_mult: List[Dict[int, int]] = [defaultdict(int) for _ in range(n)]
    adj_simple: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        for _, j in det_min[i].items():
            adj_mult[i][j] += 1
    for i in range(n):
        adj_simple[i] = list(adj_mult[i].keys())

    # Reachable from start
    reach = [False] * n
    q: deque[int] = deque([start])
    reach[start] = True
    while q:
        v = q.popleft()
        for u in adj_simple[v]:
            if not reach[u]:
                reach[u] = True
                q.append(u)

    # SCCs on reachable subgraph
    idx_map = {i: k for k, i in enumerate([i for i in range(n) if reach[i]])}
    inv = [i for i in range(n) if reach[i]]
    if not inv:
        return 0, 0, 0.0
    adj_r: List[List[int]] = [[] for _ in inv]
    for i in inv:
        ii = idx_map[i]
        adj_r[ii] = [idx_map[j] for j in adj_simple[i] if reach[j]]
    comps = _scc_kosaraju(adj_r)

    # pick the SCC with maximum spectral radius (essential entropy carrier)
    best_log_rho = 0.0
    best_states: List[int] = []
    for comp in comps:
        if len(comp) == 1:
            v = comp[0]
            # self-loop?
            if v not in adj_r[v]:
                continue
        # build matrix for this SCC
        comp_set = set(comp)
        k = len(comp)
        M = np.zeros((k, k), dtype=np.float64)
        pos = {comp[i]: i for i in range(k)}
        for u in comp:
            iu = pos[u]
            orig_u = inv[u]
            for orig_v, c in adj_mult[orig_u].items():
                if reach[orig_v]:
                    v = idx_map[orig_v]
                    if v in comp_set:
                        iv = pos[v]
                        M[iu, iv] += float(c)
        # spectral radius
        vals = np.linalg.eigvals(M)
        rho = max(abs(v) for v in vals) if len(vals) else 0.0
        if rho > 0:
            log_rho = float(math.log(rho))
            if log_rho > best_log_rho:
                best_log_rho = log_rho
                best_states = comp

    # count edges (label transitions) restricted to reachable part (approx)
    num_edges = sum(len(det_min[i]) for i in range(n) if reach[i])
    return len(best_states), num_edges, best_log_rho


@dataclass(frozen=True)
class Row:
    m: int
    det_states: int
    min_states: int
    ess_states: int
    det_edges: int
    entropy: float


def main() -> None:
    out_csv = export_dir() / "phi_m_sofic_entropy.csv"
    out_csv.parent.mkdir(parents=True, exist_ok=True)

    ms = [2, 3, 4, 5, 6, 7, 8]
    prog = Progress("exp_phi_m_sofic_entropy", every_seconds=20.0)

    rows: List[Row] = []
    t0_all = time.time()
    for m in ms:
        t0 = time.time()
        fold_map = build_fold_map(m, prog)
        nV, trans = build_Gm_edges(m, fold_map)
        start_det, det = determinize(nV, trans, prog)
        start_min, det_min = minimize_right_language(det)
        ess_states, det_edges, h = compute_entropy_from_det(start_min, det_min)
        rows.append(
            Row(
                m=m,
                det_states=len(det),
                min_states=len(det_min),
                ess_states=ess_states,
                det_edges=det_edges,
                entropy=h,
            )
        )
        dt = time.time() - t0
        print(
            f"[exp_phi_m_sofic_entropy] m={m} det={len(det)} min={len(det_min)} ess={ess_states} h={h:.6g} dt={dt:.2f}s",
            flush=True,
        )

    with out_csv.open("w", encoding="utf-8", newline="") as f:
        wr = csv.DictWriter(
            f,
            fieldnames=["m", "det_states", "min_states", "ess_states", "det_edges", "h_top"],
        )
        wr.writeheader()
        for r in rows:
            wr.writerow(
                {
                    "m": r.m,
                    "det_states": r.det_states,
                    "min_states": r.min_states,
                    "ess_states": r.ess_states,
                    "det_edges": r.det_edges,
                    "h_top": f"{r.entropy:.12g}",
                }
            )

    dt_all = time.time() - t0_all
    print(f"[exp_phi_m_sofic_entropy] WROTE {out_csv} in {dt_all:.1f}s", flush=True)


if __name__ == "__main__":
    main()

