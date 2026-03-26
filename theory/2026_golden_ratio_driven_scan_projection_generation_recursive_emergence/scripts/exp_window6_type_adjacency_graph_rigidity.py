#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Type adjacency graph Γ_6 induced by hypercube edges, and its rigidity.

All code is English-only by repository convention.

We define the label map
  F6(omega) := Fold^{bin}_6(int_6(omega)) ∈ X6,
on Omega_6={0,1}^6 with the hypercube graph Q_6 (Hamming distance 1).

The type adjacency graph Γ_6 is the simple graph on vertices X_6 where
  u ~_{Γ_6} v  <=>  exists an edge (x~y) in Q_6 with F6(x)=u and F6(y)=v, u≠v.

We compute:
  - |V(Γ_6)|, |E(Γ_6)|, connectedness,
  - the diameter of Γ_6,
  - the degree histogram,
  - whether the adjacency spectrum is simple (all eigenvalues distinct),
  - the automorphism group size (we expect Aut(Γ_6) to be trivial).

Outputs:
  - artifacts/export/window6_type_adjacency_graph_rigidity.json
  - sections/generated/eq_window6_type_adjacency_graph_rigidity.tex
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Dict, List, Set, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import word_to_str, zeckendorf_digits


def _foldbin6_label(n: int) -> str:
    # For m=6, K(6)=9 (F_{10}=55 ≤ 63 < F_{11}=89), so digits up to k=9 are exact.
    digits = zeckendorf_digits(n, 9)  # digits for weights F_{k+1}, k=1..9
    return word_to_str(digits[:6])


def _build_gamma6() -> Tuple[List[str], List[Tuple[int, int]]]:
    """Return (nodes, edges) where nodes are sorted words, edges are (i<j) indices."""
    labels = [_foldbin6_label(n) for n in range(64)]
    nodes = sorted(set(labels))
    idx = {w: i for i, w in enumerate(nodes)}

    edges: Set[Tuple[int, int]] = set()
    for n in range(64):
        for k in range(6):
            m = n ^ (1 << k)
            if n < m:  # each undirected hypercube edge once
                a = labels[n]
                b = labels[m]
                if a != b:
                    i = idx[a]
                    j = idx[b]
                    edges.add((i, j) if i < j else (j, i))

    return nodes, sorted(edges)


def _adj_bitsets(n: int, edges: List[Tuple[int, int]]) -> List[int]:
    adj = [0] * n
    for i, j in edges:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def _is_connected(n: int, adj: List[int]) -> bool:
    if n == 0:
        return True
    seen = {0}
    q = deque([0])
    while q:
        v = q.popleft()
        bits = adj[v]
        while bits:
            lsb = bits & -bits
            u = lsb.bit_length() - 1
            bits -= lsb
            if u not in seen:
                seen.add(u)
                q.append(u)
    return len(seen) == n


def _diameter(n: int, adj: List[int]) -> int:
    if n == 0:
        return 0
    diam = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = deque([s])
        while q:
            v = q.popleft()
            bits = adj[v]
            while bits:
                lsb = bits & -bits
                u = lsb.bit_length() - 1
                bits -= lsb
                if dist[u] == -1:
                    dist[u] = dist[v] + 1
                    q.append(u)
        if any(d < 0 for d in dist):
            raise RuntimeError("Graph is disconnected; diameter undefined.")
        diam = max(diam, max(dist))
    return int(diam)


def _adjacency_matrix_sympy(n: int, edges: List[Tuple[int, int]]) -> sp.Matrix:
    A = sp.zeros(n, n)
    for i, j in edges:
        A[i, j] = 1
        A[j, i] = 1
    return A


def _wl_refine_colors(n: int, adj: List[int], initial: List[int]) -> List[int]:
    """1-WL color refinement using neighbor color multisets."""
    color = list(initial)
    changed = True
    while changed:
        changed = False
        sigs: List[Tuple[int, Tuple[int, ...]]] = []
        for v in range(n):
            neigh_colors: List[int] = []
            bits = adj[v]
            while bits:
                lsb = bits & -bits
                u = lsb.bit_length() - 1
                bits -= lsb
                neigh_colors.append(color[u])
            neigh_colors.sort()
            sigs.append((color[v], tuple(neigh_colors)))

        uniq: Dict[Tuple[int, Tuple[int, ...]], int] = {}
        new_color: List[int] = [0] * n
        next_id = 0
        for v, s in enumerate(sigs):
            if s not in uniq:
                uniq[s] = next_id
                next_id += 1
            new_color[v] = uniq[s]

        if new_color != color:
            color = new_color
            changed = True
    return color


def _find_nontrivial_automorphism(n: int, adj: List[int]) -> List[int] | None:
    """Return a nontrivial automorphism as a permutation list, or None if none exists."""
    deg = [adj[v].bit_count() for v in range(n)]

    # Initial partition by degree.
    deg_classes: Dict[int, List[int]] = defaultdict(list)
    for v, d in enumerate(deg):
        deg_classes[d].append(v)
    degree_values = sorted(deg_classes.keys())
    initial_color = [0] * n
    for cid, d in enumerate(degree_values):
        for v in deg_classes[d]:
            initial_color[v] = cid

    color = _wl_refine_colors(n, adj, initial_color)
    classes: Dict[int, List[int]] = defaultdict(list)
    for v, c in enumerate(color):
        classes[c].append(v)
    # Candidate sets constrained by final colors.
    same_color: List[List[int]] = [[] for _ in range(n)]
    for vs in classes.values():
        vs_sorted = sorted(vs)
        for v in vs_sorted:
            same_color[v] = vs_sorted

    # If fully refined, only identity is possible.
    if all(len(same_color[v]) == 1 for v in range(n)):
        return None

    mapped_to = [-1] * n
    mapped_from = [-1] * n

    order = sorted(range(n), key=lambda v: (len(same_color[v]), deg[v], v))

    def compatible(v: int, u: int) -> bool:
        # Check adjacency with already mapped vertices.
        for w in range(n):
            uw = mapped_to[w]
            if uw == -1:
                continue
            a = (adj[v] >> w) & 1
            b = (adj[u] >> uw) & 1
            if a != b:
                return False
        return True

    def find_next() -> Tuple[int | None, List[int]]:
        best_v: int | None = None
        best_cands: List[int] = []
        for v in order:
            if mapped_to[v] != -1:
                continue
            cands = [u for u in same_color[v] if mapped_from[u] == -1]
            if best_v is None or len(cands) < len(best_cands):
                best_v = v
                best_cands = cands
                if len(best_cands) <= 1:
                    break
        return best_v, best_cands

    result: List[int] | None = None

    def backtrack() -> None:
        nonlocal result
        if result is not None:
            return
        v, cands = find_next()
        if v is None:
            perm = list(mapped_to)
            if any(perm[i] != i for i in range(n)):
                result = perm
            return
        for u in cands:
            if compatible(v, u):
                mapped_to[v] = u
                mapped_from[u] = v
                backtrack()
                mapped_to[v] = -1
                mapped_from[u] = -1
                if result is not None:
                    return

    backtrack()
    return result


def _edge_hash(nodes: List[str], edges: List[Tuple[int, int]]) -> str:
    # Stable hash of the labeled edge set.
    parts = []
    for i, j in edges:
        a = nodes[i]
        b = nodes[j]
        parts.append(f"{a}-{b}")
    s = "\n".join(parts).encode("utf-8")
    return hashlib.sha256(s).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute Γ_6 induced by Q_6 edges and audit its rigidity.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_type_adjacency_graph_rigidity.json"),
        help="Path to JSON audit output.",
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_window6_type_adjacency_graph_rigidity.tex"),
        help="Path to generated TeX equation snippet (\\input{}).",
    )
    args = ap.parse_args()

    nodes, edges = _build_gamma6()
    n = len(nodes)
    adj = _adj_bitsets(n, edges)
    connected = _is_connected(n, adj)
    diam = _diameter(n, adj) if connected else None
    deg = [adj[v].bit_count() for v in range(n)]
    deg_hist = Counter(deg)

    # Simple spectrum check: characteristic polynomial is squarefree over Q.
    A_sp = _adjacency_matrix_sympy(n, edges)
    t = sp.Symbol("t")
    chi = sp.Poly(A_sp.charpoly(t).as_expr(), t, domain="ZZ")
    g = sp.gcd(chi, chi.diff())
    spectrum_is_simple = bool(g.degree() == 0)

    nontrivial = _find_nontrivial_automorphism(n, adj)
    aut_trivial = nontrivial is None
    aut_size = 1 if aut_trivial else None  # not enumerating full group if nontrivial

    payload: Dict[str, object] = {
        "m": 6,
        "num_nodes": n,
        "num_edges": len(edges),
        "connected": bool(connected),
        "diameter": int(diam) if diam is not None else None,
        "degree_histogram": {str(k): int(v) for k, v in sorted(deg_hist.items())},
        "spectrum_is_simple": bool(spectrum_is_simple),
        "aut_is_trivial": bool(aut_trivial),
        "aut_size": aut_size,
        "nontrivial_automorphism_example": nontrivial,
        "nodes": nodes,
        "edges": [[int(i), int(j)] for i, j in edges],
        "edge_hash_sha256": _edge_hash(nodes, edges),
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX snippet.
    tex_out = Path(str(args.tex_eq_out))
    dh_parts = ",\\ ".join(f"{d}:{deg_hist[d]}" for d in sorted(deg_hist.keys()))
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_window6_type_adjacency_graph_rigidity.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(f"|V(\\Gamma_6)|&={n},\\qquad |E(\\Gamma_6)|={len(edges)},\\\\")
    lines.append(f"\\Gamma_6\\ \\text{{connected}}&=\\ {str(connected).lower()},\\\\")
    if diam is not None:
        lines.append(f"\\mathrm{{diam}}(\\Gamma_6)&=\\ {int(diam)},\\\\")
    lines.append(f"\\#\\{{v\\in V(\\Gamma_6):\\ \\deg(v)=d\\}}&=({dh_parts}),\\\\")
    lines.append(f"\\Gamma_6\\ \\text{{simple spectrum}}&=\\ {str(spectrum_is_simple).lower()},\\\\")
    if aut_trivial:
        lines.append("\\mathrm{Aut}(\\Gamma_6)&=\\{1\\}.")
    else:
        lines.append("\\mathrm{Aut}(\\Gamma_6)&\\neq\\{1\\}\\ \\text{(see JSON audit for an explicit nontrivial element)}.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append("")
    tex_out.parent.mkdir(parents=True, exist_ok=True)
    tex_out.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()

