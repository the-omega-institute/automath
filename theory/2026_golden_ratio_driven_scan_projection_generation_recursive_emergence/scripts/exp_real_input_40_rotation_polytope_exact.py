#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Exact rotation polytope for the real-input 40-state kernel (essential 20 core).

We work on the essential SCC (size 20; see Prop. `prop:real-input-40-essential-20` in
`sections/appendix/sync_kernel/real_input/app__real-input-40-kernel.tex`)
and treat the system as an edge shift (SFT) with a locally constant Z^3 observable.

This script:
  1) builds the essential 20-state directed graph of the real-input kernel,
  2) enumerates all elementary (simple) directed cycles in the essential core,
  3) computes their rotation vectors for both coordinates
       (e, nu, xi)  and  (chi, nu, xi) with chi = e - xi,
  4) verifies a closed-form V- and H-representation (6 vertices, 7 facets),
  5) emits LaTeX snippets and a JSON artifact for reproducibility.

Outputs:
  - artifacts/export/real_input_40_rotation_polytope_exact.json
  - sections/generated/eq_real_input_40_rotation_polytope_vertices.tex
  - sections/generated/eq_real_input_40_rotation_polytope_facets.tex
  - sections/generated/eq_real_input_40_rotation_polytope_zero_temp_support.tex
  - sections/generated/tab_real_input_40_rotation_polytope_vertices.tex
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Edge:
    src: int
    dst: int
    x: int
    y: int
    d: int
    e: int
    nu: int
    xi: int

    @property
    def chi(self) -> int:
        # chi = e - 1_{d=2}
        return int(self.e) - int(self.xi)


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _build_graph_40() -> Tuple[List[Tuple[str, int, int]], List[Edge]]:
    """
    Return (states, edges) for the 40-state real-input kernel.

    states are triples (s, px, py) where s in Q and (px,py) is 1-bit memory.
    edges are labeled by (x,y)->d and produce output bit e and indicators (nu,xi).
    """
    # Keep consistent with the kernel definition used across the paper.
    from exp_sync_kernel_real_input_40_arity_3d import build_kernel_edges, build_kernel_map, build_real_input_states

    kernel_map = build_kernel_map(build_kernel_edges())  # (s,d) -> (t,e)
    states = list(build_real_input_states())
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
                # Observables:
                xi = 1 if d == 2 else 0
                # Negative-carry event is "entering" Q_- (destination state in Q_-).
                nu = 1 if "-" in dst_state else 0
                u = idx[(s, px, py)]
                v = idx[(dst_state, x, y)]
                edges.append(Edge(src=u, dst=v, x=x, y=y, d=d, e=int(e), nu=nu, xi=xi))
    return states, edges


def _scc_kosaraju(n: int, edges: Sequence[Edge]) -> List[List[int]]:
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


def _extract_essential_scc(states40: Sequence[Tuple[str, int, int]], edges40: Sequence[Edge]) -> Tuple[List[int], List[Edge]]:
    """Pick the unique essential SCC and restrict edges to it."""
    n = len(states40)
    comps = _scc_kosaraju(n, edges40)
    comps_sorted = sorted(comps, key=len, reverse=True)
    ess_nodes = sorted(comps_sorted[0])
    if len(ess_nodes) != 20:
        raise SystemExit(f"[rotation-polytope-exact] expected essential SCC size 20, got {len(ess_nodes)}")
    ess_set = set(ess_nodes)
    new_id = {v: i for i, v in enumerate(ess_nodes)}
    edges2: List[Edge] = []
    for e in edges40:
        if e.src in ess_set and e.dst in ess_set:
            edges2.append(
                Edge(
                    src=new_id[e.src],
                    dst=new_id[e.dst],
                    x=e.x,
                    y=e.y,
                    d=e.d,
                    e=e.e,
                    nu=e.nu,
                    xi=e.xi,
                )
            )
    return ess_nodes, edges2


def _build_edge_map(edges: Sequence[Edge]) -> Dict[Tuple[int, int], Edge]:
    out: Dict[Tuple[int, int], Edge] = {}
    for e in edges:
        key = (e.src, e.dst)
        if key in out:
            # Should not happen for this presentation (branch graph has unique edge per (src,dst)).
            raise SystemExit(f"[rotation-polytope-exact] duplicate edge key {key}")
        out[key] = e
    return out


def _enumerate_simple_cycles(n: int, adj: Sequence[Sequence[int]]) -> List[List[int]]:
    """
    Enumerate all elementary directed cycles, each reported once.

    Strategy: for each start vertex s, depth-first search but only traverse vertices >= s.
    This reports each cycle exactly once (at its minimal vertex).
    """
    cycles: List[List[int]] = []
    for s in range(n):
        stack: List[int] = [s]
        seen = {s}

        def dfs(v: int) -> None:
            for w in adj[v]:
                if w < s:
                    continue
                if w == s:
                    cycles.append(stack.copy())
                    continue
                if w in seen:
                    continue
                seen.add(w)
                stack.append(w)
                dfs(w)
                stack.pop()
                seen.remove(w)

        dfs(s)
    return cycles


def _cycle_sums(cycle: Sequence[int], edge_map: Dict[Tuple[int, int], Edge]) -> Tuple[int, int, int]:
    E = 0
    N = 0
    X = 0
    L = len(cycle)
    for i in range(L):
        a = int(cycle[i])
        b = int(cycle[(i + 1) % L])
        e = edge_map[(a, b)]
        E += int(e.e)
        N += int(e.nu)
        X += int(e.xi)
    return E, N, X


def _fmt_frac(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return rf"\tfrac{{{x.numerator}}}{{{x.denominator}}}"


def _as_frac_tuple(v: Tuple[int, int, int], L: int) -> Tuple[Fraction, Fraction, Fraction]:
    a, b, c = v
    return (Fraction(a, L), Fraction(b, L), Fraction(c, L))


def _solve_vertices_from_inequalities_e() -> List[Tuple[Fraction, Fraction, Fraction]]:
    """
    Compute vertex set of the claimed H-representation in (e,nu,xi) coordinates.

    Inequalities (all are <= form):
      (1) -xi <= 0                  (xi >= 0)
      (2) -e + xi <= 0              (xi <= e)
      (3)  e <= 1/2
      (4) -2 nu + xi <= 0           (xi <= 2 nu)
      (5) -e -nu + 2 xi <= 0        (2 xi <= e + nu)
      (6) -e + nu - xi <= 0         (nu <= e + xi)
      (7)  e - nu + 5 xi <= 2
    """
    A = [
        (Fraction(0), Fraction(0), Fraction(-1), Fraction(0)),
        (Fraction(-1), Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(0), Fraction(0), Fraction(1, 2)),
        (Fraction(0), Fraction(-2), Fraction(1), Fraction(0)),
        (Fraction(-1), Fraction(-1), Fraction(2), Fraction(0)),
        (Fraction(-1), Fraction(1), Fraction(-1), Fraction(0)),
        (Fraction(1), Fraction(-1), Fraction(5), Fraction(2)),
    ]

    def sat(pt: Tuple[Fraction, Fraction, Fraction]) -> bool:
        e, nu, xi = pt
        for a, b, c, d in A:
            if a * e + b * nu + c * xi > d:
                return False
        return True

    pts: List[Tuple[Fraction, Fraction, Fraction]] = []
    # Enumerate intersections of triples of bounding planes.
    for i in range(len(A)):
        for j in range(i + 1, len(A)):
            for k in range(j + 1, len(A)):
                M = sp.Matrix(
                    [
                        [sp.Rational(A[i][0]), sp.Rational(A[i][1]), sp.Rational(A[i][2])],
                        [sp.Rational(A[j][0]), sp.Rational(A[j][1]), sp.Rational(A[j][2])],
                        [sp.Rational(A[k][0]), sp.Rational(A[k][1]), sp.Rational(A[k][2])],
                    ]
                )
                rhs = sp.Matrix([sp.Rational(A[i][3]), sp.Rational(A[j][3]), sp.Rational(A[k][3])])
                if M.det() == 0:
                    continue
                sol = M.LUsolve(rhs)
                pt = (Fraction(int(sol[0].p), int(sol[0].q)), Fraction(int(sol[1].p), int(sol[1].q)), Fraction(int(sol[2].p), int(sol[2].q)))
                if not sat(pt):
                    continue
                pts.append(pt)

    # Deduplicate and sort.
    uniq = sorted(set(pts), key=lambda t: (t[0], t[1], t[2]))
    return uniq


def main() -> None:
    states40, edges40 = _build_graph_40()
    ess_nodes_old, edges20 = _extract_essential_scc(states40, edges40)
    n = 20

    # Adjacency + edge map.
    adj: List[List[int]] = [[] for _ in range(n)]
    for e in edges20:
        adj[e.src].append(e.dst)
    for v in range(n):
        adj[v] = sorted(set(adj[v]))
    edge_map = _build_edge_map(edges20)

    cycles = _enumerate_simple_cycles(n, adj)
    # Compute rotation vectors for each cycle.
    cycle_rows: List[dict] = []
    rot_e: List[Tuple[Fraction, Fraction, Fraction]] = []
    rot_chi: List[Tuple[Fraction, Fraction, Fraction]] = []
    for cyc in cycles:
        E, N, X = _cycle_sums(cyc, edge_map)
        L = len(cyc)
        ebar, nubar, xibar = _as_frac_tuple((E, N, X), L)
        chibar = ebar - xibar
        rot_e.append((ebar, nubar, xibar))
        rot_chi.append((chibar, nubar, xibar))
        cycle_rows.append(
            {
                "len": L,
                "cycle": list(cyc),
                "sum": {"E": E, "N": N, "X": X, "chi": int(E - X)},
                "mean_e": [str(ebar), str(nubar), str(xibar)],
                "mean_chi": [str(chibar), str(nubar), str(xibar)],
            }
        )

    # Claimed vertices (V-representation) in (e,nu,xi).
    V_e: List[Tuple[Fraction, Fraction, Fraction]] = [
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(1, 2), Fraction(0), Fraction(0)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(0)),
        (Fraction(1, 2), Fraction(1), Fraction(1, 2)),
        (Fraction(2, 5), Fraction(2, 5), Fraction(2, 5)),
        (Fraction(1, 2), Fraction(1, 6), Fraction(1, 3)),
    ]
    V_chi = [(e - xi, nu, xi) for (e, nu, xi) in V_e]

    # Verify: each claimed vertex is realized by some cycle, and pick shortest witness.
    witnesses: Dict[Tuple[Fraction, Fraction, Fraction], dict] = {}
    for v in V_e:
        best = None
        for row in cycle_rows:
            ebar, nubar, xibar = (Fraction(row["mean_e"][0]), Fraction(row["mean_e"][1]), Fraction(row["mean_e"][2]))
            if (ebar, nubar, xibar) != v:
                continue
            L = int(row["len"])
            if best is None or L < int(best["len"]):
                best = row
        if best is None:
            raise SystemExit(f"[rotation-polytope-exact] missing vertex witness for v={v}")
        witnesses[v] = best

    # Verify the H-representation vertices match the V-list.
    V_from_H = _solve_vertices_from_inequalities_e()
    if sorted(V_from_H) != sorted(V_e):
        raise SystemExit(f"[rotation-polytope-exact] H-vertices != claimed V-vertices.\nH={V_from_H}\nV={V_e}")

    # Verify all cycle rotation vectors satisfy the claimed inequalities (facet system).
    def sat_H_e(pt: Tuple[Fraction, Fraction, Fraction]) -> bool:
        e, nu, xi = pt
        return (
            (xi >= 0)
            and (xi <= e)
            and (e <= Fraction(1, 2))
            and (xi <= 2 * nu)
            and (2 * xi <= e + nu)
            and (nu <= e + xi)
            and (e - nu + 5 * xi <= 2)
        )

    bad = [p for p in rot_e if not sat_H_e(p)]
    if bad:
        raise SystemExit(f"[rotation-polytope-exact] found rotation vectors violating H-system: {bad[:5]}")

    # Prepare a compact payload.
    payload = {
        "graph": {
            "n40": len(states40),
            "n_ess": 20,
            "m_ess": len(edges20),
            "ess_nodes_old": ess_nodes_old,
        },
        "cycle_stats": {
            "cycle_count": len(cycles),
            "distinct_means_e": len(set(rot_e)),
            "distinct_means_chi": len(set(rot_chi)),
        },
        "vertices_e": [[str(a), str(b), str(c)] for (a, b, c) in V_e],
        "vertices_chi": [[str(a), str(b), str(c)] for (a, b, c) in V_chi],
        "witnesses": {
            f"{str(v[0])},{str(v[1])},{str(v[2])}": witnesses[v]
            for v in V_e
        },
        "cycles": cycle_rows,
    }
    out_json = export_dir() / "real_input_40_rotation_polytope_exact.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")

    # --- LaTeX outputs ---
    # (1) Vertex list in both coordinates.
    ve_tex = ",\n".join([rf"\Big({_fmt_frac(e)},{_fmt_frac(nu)},{_fmt_frac(xi)}\Big)" for (e, nu, xi) in V_e])
    vchi_tex = ",\n".join([rf"\Big({_fmt_frac(ch)},{_fmt_frac(nu)},{_fmt_frac(xi)}\Big)" for (ch, nu, xi) in V_chi])
    tex_vertices = "\n".join(
        [
            "% AUTO-GENERATED by scripts/exp_real_input_40_rotation_polytope_exact.py",
            r"\begin{align*}",
            r"\mathrm{Rot}\!\bigl(\Phi^{(e)}\bigr)",
            r"&=\mathrm{conv}\left\{",
            ve_tex,
            r"\right\},\\",
            r"\mathrm{Rot}\!\bigl(\Phi^{(\chi)}\bigr)",
            r"&=\mathrm{conv}\left\{",
            vchi_tex,
            r"\right\}.",
            r"\end{align*}",
            "",
        ]
    )
    _write_text(generated_dir() / "eq_real_input_40_rotation_polytope_vertices.tex", tex_vertices)

    # (2) Facet inequalities (both coordinates; the chi-version is the shear).
    tex_facets = "\n".join(
        [
            "% AUTO-GENERATED by scripts/exp_real_input_40_rotation_polytope_exact.py",
            r"\begin{align*}",
            r"&\text{\textbf{$(e,\nu,\xi)$ 坐标：}}\\",
            r"&\xi \ge 0,\quad \xi \le e,\quad e \le \tfrac12,\quad \xi \le 2\nu,\quad 2\xi \le e+\nu,\quad \nu \le e+\xi,\quad e-\nu+5\xi \le 2.\\[4pt]",
            r"&\text{\textbf{$(\chi,\nu,\xi)$ 坐标：}}\\",
            r"&\xi \ge 0,\quad \chi \ge 0,\quad \chi+\xi \le \tfrac12,\quad \xi \le 2\nu,\quad \xi \le \chi+\nu,\quad \nu \le \chi+2\xi,\quad \chi-\nu+6\xi \le 2.",
            r"\end{align*}",
            "",
        ]
    )
    _write_text(generated_dir() / "eq_real_input_40_rotation_polytope_facets.tex", tex_facets)

    # (3) Zero-temperature support function (max over vertices) for (e,nu,xi).
    tex_zero = "\n".join(
        [
            "% AUTO-GENERATED by scripts/exp_real_input_40_rotation_polytope_exact.py",
            r"\begin{equation*}",
            r"\lim_{t\to+\infty}\frac{P(t\theta)}{t}",
            r"=\max\Bigl\{",
            r"0,",
            r"\tfrac12\,\theta_e,",
            r"\tfrac12(\theta_e+\theta_-),",
            r"\tfrac12\,\theta_e+\theta_-+\tfrac12\,\theta_2,",
            r"\tfrac25(\theta_e+\theta_-+\theta_2),",
            r"\tfrac12\,\theta_e+\tfrac16\,\theta_-+\tfrac13\,\theta_2",
            r"\Bigr\}.",
            r"\end{equation*}",
            "",
        ]
    )
    _write_text(generated_dir() / "eq_real_input_40_rotation_polytope_zero_temp_support.tex", tex_zero)

    # (4) Table of vertices with shortest witness cycle length and a branch-level (x,y)/e word.
    def word_from_cycle(cyc: Sequence[int]) -> Tuple[str, str]:
        xs: List[str] = []
        es: List[str] = []
        L = len(cyc)
        for i in range(L):
            a = int(cyc[i])
            b = int(cyc[(i + 1) % L])
            ed = edge_map[(a, b)]
            xs.append(f"({ed.x},{ed.y})")
            es.append(str(ed.e))
        return (" ".join(xs), "".join(es))

    rows: List[str] = []
    for (e, nu, xi) in V_e:
        w = witnesses[(e, nu, xi)]
        L = int(w["len"])
        cyc = w["cycle"]
        xy_word, e_word = word_from_cycle(cyc)
        chi = e - xi
        rows.append(
            " & ".join(
                [
                    f"${_fmt_frac(e)}$",
                    f"${_fmt_frac(nu)}$",
                    f"${_fmt_frac(xi)}$",
                    f"${_fmt_frac(chi)}$",
                    str(L),
                    rf"\(\,{xy_word}\,\)",
                    rf"\(\,{e_word}\,\)",
                ]
            )
            + r"\\"
        )

    tex_table = "\n".join(
        [
            "% AUTO-GENERATED by scripts/exp_real_input_40_rotation_polytope_exact.py",
            r"\begin{table}[H]",
            r"\centering",
            r"\scriptsize",
            r"\setlength{\tabcolsep}{5pt}",
            r"\begin{tabular}{@{}cccccrll@{}}",
            r"\toprule",
            r"$\bar e$ & $\bar\nu$ & $\bar\xi$ & $\bar\chi$ & $|\gamma|$ & $(x_k,y_k)$ 周期字 & $e_k$ 周期字\\",
            r"\midrule",
            *rows,
            r"\bottomrule",
            r"\end{tabular}",
            r"\caption{真实输入 40 状态核（essential 20 核心）上，三观测量 $(e,\nu,\xi)$ 的 rotation polytope 的 6 个极点（顶点）及其最短见证周期轨道。这里 $\chi=e-\xi$ 为 arity-charge。}",
            r"\label{tab:real-input-40-rotation-polytope-vertices}",
            r"\end{table}",
            "",
        ]
    )
    _write_text(generated_dir() / "tab_real_input_40_rotation_polytope_vertices.tex", tex_table)

    print(f"[rotation-polytope-exact] cycles={len(cycles)} distinct_means_e={len(set(rot_e))}", flush=True)
    print(f"[rotation-polytope-exact] wrote {out_json}", flush=True)
    print("[rotation-polytope-exact] wrote TeX snippets", flush=True)
    print("[rotation-polytope-exact] done", flush=True)


if __name__ == "__main__":
    main()

