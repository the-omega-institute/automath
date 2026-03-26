#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Bowen–Franks / Cuntz–Krieger K-theory invariants, Parry internal distribution, and nilpotent indices.

We work with the real-input 40-state kernel adjacency matrix M (integer, multi-edge counts),
and its unique essential SCC adjacency M_ess (size 20), as defined in the appendix.

This script computes:
  (I)  Smith normal form of I - M_ess and I - M_ess^T, giving BF group and K_0/K_1 of O_{M_ess}.
       We also compute the same for the full 40x40 matrix (as a consistency check).
  (II) Parry (max-entropy) vertex distribution on the essential SFT: pi_i ∝ l_i r_i,
       and its conditional distribution P(sync_state | memory) in Q(sqrt(5)) if possible.
  (III) Nilpotent/Jordan index at eigenvalue 0 via the kernel dimension chain dim ker(A^k).

Outputs (default):
  - artifacts/export/real_input_40_operator_algebra_invariants.json
  - sections/generated/tab_real_input_40_bf_ktheory.tex
  - sections/generated/tab_real_input_40_parry_internal_distribution.tex
  - sections/generated/tab_real_input_40_nilpotent_jordan.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import build_kernel_edges, build_kernel_map, build_real_input_matrix_int, build_real_input_states


def _adj_list_from_matrix(M: List[List[int]]) -> List[List[int]]:
    n = len(M)
    adj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        row = M[i]
        outs = []
        for j in range(n):
            if row[j] != 0:
                outs.append(j)
        adj[i] = outs
    return adj


def _scc_kosaraju(adj: List[List[int]]) -> List[List[int]]:
    n = len(adj)
    radj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        for j in adj[i]:
            radj[j].append(i)

    seen = [False] * n
    order: List[int] = []

    def dfs1(v: int) -> None:
        stack = [(v, 0)]
        seen[v] = True
        while stack:
            x, it = stack[-1]
            if it < len(adj[x]):
                y = adj[x][it]
                stack[-1] = (x, it + 1)
                if not seen[y]:
                    seen[y] = True
                    stack.append((y, 0))
            else:
                order.append(x)
                stack.pop()

    for v in range(n):
        if not seen[v]:
            dfs1(v)

    comp_id = [-1] * n
    comps: List[List[int]] = []

    def dfs2(v: int, cid: int) -> None:
        stack = [v]
        comp_id[v] = cid
        cur: List[int] = []
        while stack:
            x = stack.pop()
            cur.append(x)
            for y in radj[x]:
                if comp_id[y] == -1:
                    comp_id[y] = cid
                    stack.append(y)
        comps.append(cur)

    for v in reversed(order):
        if comp_id[v] == -1:
            dfs2(v, len(comps))

    return comps


def _essential_scc(adj: List[List[int]]) -> List[int]:
    comps = _scc_kosaraju(adj)
    n = len(adj)
    comp_of = [-1] * n
    for cid, vs in enumerate(comps):
        for v in vs:
            comp_of[v] = cid

    out_to_other = [False] * len(comps)
    for v in range(n):
        c = comp_of[v]
        for w in adj[v]:
            if comp_of[w] != c:
                out_to_other[c] = True
                break

    essential = [cid for cid in range(len(comps)) if not out_to_other[cid] and len(comps[cid]) > 1]
    if len(essential) != 1:
        raise RuntimeError(f"expected unique essential SCC, got {[(cid,len(comps[cid])) for cid in essential]}")
    return sorted(comps[essential[0]])


def _submatrix(M: List[List[int]], idx: List[int]) -> List[List[int]]:
    return [[M[i][j] for j in idx] for i in idx]


def _smith_invariants(I_minus_A: sp.Matrix) -> Tuple[List[int], int]:
    # Returns (nontrivial diagonal invariants incl. zeros) and rank over Z.
    from sympy.matrices.normalforms import smith_normal_form

    S = smith_normal_form(I_minus_A, domain=sp.ZZ)
    diag = [int(S[i, i]) for i in range(int(S.rows))]
    # rank = number of nonzero diagonal entries
    rank = sum(1 for d in diag if d != 0)
    return diag, rank


def _bf_group_from_snf(diag: List[int]) -> Tuple[int, List[int]]:
    # coker diag map: Z^{n-rank} free rank plus torsion factors for d>1.
    free_rank = sum(1 for d in diag if d == 0)
    torsion = [d for d in diag if abs(d) not in (0, 1)]
    torsion = [abs(d) for d in torsion]
    return free_rank, torsion


def _nullity_chain(A: sp.Matrix, k_max: int) -> List[int]:
    n = A.rows
    cur = A
    out: List[int] = []
    for k in range(1, k_max + 1):
        if k > 1:
            cur = cur * A
        rk = int(cur.rank())
        out.append(n - rk)
    return out


def _jordan_block_stats_from_nullities(nulls: List[int]) -> Dict[str, object]:
    # For eigenvalue 0 nilpotent Jordan blocks:
    # a_k := nullity(A^k) - nullity(A^{k-1}) counts blocks of size >= k.
    n_prev = 0
    a = []
    for nk in nulls:
        a.append(nk - n_prev)
        n_prev = nk
    # blocks of exact size k: a_k - a_{k+1}, with a_{K+1}:=0
    exact = []
    for i in range(len(a)):
        nxt = a[i + 1] if i + 1 < len(a) else 0
        exact.append(a[i] - nxt)
    max_size = max(i + 1 for i, x in enumerate(a) if x > 0) if a else 0
    return {"a_ge_k": a, "blocks_exact_k": exact, "max_block_size": max_size}


def _nsimplify_sqrt5(x: float) -> sp.Expr:
    s5 = sp.sqrt(5)
    return sp.nsimplify(x, [s5])


def _parry_vertex_distribution(A_int: List[List[int]]) -> Tuple[float, List[float], List[float], List[float]]:
    # Numeric eigenvectors for Perron root.
    A = np.array(A_int, dtype=float)
    vals, vecs = np.linalg.eig(A)
    idx = int(np.argmax(np.real(vals)))
    lam = float(np.real(vals[idx]))
    r = np.real(vecs[:, idx])
    # left eigenvector from A^T
    vals2, vecs2 = np.linalg.eig(A.T)
    idx2 = int(np.argmax(np.real(vals2)))
    l = np.real(vecs2[:, idx2])
    # make positive
    if np.sum(r) < 0:
        r = -r
    if np.sum(l) < 0:
        l = -l
    # normalize
    lr = float(np.dot(l, r))
    pi = (l * r) / lr
    return lam, l.tolist(), r.tolist(), pi.tolist()


def _format_expr_qsqrt5(expr: sp.Expr) -> str:
    expr = sp.simplify(expr)
    return sp.latex(expr)


def write_bf_table(path: Path, *, core_diag: List[int], full_diag: List[int]) -> None:
    def summarize(diag: List[int]) -> str:
        # compress 1's count
        ones = sum(1 for d in diag if abs(d) == 1)
        rest = [d for d in diag if abs(d) != 1]
        rest_str = ",".join(str(d) for d in rest)
        return f"diag(1^{{{ones}}},{rest_str})"

    core_free, core_tors = _bf_group_from_snf(core_diag)
    full_free, full_tors = _bf_group_from_snf(full_diag)

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Smith normal form of $I-A$ for the real-input kernel (essential core vs full matrix). "
        "From SNF we read the Bowen--Franks group $\\mathrm{BF}(A)=\\mathbb Z^N/(I-A)\\mathbb Z^N$ and "
        "Cuntz--Krieger groups $K_0(\\mathcal O_A)\\cong\\mathrm{coker}(I-A^\\mathsf T)$, $K_1(\\mathcal O_A)\\cong\\ker(I-A^\\mathsf T)$.}"
    )
    lines.append("\\label{tab:real_input_40_bf_ktheory}")
    lines.append("\\begin{tabular}{l l l}")
    lines.append("\\toprule")
    lines.append("matrix & SNF$(I-A)$ & $\\mathrm{BF}(A)$\\\\")
    lines.append("\\midrule")
    lines.append(
        f"essential core ($20\\times20$) & ${summarize(core_diag)}$ & $\\mathbb Z^{core_free}\\oplus (\\mathbb Z/{core_tors[0]}\\mathbb Z)$\\\\"
        if core_tors
        else f"essential core ($20\\times20$) & ${summarize(core_diag)}$ & $\\mathbb Z^{core_free}$\\\\"
    )
    lines.append(
        f"full ($40\\times40$) & ${summarize(full_diag)}$ & $\\mathbb Z^{full_free}\\oplus (\\mathbb Z/{full_tors[0]}\\mathbb Z)$\\\\"
        if full_tors
        else f"full ($40\\times40$) & ${summarize(full_diag)}$ & $\\mathbb Z^{full_free}$\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_parry_table(
    path: Path,
    *,
    core_states: List[Tuple[str, int, int]],
    pi_core: List[float],
) -> None:
    # memory groups: (px,py) in {00,01,10,11}
    mems = [(0, 0), (0, 1), (1, 0), (1, 1)]
    mem_name = {(0, 0): "00", (0, 1): "01", (1, 0): "10", (1, 1): "11"}

    # group totals
    mem_total: Dict[Tuple[int, int], float] = {m: 0.0 for m in mems}
    for st, p in zip(core_states, pi_core):
        _, px, py = st
        mem_total[(px, py)] += float(p)

    # conditional distribution on sync state given memory
    # also compute marginal on sync state (10 symbols)
    syncs = sorted({s for (s, _, _) in core_states})
    sync_total: Dict[str, float] = {s: 0.0 for s in syncs}
    cond: Dict[Tuple[int, int], Dict[str, float]] = {m: {s: 0.0 for s in syncs} for m in mems}
    for (s, px, py), p in zip(core_states, pi_core):
        sync_total[s] += float(p)
        cond[(px, py)][s] += float(p)
    for m in mems:
        tot = mem_total[m]
        if tot > 0:
            for s in syncs:
                cond[m][s] /= tot

    # Try to express conditionals and marginals in Q(sqrt5).
    s5 = sp.sqrt(5)
    cond_expr: Dict[Tuple[int, int], Dict[str, sp.Expr]] = {m: {} for m in mems}
    sync_expr: Dict[str, sp.Expr] = {}
    for m in mems:
        for s in syncs:
            v = cond[m][s]
            if v == 0.0:
                continue
            cond_expr[m][s] = sp.simplify(sp.nsimplify(v, [s5]))
    for s in syncs:
        sync_expr[s] = sp.simplify(sp.nsimplify(sync_total[s], [s5]))

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Parry (max-entropy) vertex distribution on the essential 20-state real-input kernel, "
        "reported as conditional frequencies of the 10 sync states $s\\in Q$ given the memory $(p_x,p_y)\\in\\{00,01,10,11\\}$. "
        "Values are simplified in $\\mathbb Q(\\sqrt5)$ when possible.}"
    )
    lines.append("\\label{tab:real_input_40_parry_internal_distribution}")
    lines.append("\\begin{tabular}{l l l}")
    lines.append("\\toprule")
    lines.append("memory $m$ & allowed sync states and $\\mathbb P(s\\mid m)$ & check\\\\")
    lines.append("\\midrule")
    for m in mems:
        allowed = [(s, cond_expr[m].get(s, sp.Integer(0))) for s in syncs if s in cond_expr[m] and cond[m][s] > 0]
        parts = [f"{s}:\\ ${sp.latex(expr)}$" for (s, expr) in allowed]
        check = sp.simplify(sum(expr for _, expr in allowed))
        lines.append(f"${mem_name[m]}$ & " + ",\\ ".join(parts) + f" & $\\sum={sp.latex(check)}$\\\\")
    lines.append("\\midrule")
    parts2 = [f"{s}:\\ ${sp.latex(sync_expr[s])}$" for s in syncs]
    lines.append("\\multicolumn{3}{l}{sync marginal $\\mathbb P(s)$: " + ",\\ ".join(parts2) + "}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_nilpotent_table(
    path: Path,
    *,
    core_nulls: List[int],
    full_nulls: List[int],
) -> None:
    core_stats = _jordan_block_stats_from_nullities(core_nulls)
    full_stats = _jordan_block_stats_from_nullities(full_nulls)

    def fmt_list(xs: Sequence[int]) -> str:
        return "(" + ",".join(str(int(x)) for x in xs) + ")"

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Nilpotent/Jordan shadow at eigenvalue $0$ detected by the kernel dimension chain $\\dim\\ker(A^k)$. "
        "The maximal Jordan block size for eigenvalue $0$ equals the smallest $k$ where $\\dim\\ker(A^k)$ stabilizes.}"
    )
    lines.append("\\label{tab:real_input_40_nilpotent_jordan}")
    lines.append("\\begin{tabular}{l l l l}")
    lines.append("\\toprule")
    lines.append("matrix & $(\\dim\\ker A^k)_{k\\ge1}$ & blocks exact sizes & max size\\\\")
    lines.append("\\midrule")
    lines.append(
        "essential core ($20\\times20$) & "
        + f"${fmt_list(core_nulls)}$ & "
        + f"${fmt_list(core_stats['blocks_exact_k'])}$ & "
        + f"${core_stats['max_block_size']}$\\\\"
    )
    lines.append(
        "full ($40\\times40$) & "
        + f"${fmt_list(full_nulls)}$ & "
        + f"${fmt_list(full_stats['blocks_exact_k'])}$ & "
        + f"${full_stats['max_block_size']}$\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Operator-algebra invariants and nilpotent structure for real-input kernel.")
    parser.add_argument("--nilpotent-k-core", type=int, default=3, help="Max k for core nullity chain.")
    parser.add_argument("--nilpotent-k-full", type=int, default=5, help="Max k for full nullity chain.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_operator_algebra_invariants.json"),
    )
    parser.add_argument(
        "--tex-bf-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_bf_ktheory.tex"),
    )
    parser.add_argument(
        "--tex-parry-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_parry_internal_distribution.tex"),
    )
    parser.add_argument(
        "--tex-nilpotent-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_nilpotent_jordan.tex"),
    )
    args = parser.parse_args()

    prog = Progress("real-input-40-opalg", every_seconds=20.0)

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    M_full_int = build_real_input_matrix_int(states, kernel_map)

    adj_full = _adj_list_from_matrix(M_full_int)
    ess_idx_full = _essential_scc(adj_full)
    prog.tick(f"essential SCC size={len(ess_idx_full)}")
    if len(ess_idx_full) != 20:
        raise RuntimeError(f"unexpected essential SCC size: {len(ess_idx_full)}")

    M_core_int = _submatrix(M_full_int, ess_idx_full)
    core_states = [states[i] for i in ess_idx_full]

    # Smith normal forms.
    I_full = sp.eye(40)
    I_core = sp.eye(20)
    A_full = sp.Matrix(M_full_int)
    A_core = sp.Matrix(M_core_int)
    diag_full, _ = _smith_invariants(I_full - A_full)
    diag_core, _ = _smith_invariants(I_core - A_core)
    # also compute transpose SNF for consistency
    diag_full_T, _ = _smith_invariants(I_full - A_full.T)
    diag_core_T, _ = _smith_invariants(I_core - A_core.T)
    if diag_core != diag_core_T:
        prog.tick("WARNING: SNF(I-A) != SNF(I-A^T) on core (unexpected)")
    if diag_full != diag_full_T:
        prog.tick("WARNING: SNF(I-A) != SNF(I-A^T) on full (unexpected)")

    write_bf_table(Path(args.tex_bf_out), core_diag=diag_core, full_diag=diag_full)
    prog.tick(f"wrote {args.tex_bf_out}")

    # Parry distribution (numeric + nsimplify to Q(sqrt5)).
    lam_num, l_vec, r_vec, pi_vec = _parry_vertex_distribution(M_core_int)
    write_parry_table(Path(args.tex_parry_out), core_states=core_states, pi_core=pi_vec)
    prog.tick(f"wrote {args.tex_parry_out}")

    # Nilpotent chains.
    core_nulls = _nullity_chain(A_core, int(args.nilpotent_k_core))
    full_nulls = _nullity_chain(A_full, int(args.nilpotent_k_full))
    write_nilpotent_table(Path(args.tex_nilpotent_out), core_nulls=core_nulls, full_nulls=full_nulls)
    prog.tick(f"wrote {args.tex_nilpotent_out}")

    payload: Dict[str, object] = {
        "essential_scc_size": len(ess_idx_full),
        "essential_indices_full": ess_idx_full,
        "snf_core_I_minus_A_diag": diag_core,
        "snf_core_I_minus_AT_diag": diag_core_T,
        "snf_full_I_minus_A_diag": diag_full,
        "snf_full_I_minus_AT_diag": diag_full_T,
        "parry_lambda_numeric": lam_num,
        "parry_pi_core_numeric": pi_vec,
        "core_nullities": core_nulls,
        "full_nullities": full_nulls,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[real-input-40-opalg] wrote {jout}", flush=True)


if __name__ == "__main__":
    main()

