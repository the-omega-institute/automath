#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Closed-form package for the arity-charge weighting on the real-input 40-state kernel.

We implement an auditable certificate for:
  (A) A 0/1 coboundary normal form on the essential 20-state core:
        g(e) := chi(e) + V(dst) - V(src) in {0,1} for every allowed edge in the core.
  (B) The zero-charge subgraph zeta/determinant closed form for the g=0 edges.
  (C) A fully explicit two-variable determinant factorization:
        det(I - z M(q)) = (1+z)(1-q z^2) Q7(z,q),
      with Q7 given explicitly, hence an algebraic pressure curve of degree 7.
  (D) Closed-form cumulants at q=1 (theta=0): mean/variance and higher derivatives (up to 4th order) in Q(sqrt(5)).
  (E) A residue constant formula:
        C(q) = lambda(q)^9 / ((lambda(q)+1)(lambda(q)^2-q) * d/dLambda P7(lambda(q),q)).

Outputs (default):
  - artifacts/export/sync_kernel_real_input_40_arity_charge_closed_form.json
  - sections/generated/eq_real_input_40_arity_charge_det_closed.tex
  - sections/generated/eq_real_input_40_arity_charge_det_q_cubic.tex
  - sections/generated/eq_real_input_40_arity_charge_zero_charge_zeta.tex
  - sections/generated/eq_real_input_40_arity_charge_cumulants_closed.tex
  - sections/generated/eq_real_input_40_arity_charge_B_charpoly.tex
  - sections/generated/tab_real_input_40_arity_charge_coboundary_audit.tex
  - sections/generated/tab_real_input_40_arity_charge_density_audit.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_matrix_int,
    build_real_input_states,
)


State = Tuple[str, int, int]  # (sync_state, px, py)


@dataclass(frozen=True)
class EdgeAuditRow:
    src: State
    dst: State
    d: int
    e: int
    chi: int
    V_src: int
    V_dst: int
    g: int


def _adj_list_from_matrix(M: List[List[int]]) -> List[List[int]]:
    n = len(M)
    adj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        row = M[i]
        outs: List[int] = []
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

    essential = [
        cid for cid in range(len(comps)) if not out_to_other[cid] and len(comps[cid]) > 1
    ]
    if len(essential) != 1:
        raise RuntimeError(
            f"expected unique essential SCC, got {[(cid, len(comps[cid])) for cid in essential]}"
        )
    return sorted(comps[essential[0]])


def _submatrix(M: List[List[int]], idx: List[int]) -> List[List[int]]:
    return [[M[i][j] for j in idx] for i in idx]


def _V_certificate(core_states: Sequence[State]) -> Dict[State, int]:
    # V=1 on four explicit essential-core states, else 0.
    V: Dict[State, int] = {st: 0 for st in core_states}
    ones = [
        ("1-12", 1, 1),  # 1 \bar{1} 2
        ("101", 1, 1),
        ("002", 1, 1),
        ("11-1", 0, 0),  # 11 \bar{1}
    ]
    for st in ones:
        if st not in V:
            raise RuntimeError(f"V-certificate state not in essential core: {st}")
        V[st] = 1
    return V


def _h_certificate(core_states: Sequence[State]) -> Dict[State, int]:
    """A {-2,-1,0}-valued vertex potential used for the density bound certificate.

    This is an explicit, finite certificate used to prove that for every essential-core
    edge e:u->v we have:
        w(e) + h(u) - h(v) >= 0,
    where w(e)=1-2*g(e) in {+1,-1} and g(e) is the 0/1 coboundary normal form of chi.
    """
    h: Dict[State, int] = {st: 0 for st in core_states}
    minus2 = [
        ("000", 0, 0),
        ("001", 0, 1),
        ("001", 1, 0),
    ]
    minus1 = [
        ("000", 0, 1),
        ("000", 1, 0),
        ("010", 0, 0),
        ("100", 0, 1),
        ("100", 1, 0),
        ("002", 1, 1),
        ("11-1", 0, 0),
    ]
    for st in minus2:
        if st not in h:
            raise RuntimeError(f"h-certificate state not in essential core: {st}")
        h[st] = -2
    for st in minus1:
        if st not in h:
            raise RuntimeError(f"h-certificate state not in essential core: {st}")
        h[st] = -1
    return h


@dataclass(frozen=True)
class CoboundaryAudit:
    essential_core_size: int
    edges_in_core: int
    edges_g0: int
    edges_g1: int
    g_min: int
    g_max: int
    chi_min: int
    chi_max: int
    V_ones: List[State]


@dataclass(frozen=True)
class DensityAuditRow:
    src: State
    dst: State
    g: int
    w: int
    h_src: int
    h_dst: int
    slack: int


def _build_g_matrices_and_audit(
    *,
    core_states: List[State],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    prog: Progress,
) -> Tuple[List[List[int]], List[List[int]], CoboundaryAudit, List[EdgeAuditRow]]:
    n = len(core_states)
    core_idx = {st: i for i, st in enumerate(core_states)}
    V = _V_certificate(core_states)

    M0 = [[0] * n for _ in range(n)]  # g=0 edges
    M1 = [[0] * n for _ in range(n)]  # g=1 edges
    rows: List[EdgeAuditRow] = []

    edges = 0
    edges_g0 = 0
    edges_g1 = 0
    g_min = 10
    g_max = -10
    chi_min = 10
    chi_max = -10

    for k, (s, px, py) in enumerate(core_states, start=1):
        i = core_idx[(s, px, py)]
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_s, e = kernel_map[(s, d)]
                dst_state = (dst_s, x, y)
                if dst_state not in core_idx:
                    raise RuntimeError(
                        f"edge from core leaves core (unexpected): {(s,px,py)} -> {dst_state}"
                    )
                j = core_idx[dst_state]
                chi = int(e) - (1 if d == 2 else 0)
                V_src = int(V[(s, px, py)])
                V_dst = int(V[dst_state])
                g = int(chi + V_dst - V_src)
                edges += 1
                g_min = min(g_min, g)
                g_max = max(g_max, g)
                chi_min = min(chi_min, chi)
                chi_max = max(chi_max, chi)
                rows.append(
                    EdgeAuditRow(
                        src=(s, px, py),
                        dst=dst_state,
                        d=d,
                        e=int(e),
                        chi=int(chi),
                        V_src=V_src,
                        V_dst=V_dst,
                        g=int(g),
                    )
                )
                if g not in (0, 1):
                    raise RuntimeError(
                        f"coboundary certificate failed: g={g} for edge {(s,px,py)} -> {dst_state} "
                        f"(d={d}, e={e}, chi={chi}, Vsrc={V_src}, Vdst={V_dst})"
                    )
                if g == 0:
                    M0[i][j] += 1
                    edges_g0 += 1
                else:
                    M1[i][j] += 1
                    edges_g1 += 1
        prog.tick(f"core edge audit {k}/{n}")

    V_ones = [st for st in core_states if V[st] == 1]
    audit = CoboundaryAudit(
        essential_core_size=n,
        edges_in_core=edges,
        edges_g0=edges_g0,
        edges_g1=edges_g1,
        g_min=g_min,
        g_max=g_max,
        chi_min=chi_min,
        chi_max=chi_max,
        V_ones=V_ones,
    )
    rows.sort(
        key=lambda r: (
            r.src[1],
            r.src[2],
            r.src[0],
            r.dst[1],
            r.dst[2],
            r.dst[0],
            r.d,
            r.e,
        )
    )
    return M0, M1, audit, rows


def _build_density_audit_rows(
    *, edge_rows: Sequence[EdgeAuditRow], h: Dict[State, int]
) -> List[DensityAuditRow]:
    rows: List[DensityAuditRow] = []
    for r in edge_rows:
        if r.g not in (0, 1):
            raise RuntimeError(f"unexpected g value in audit row: {r.g}")
        w = 1 - 2 * r.g
        hs = int(h[r.src])
        ht = int(h[r.dst])
        slack = int(w + hs - ht)
        if slack < 0:
            raise RuntimeError(
                "density certificate violated: "
                f"src={r.src} dst={r.dst} g={r.g} w={w} h(src)={hs} h(dst)={ht} slack={slack}"
            )
        rows.append(
            DensityAuditRow(
                src=r.src,
                dst=r.dst,
                g=r.g,
                w=int(w),
                h_src=hs,
                h_dst=ht,
                slack=slack,
            )
        )
    rows.sort(
        key=lambda r: (
            r.src[1],
            r.src[2],
            r.src[0],
            r.dst[1],
            r.dst[2],
            r.dst[0],
            r.g,
        )
    )
    return rows


def _Q7(z: sp.Symbol, q: sp.Symbol) -> sp.Expr:
    # Q7(z,q) as in the closed form package.
    return sp.expand(
        1
        - 2 * z
        + (1 - 5 * q) * z**2
        + 6 * q * z**3
        + (-1 - 3 * q + 6 * q**2) * z**4
        + (1 - q - 4 * q**2) * z**5
        + (-3 * q + 4 * q**2) * z**6
        + (q - q**2) * z**7
    )


def _P7(L: sp.Symbol, q: sp.Symbol) -> sp.Expr:
    # P7(L,q) = L^7 Q7(1/L,q)
    z = sp.Symbol("z")
    Q = _Q7(z, q)
    return sp.expand(L**7 * Q.subs(z, 1 / L))


def _delta_closed(z: sp.Symbol, q: sp.Symbol) -> sp.Expr:
    return sp.expand((1 + z) * (1 - q * z**2) * _Q7(z, q))


def _delta_q_cubic_factored(z: sp.Symbol, q: sp.Symbol) -> sp.Expr:
    # A human-auditable q-cubic closed form, used for TeX output.
    return sp.expand(
        (z - 1) * (z + 1) * (z**4 + z - 1)
        - z**2 * (z + 1) * (2 * z**4 + z**3 + 4 * z**2 - 8 * z + 6) * q
        - z**4 * (z + 1) * (z**5 - 3 * z**4 - 7 * z**2 + 10 * z - 11) * q**2
        + z**6 * (z + 1) * (z**3 - 4 * z**2 + 4 * z - 6) * q**3
    )


def _write_tex_det_q_cubic(path: Path) -> None:
    z, q = sp.symbols("z q")
    Delta_closed = _delta_closed(z, q)
    Delta_q_cubic = _delta_q_cubic_factored(z, q)
    if sp.expand(Delta_closed - Delta_q_cubic) != 0:
        raise RuntimeError("Delta(z,q) q-cubic form does not match closed form.")

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append("\\Delta(z,q):=\\det(I-zM(q))")
    lines.append("={}&(z-1)(z+1)(z^4+z-1)\\\\")
    lines.append("&-z^2(z+1)(2 z^4 + z^3 + 4 z^2 - 8 z + 6)\\,q\\\\")
    lines.append("&-z^4(z+1)(z^5 - 3 z^4 - 7 z^2 + 10 z - 11)\\,q^2\\\\")
    lines.append("&+z^6(z+1)(z^3 - 4 z^2 + 4 z - 6)\\,q^3.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _det_poly_z(M: sp.Matrix, z: sp.Symbol) -> sp.Expr:
    return sp.expand((sp.eye(M.rows) - z * M).det())


def _write_tex_det_closed(path: Path) -> None:
    z, q, L = sp.symbols("z q Lambda")
    Q7 = sp.expand(_Q7(z, q))
    P7 = sp.expand(_P7(L, q))

    def poly_in_var_lines(expr: sp.Expr, var: sp.Symbol, deg: int, *, max_line_len: int = 95) -> List[str]:
        poly = sp.Poly(sp.expand(expr), var)
        terms: List[str] = []

        def monomial(k: int) -> str:
            if k == 1:
                return sp.latex(var)
            return sp.latex(var) + f"^{{{k}}}"

        def coeff_times_monomial(coeff: sp.Expr, k: int) -> str:
            if k == 0:
                return sp.latex(coeff)
            m = monomial(k)
            if coeff == 1:
                return m
            if coeff == -1:
                return "-" + m
            ctex = sp.latex(coeff)
            if isinstance(coeff, sp.Add):
                ctex = f"\\left({ctex}\\right)"
            return ctex + "\\," + m

        for k in range(0, deg + 1):
            coeff = sp.simplify(poly.coeff_monomial(var**k))
            if coeff == 0:
                continue
            terms.append(coeff_times_monomial(coeff, k))
        if not terms:
            return ["0"]

        # Greedy packing by character length (constant-first order).
        out: List[str] = []
        cur = terms[0]
        for t in terms[1:]:
            cand = cur + " + " + t
            if len(cand) > max_line_len:
                out.append(cur)
                cur = ("- " + t[1:]) if t.startswith("-") else ("+ " + t)
            else:
                cur = cand
        out.append(cur)
        return [ln.replace("+ -", "- ") for ln in out]

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(
        "\\det(I-zM(q))"
        "=(1+z)(1-qz^2)\\,Q_7(z,q),"
    )
    lines.append("\\\\")
    q7_lines = poly_in_var_lines(Q7, z, 7, max_line_len=90)
    if len(q7_lines) == 1:
        lines.append("Q_7(z,q)&=" + q7_lines[0] + ".")
    else:
        lines.append("Q_7(z,q)&=" + q7_lines[0] + "\\\\")
        for ln in q7_lines[1:-1]:
            lines.append("&" + ln + "\\\\")
        lines.append("&" + q7_lines[-1] + ".")
    lines.append("\\\\[2pt]")
    lines.append(
        "\\det(\\Lambda I-M(q))"
        "=\\Lambda^{10}(\\Lambda+1)(\\Lambda^2-q)\\,P_7(\\Lambda,q),"
    )
    lines.append("\\\\")
    p7_lines = poly_in_var_lines(P7, L, 7, max_line_len=90)
    if len(p7_lines) == 1:
        lines.append("P_7(\\Lambda,q)&=" + p7_lines[0] + ".")
    else:
        lines.append("P_7(\\Lambda,q)&=" + p7_lines[0] + "\\\\")
        for ln in p7_lines[1:-1]:
            lines.append("&" + ln + "\\\\")
        lines.append("&" + p7_lines[-1] + ".")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_zero_charge(path: Path, det0: sp.Expr, kappa: float) -> None:
    z = sp.Symbol("z")
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append("\\det(I-zM_0)&=" + sp.latex(sp.factor(det0)) + ",")
    lines.append("\\\\")
    lines.append("\\zeta_0(z)&=\\det(I-zM_0)^{-1}")
    lines.append(
        "=\\frac{1}{(1-z^2)(1-z-z^4)},"
    )
    lines.append("\\\\")
    lines.append(
        "\\kappa&\\approx "
        + f"{kappa:.12g}"
        + "\\quad\\text{(the Perron root of }\\kappa^4-\\kappa^3-1=0\\text{).}"
    )
    lines.append("\\end{aligned}")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_cumulants(
    path: Path,
    *,
    P1: sp.Expr,
    P2: sp.Expr,
    P3: sp.Expr,
    P4: sp.Expr,
) -> None:
    P1_s = sp.simplify(P1)
    P2_s = sp.simplify(P2)
    P3_s = sp.simplify(P3)
    P4_s = sp.simplify(P4)
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append("\\mathbb{E}[\\chi]&=" + sp.latex(P1_s) + f"\\approx {float(sp.N(P1_s, 20)):.12g},")
    lines.append("\\\\")
    lines.append(
        "\\mathrm{Var}_\\infty(\\chi)&="
        + sp.latex(P2_s)
        + f"\\approx {float(sp.N(P2_s, 20)):.12g},"
    )
    lines.append("\\\\")
    lines.append(
        "P_\\chi^{(3)}(0)&="
        + sp.latex(P3_s)
        + f"\\approx {float(sp.N(P3_s, 20)):.12g},"
    )
    lines.append("\\\\")
    lines.append(
        "P_\\chi^{(4)}(0)&="
        + sp.latex(P4_s)
        + f"\\approx {float(sp.N(P4_s, 20)):.12g}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _tex_sync_state(s: str) -> str:
    # Repository uses "-1" in state strings; paper uses overline notation.
    return s.replace("-1", "\\overline{1}")


def _tex_state(st: State) -> str:
    s, px, py = st
    return f"({_tex_sync_state(s)},{px}{py})"


def _write_tex_coboundary_audit(path: Path, rows: Sequence[EdgeAuditRow]) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    # Avoid hard float placement ([H]) which can overflow page boxes.
    lines.append("\\begin{table}[tbp]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append("\\renewcommand{\\arraystretch}{0.95}")
    lines.append("\\begin{tabular}{@{}llcccccc@{}}")
    lines.append("\\toprule")
    lines.append("$u=(s,m)$ & $v=(s',m')$ & $d$ & $e$ & $\\chi$ & $V(u)$ & $V(v)$ & $g$\\\\")
    lines.append("\\midrule")
    for r in rows:
        u = _tex_state(r.src)
        v = _tex_state(r.dst)
        lines.append(
            f"${u}$ & ${v}$ & ${r.d}$ & ${r.e}$ & ${r.chi}$ & ${r.V_src}$ & ${r.V_dst}$ & ${r.g}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{真实输入 40 状态核（essential 20 状态核心）上，arity-charge 的 $0/1$ 共边界证书逐边核验表（共 "
        + str(len(rows))
        + " 条边）。}"
    )
    lines.append("\\label{tab:real-input-40-arity-charge-coboundary-audit}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_density_audit(path: Path, rows: Sequence[DensityAuditRow]) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    # Avoid hard float placement ([H]) which can overflow page boxes.
    lines.append("\\begin{table}[tbp]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append("\\renewcommand{\\arraystretch}{0.95}")
    lines.append("\\begin{tabular}{@{}llcccccc@{}}")
    lines.append("\\toprule")
    lines.append("$u=(s,m)$ & $v=(s',m')$ & $g$ & $w$ & $h(u)$ & $h(v)$ & $w+h(u)-h(v)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        u = _tex_state(r.src)
        v = _tex_state(r.dst)
        lines.append(
            f"${u}$ & ${v}$ & ${r.g}$ & ${r.w}$ & ${r.h_src}$ & ${r.h_dst}$ & ${r.slack}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{真实输入 40 状态核（essential 20 状态核心）上，arity-charge 密度上界的逐边有限证书核验表（共 "
        + str(len(rows))
        + " 条边）。}"
    )
    lines.append("\\label{tab:real-input-40-arity-charge-density-audit}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_B_charpoly(path: Path, B_charpoly_factored: sp.Expr) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_charge_closed_form.py")
    lines.append("\\[")
    lines.append("\\boxed{\\ ")
    lines.append(
        "\\chi_B(\\Lambda):=\\det(\\Lambda I-B)="
        + sp.latex(B_charpoly_factored)
        + ",\\qquad \\rho(B)=3."
    )
    lines.append("\\ }")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _chi_cumulants_closed_form(*, prog: Progress) -> Tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    # Compute P^{(k)}(0) (k=1..4) for P(theta)=log lambda(e^theta),
    # where lambda(q) is the PF root of P7(L,q)=0.
    theta = sp.Symbol("theta")
    q = sp.exp(theta)
    L = sp.Symbol("L")

    sqrt5 = sp.sqrt(5)
    lam0 = (sp.Integer(3) + sqrt5) / 2  # phi^2

    c1, c2, c3, c4 = sp.symbols("c1 c2 c3 c4")
    lam_series = lam0 + c1 * theta + c2 * theta**2 + c3 * theta**3 + c4 * theta**4

    P7 = _P7(L, sp.Symbol("q"))
    expr = sp.expand(P7.subs({L: lam_series, sp.Symbol("q"): q}))
    ser = sp.series(expr, theta, 0, 5).removeO()
    ser = sp.expand(ser)

    e0 = sp.simplify(ser.coeff(theta, 0))
    if e0 != 0:
        raise RuntimeError("P7(lam0,1) != 0; incorrect base point for series.")

    sol: Dict[sp.Symbol, sp.Expr] = {}
    for k, ck in enumerate([c1, c2, c3, c4], start=1):
        prog.tick(f"solving chi cumulants: c{k}")
        eqk = sp.expand(ser.subs(sol).coeff(theta, k))
        a = sp.diff(eqk, ck)
        if a == 0:
            raise RuntimeError(f"unexpected: theta^{k} equation is not linear in c{k}")
        b = sp.expand(eqk.subs(ck, 0))
        sol[ck] = sp.simplify(-b / a)

    lam_series = sp.expand(lam_series.subs(sol))
    P_series = sp.series(sp.log(lam_series), theta, 0, 5).removeO()
    P1 = sp.simplify(sp.diff(P_series, theta, 1).subs(theta, 0))
    P2 = sp.simplify(sp.diff(P_series, theta, 2).subs(theta, 0))
    P3 = sp.simplify(sp.diff(P_series, theta, 3).subs(theta, 0))
    P4 = sp.simplify(sp.diff(P_series, theta, 4).subs(theta, 0))
    return P1, P2, P3, P4


def main() -> None:
    parser = argparse.ArgumentParser(description="Closed-form package for arity-charge on real-input-40 kernel.")
    parser.add_argument(
        "--no-output",
        action="store_true",
        help="Skip writing JSON and TeX outputs (still runs audits).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40_arity_charge_closed_form.json"),
    )
    parser.add_argument(
        "--tex-det-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_arity_charge_det_closed.tex"),
    )
    parser.add_argument(
        "--tex-det-q-cubic-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_arity_charge_det_q_cubic.tex"),
        help="Write a human-auditable q-cubic expansion of det(I-zM(q)).",
    )
    parser.add_argument(
        "--tex-zero-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_arity_charge_zero_charge_zeta.tex"),
    )
    parser.add_argument(
        "--tex-cumulants-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_arity_charge_cumulants_closed.tex"),
    )
    parser.add_argument(
        "--tex-edge-audit-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_charge_coboundary_audit.tex"),
    )
    parser.add_argument(
        "--tex-density-audit-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_charge_density_audit.tex"),
    )
    parser.add_argument(
        "--tex-B-charpoly-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_arity_charge_B_charpoly.tex"),
    )
    args = parser.parse_args()

    prog = Progress(label="real-input-40-arity-charge", every_seconds=10.0)
    print("[real-input-40-arity-charge] start", flush=True)

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    M_full = build_real_input_matrix_int(states, kernel_map)

    adj = _adj_list_from_matrix(M_full)
    ess_idx_full = _essential_scc(adj)
    core_states = [states[i] for i in ess_idx_full]
    if len(core_states) != 20:
        raise RuntimeError(f"unexpected essential core size: {len(core_states)}")
    prog.tick("essential core extracted")

    M0, M1, audit, edge_rows = _build_g_matrices_and_audit(
        core_states=core_states,
        kernel_map=kernel_map,
        prog=prog,
    )
    prog.tick(
        f"coboundary OK: edges={audit.edges_in_core} g0={audit.edges_g0} g1={audit.edges_g1}"
    )

    # Convert once to SymPy matrices (avoid repeated construction in checks).
    M0_sp = sp.Matrix(M0)
    M1_sp = sp.Matrix(M1)
    I = sp.eye(M0_sp.rows)

    # Density-bound certificate (explicit h, auditable per-edge inequality).
    h_cert = _h_certificate(core_states)
    density_rows = _build_density_audit_rows(edge_rows=edge_rows, h=h_cert)
    min_slack = min(r.slack for r in density_rows) if density_rows else 0
    prog.tick(f"density certificate OK, min slack={min_slack}")

    # Two-step mixing matrix B := M0*M1 + M1*M0 for the large-bias mechanism.
    Lam = sp.Symbol("Lambda")
    B = M0_sp * M1_sp + M1_sp * M0_sp
    B_charpoly = sp.factor(B.charpoly(Lam).as_expr())
    B_charpoly_expected = Lam**13 * (Lam - 1) ** 3 * (Lam - 2) ** 3 * (Lam - 3)
    if sp.simplify(B_charpoly - B_charpoly_expected) != 0:
        raise RuntimeError(f"unexpected B charpoly factorization: {B_charpoly}")
    prog.tick("B charpoly factorization OK (rho(B)=3)")

    # Determinant identities are polynomials in z of degree <= n (n=20).
    # Instead of computing symbolic det(I - z M) (slow), we certify equality by
    # evaluating at enough integer z points (exact integer arithmetic).
    z = sp.Symbol("z")
    z_values = list(range(0, 21))  # 21 points certify degree <= 20

    # Zero-charge subgraph determinant (exact in z only).
    det0_target = sp.expand((1 - z**2) * (1 - z - z**4))
    for zv in z_values:
        det_eval = (I - sp.Integer(zv) * M0_sp).det(method="bareiss")
        rhs_eval = det0_target.subs(z, sp.Integer(zv))
        if det_eval != rhs_eval:
            raise RuntimeError(f"det(I-zM0) mismatch at z={zv}: got={det_eval}, target={rhs_eval}")
    det0_fact = sp.factor(det0_target)
    # Perron root kappa from x^4-x^3-1=0.
    x = sp.Symbol("x")
    kappa_roots = [r for r in sp.nroots(x**4 - x**3 - 1) if abs(sp.im(r)) < 1e-20]
    if not kappa_roots:
        raise RuntimeError("failed to locate real root for kappa")
    kappa = float(max(float(sp.re(r)) for r in kappa_roots))
    prog.tick(f"zero-charge det OK, kappa~{kappa:.6g}")

    # Closed-form determinant identity check at several integer q values.
    # We certify polynomial equality in z by integer evaluation (exact).
    q_sym = sp.Symbol("q")
    Delta_closed = _delta_closed(z, q_sym)
    for idx, qv in enumerate([1, 2, 3, 4, 5], start=1):
        A = M0_sp + int(qv) * M1_sp
        for zv in z_values:
            det_eval = (I - sp.Integer(zv) * A).det(method="bareiss")
            rhs_eval = Delta_closed.subs({q_sym: int(qv), z: sp.Integer(zv)})
            if det_eval != rhs_eval:
                raise RuntimeError(f"Delta(z,q) mismatch at q={qv} z={zv}: got={det_eval}, target={rhs_eval}")
        prog.tick(f"Delta(z,q) exact check {idx}/5 (q={qv})")

    # Closed-form cumulants at theta=0.
    P1, P2, P3, P4 = _chi_cumulants_closed_form(prog=prog)

    # Residue constant sanity check at q=1: C = (47+21*sqrt5)/100.
    sqrt5 = sp.sqrt(5)
    lam0 = (sp.Integer(3) + sqrt5) / 2
    L = sp.Symbol("Lambda")
    q = sp.Symbol("q")
    P7 = _P7(L, q)
    dP7 = sp.diff(P7, L)
    C_expr = sp.simplify(
        (lam0**9) / ((lam0 + 1) * (lam0**2 - 1) * dP7.subs({L: lam0, q: 1}))
    )
    C_target = (sp.Integer(47) + sp.Integer(21) * sqrt5) / sp.Integer(100)
    if sp.simplify(C_expr - C_target) != 0:
        raise RuntimeError("Residue constant check at q=1 failed.")
    prog.tick("residue constant check OK at q=1")

    payload: Dict[str, object] = {
        "coboundary_audit": asdict(audit),
        "coboundary_edges": [
            {
                "src": {"s": r.src[0], "px": r.src[1], "py": r.src[2]},
                "dst": {"s": r.dst[0], "px": r.dst[1], "py": r.dst[2]},
                "d": r.d,
                "e": r.e,
                "chi": r.chi,
                "V_src": r.V_src,
                "V_dst": r.V_dst,
                "g": r.g,
            }
            for r in edge_rows
        ],
        "det_zero_charge_factored": str(det0_fact),
        "kappa_approx": kappa,
        "Q7": str(_Q7(sp.Symbol("z"), sp.Symbol("q"))),
        "P7": str(_P7(sp.Symbol("Lambda"), sp.Symbol("q"))),
        "E_chi_closed": str(sp.simplify(P1)),
        "Var_chi_closed": str(sp.simplify(P2)),
        "P3_chi_closed": str(sp.simplify(P3)),
        "P4_chi_closed": str(sp.simplify(P4)),
        "C_q1_exact": str(C_target),
        "density_min_slack": min_slack,
        "B_charpoly_factored": str(B_charpoly),
    }

    if not args.no_output:
        # JSON
        jout = Path(args.json_out)
        jout.parent.mkdir(parents=True, exist_ok=True)
        jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[real-input-40-arity-charge] wrote {jout}", flush=True)

        # TeX snippets
        _write_tex_det_closed(Path(args.tex_det_out))
        _write_tex_det_q_cubic(Path(args.tex_det_q_cubic_out))
        _write_tex_zero_charge(Path(args.tex_zero_out), det0=det0_fact, kappa=kappa)
        _write_tex_cumulants(Path(args.tex_cumulants_out), P1=P1, P2=P2, P3=P3, P4=P4)
        _write_tex_coboundary_audit(Path(args.tex_edge_audit_out), edge_rows)
        _write_tex_density_audit(Path(args.tex_density_audit_out), density_rows)
        _write_tex_B_charpoly(Path(args.tex_B_charpoly_out), B_charpoly)
        print(f"[real-input-40-arity-charge] wrote {args.tex_det_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_det_q_cubic_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_zero_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_cumulants_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_edge_audit_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_density_audit_out}", flush=True)
        print(f"[real-input-40-arity-charge] wrote {args.tex_B_charpoly_out}", flush=True)

    print(
        f"[real-input-40-arity-charge] E[chi]={float(sp.N(P1, 18)):.12g} Var={float(sp.N(P2, 18)):.12g}",
        flush=True,
    )
    print("[real-input-40-arity-charge] done", flush=True)


if __name__ == "__main__":
    main()

