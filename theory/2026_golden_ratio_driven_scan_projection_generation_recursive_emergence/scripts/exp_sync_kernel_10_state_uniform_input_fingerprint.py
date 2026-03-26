#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Uniform-input statistical fingerprint for the 10-state sync-kernel.

We treat the deterministic transducer (state, input d) -> (next_state, output e)
as a stochastic system by forcing an i.i.d. uniform input:

  P(d=0)=P(d=1)=P(d=2)=1/3.

This induces:
- a 10-state Markov chain on Q (hidden state),
- an output bit process (e_t) as an HMM.

We export:
- exact stationary distribution pi over states (Fractions),
- exact joint distributions P(d,e) and P(e_t,e_{t+1}),
- exact output correlations Corr(e_t,e_{t+k}) for small k,
- a reproducible numerical estimate of the output entropy rate h_out (bits/step),
  computed via the standard filtering recursion for HMMs.

Outputs:
- artifacts/export/sync_kernel_10_state_uniform_input_fingerprint.json
- sections/generated/eq_sync_kernel_10_state_uniform_input_fingerprint.tex
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Edge:
    src: str
    dst: str
    d: int
    e: int


STATES: List[str] = [
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


def build_edges() -> List[Edge]:
    # Must match the transition list in:
    # sections/07_emergent_arithmetic/.../07_emergent_arithmetic_07_subsec_zeckendorf_algorithms_complexity.tex
    edges: List[Edge] = []
    for d in (0, 1, 2):
        edges.append(Edge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(Edge("100", f"00{d}", d, 1))
    edges += [
        Edge("001", "010", 0, 0),
        Edge("001", "100", 1, 0),
        Edge("001", "101", 2, 0),
        Edge("002", "11-1", 0, 0),
        Edge("002", "000", 1, 1),
        Edge("002", "001", 2, 1),
        Edge("010", "100", 0, 0),
        Edge("010", "101", 1, 0),
        Edge("010", "0-12", 2, 1),
        Edge("101", "010", 0, 1),
        Edge("101", "100", 1, 1),
        Edge("101", "101", 2, 1),
        Edge("0-12", "01-1", 0, 0),
        Edge("0-12", "010", 1, 0),
        Edge("0-12", "100", 2, 0),
        Edge("1-12", "01-1", 0, 1),
        Edge("1-12", "010", 1, 1),
        Edge("1-12", "100", 2, 1),
        Edge("01-1", "001", 0, 0),
        Edge("01-1", "002", 1, 0),
        Edge("01-1", "1-12", 2, 0),
        Edge("11-1", "001", 0, 1),
        Edge("11-1", "002", 1, 1),
        Edge("11-1", "1-12", 2, 1),
    ]
    return edges


def _edge_map(edges: Iterable[Edge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    m: Dict[Tuple[str, int], Tuple[str, int]] = {}
    for e in edges:
        key = (e.src, e.d)
        if key in m:
            raise ValueError(f"Non-deterministic edge for {key}: {m[key]} vs {(e.dst, e.e)}")
        m[key] = (e.dst, e.e)
    # Sanity: total deterministic transitions = |Q|*3
    expected = len(STATES) * 3
    if len(m) != expected:
        missing = []
        for s in STATES:
            for d in (0, 1, 2):
                if (s, d) not in m:
                    missing.append((s, d))
        raise ValueError(f"Missing transitions: {missing}")
    return m


def transition_matrix_Q(edges: List[Edge]) -> List[List[Fraction]]:
    idx = {s: i for i, s in enumerate(STATES)}
    nxt = _edge_map(edges)
    n = len(STATES)
    P = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for s in STATES:
        i = idx[s]
        for d in (0, 1, 2):
            t, _ = nxt[(s, d)]
            j = idx[t]
            P[i][j] += Fraction(1, 3)
    return P


def _solve_stationary(P: List[List[Fraction]]) -> List[Fraction]:
    # Solve pi = pi P, sum pi = 1 over rationals.
    # Write (P^T - I) pi^T = 0, replace last equation with sum pi = 1.
    n = len(P)
    A: List[List[Fraction]] = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    b: List[Fraction] = [Fraction(0, 1) for _ in range(n)]

    for i in range(n - 1):
        for j in range(n):
            A[i][j] = P[j][i]  # P^T
        A[i][i] -= Fraction(1, 1)
        b[i] = Fraction(0, 1)

    for j in range(n):
        A[n - 1][j] = Fraction(1, 1)
    b[n - 1] = Fraction(1, 1)

    # Gaussian elimination over Fractions.
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if A[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            b[col], b[pivot] = b[pivot], b[col]
        piv = A[col][col]
        if piv == 0:
            continue
        inv = Fraction(1, 1) / piv
        for j in range(col, n):
            A[col][j] *= inv
        b[col] *= inv
        for row in range(n):
            if row == col:
                continue
            f = A[row][col]
            if f == 0:
                continue
            for j in range(col, n):
                A[row][j] -= f * A[col][j]
            b[row] -= f * b[col]

    pi = b[:]  # should now be the solution
    s = sum(pi)
    if s != 1:
        pi = [x / s for x in pi]
    return pi


def joint_P_d_e(pi: List[Fraction], edges: List[Edge]) -> Dict[Tuple[int, int], Fraction]:
    idx = {s: i for i, s in enumerate(STATES)}
    nxt = _edge_map(edges)
    out: Dict[Tuple[int, int], Fraction] = {(d, e): Fraction(0, 1) for d in (0, 1, 2) for e in (0, 1)}
    for s in STATES:
        ps = pi[idx[s]]
        for d in (0, 1, 2):
            _, e = nxt[(s, d)]
            out[(d, e)] += ps * Fraction(1, 3)
    return out


def joint_P_e_pair(pi: List[Fraction], edges: List[Edge]) -> Dict[Tuple[int, int], Fraction]:
    idx = {s: i for i, s in enumerate(STATES)}
    nxt = _edge_map(edges)
    out: Dict[Tuple[int, int], Fraction] = {(a, b): Fraction(0, 1) for a in (0, 1) for b in (0, 1)}
    for s in STATES:
        ps = pi[idx[s]]
        for d in (0, 1, 2):
            s1, e0 = nxt[(s, d)]
            for d1 in (0, 1, 2):
                _, e1 = nxt[(s1, d1)]
                out[(e0, e1)] += ps * Fraction(1, 3) * Fraction(1, 3)
    return out


def _mat_mul(A: List[List[Fraction]], B: List[List[Fraction]]) -> List[List[Fraction]]:
    n = len(A)
    m = len(B[0])
    k = len(B)
    out = [[Fraction(0, 1) for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for t in range(k):
            if A[i][t] == 0:
                continue
            a = A[i][t]
            rowB = B[t]
            for j in range(m):
                if rowB[j] != 0:
                    out[i][j] += a * rowB[j]
    return out


def _mat_pow(P: List[List[Fraction]], n: int) -> List[List[Fraction]]:
    size = len(P)
    # identity
    out = [[Fraction(1, 1) if i == j else Fraction(0, 1) for j in range(size)] for i in range(size)]
    base = [row[:] for row in P]
    e = n
    while e > 0:
        if e & 1:
            out = _mat_mul(out, base)
        base = _mat_mul(base, base)
        e >>= 1
    return out


def _row_vec_mul(v: List[Fraction], M: List[List[Fraction]]) -> List[Fraction]:
    n = len(v)
    m = len(M[0])
    out = [Fraction(0, 1) for _ in range(m)]
    for i in range(n):
        if v[i] == 0:
            continue
        vi = v[i]
        row = M[i]
        for j in range(m):
            if row[j] != 0:
                out[j] += vi * row[j]
    return out


def _dot(u: List[Fraction], v: List[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), start=Fraction(0, 1))


def corr_lags(pi: List[Fraction], edges: List[Edge], lags: List[int]) -> Dict[int, Fraction]:
    idx = {s: i for i, s in enumerate(STATES)}
    nxt = _edge_map(edges)
    n = len(STATES)

    # P: state transition matrix (uniform input)
    P = transition_matrix_Q(edges)

    # m(s) = E[e | state=s] under uniform input
    m = [Fraction(0, 1) for _ in range(n)]
    for s in STATES:
        i = idx[s]
        cnt = 0
        for d in (0, 1, 2):
            _, e = nxt[(s, d)]
            cnt += int(e)
        m[i] = Fraction(cnt, 3)

    mu = _dot(pi, m)
    var = mu * (Fraction(1, 1) - mu)  # since e is {0,1} at each time
    if var == 0:
        return {k: Fraction(0, 1) for k in lags}

    # A(s, t) = P(next=t, e=1 | current=s) under uniform input
    A = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for s in STATES:
        i = idx[s]
        for d in (0, 1, 2):
            t, e = nxt[(s, d)]
            if e == 1:
                j = idx[t]
                A[i][j] += Fraction(1, 3)

    out: Dict[int, Fraction] = {}
    for k in lags:
        if k <= 0:
            out[k] = Fraction(1, 1)
            continue
        # E[e_t e_{t+k}] = pi * A * P^{k-1} * m
        Pk_1 = _mat_pow(P, k - 1)
        B = _mat_mul(A, Pk_1)
        v = _row_vec_mul(pi, B)
        exy = _dot(v, m)
        cov = exy - mu * mu
        out[k] = cov / var
    return out


def hmm_entropy_rate_bits(
    edges: List[Edge],
    steps: int,
    burn_in: int,
    seed: int,
    prog: Progress,
) -> float:
    # HMM with hidden state in STATES and symbol e in {0,1}.
    #
    # We run the standard filtering recursion (Blackwell entropy-rate estimator)
    # for a long trajectory (10^7+ steps in the main pipeline). The naive dense
    # O(n^2) implementation inside Python loops is too slow even for n=10.
    #
    # Here we exploit determinism + uniform input:
    #   - each hidden state has exactly 3 transitions (d=0,1,2), weight 1/3
    #   - for a fixed observed symbol sym, alpha' can be updated by a sparse
    #     scatter-add over those transitions producing sym.
    #
    # This reduces per-step work to O(#transitions with sym) ~= 15 operations
    # plus a short normalization, and avoids allocating new lists each step.
    idx = {s: i for i, s in enumerate(STATES)}
    nxt = _edge_map(edges)
    n = len(STATES)
    inv3 = 1.0 / 3.0

    # Build sparse transition lists for sym=0/1:
    # out[dst] += alpha[src] * prob, where prob in {1/3,2/3,1}.
    src0: List[int] = []
    dst0: List[int] = []
    prob0: List[float] = []
    src1: List[int] = []
    dst1: List[int] = []
    prob1: List[float] = []
    p1_given_state = [0.0] * n  # P(sym=1 | current hidden state)

    for s in STATES:
        i = idx[s]
        # Aggregate counts by destination to match the dense kernel exactly.
        c0: Dict[int, int] = {}
        c1: Dict[int, int] = {}
        ones = 0
        for d in (0, 1, 2):
            t, e = nxt[(s, d)]
            j = idx[t]
            if e == 0:
                c0[j] = c0.get(j, 0) + 1
            else:
                c1[j] = c1.get(j, 0) + 1
                ones += 1
        p1_given_state[i] = float(ones) * inv3
        for j in sorted(c0.keys()):
            src0.append(i)
            dst0.append(j)
            prob0.append(float(c0[j]) * inv3)
        for j in sorted(c1.keys()):
            src1.append(i)
            dst1.append(j)
            prob1.append(float(c1[j]) * inv3)

    n0 = len(src0)
    n1 = len(src1)

    # Start from stationary distribution to reduce transient.
    P = transition_matrix_Q(edges)
    pi = _solve_stationary(P)
    alpha = [float(x) for x in pi]  # row belief over hidden states
    out = [0.0] * n  # reusable scratch

    rng = random.Random(seed)
    rnd = rng.random
    log2 = math.log2

    total = 0.0
    count = 0
    total_steps = int(steps) + int(burn_in)
    if total_steps <= 0:
        return float("nan")

    # Call Progress.tick only occasionally; it rate-limits actual prints.
    tick_mask = (1 << 16) - 1  # ~ every 65536 steps

    for t in range(total_steps):
        # Predictive symbol probability p1 = P(sym=1 | past) via state-marginal:
        # p1 = sum_i alpha[i] * P(sym=1 | state=i).
        p1 = 0.0
        for i in range(n):
            p1 += alpha[i] * p1_given_state[i]
        # Clamp for numerical safety (should already be in [0,1]).
        if p1 <= 0.0:
            sym = 0
        elif p1 >= 1.0:
            sym = 1
        else:
            sym = 1 if rnd() < p1 else 0

        # Reset scratch.
        for j in range(n):
            out[j] = 0.0

        # Sparse filter update for the observed symbol.
        p_sym = 0.0
        if sym == 1:
            for k in range(n1):
                v = alpha[src1[k]] * prob1[k]
                out[dst1[k]] += v
                p_sym += v
        else:
            for k in range(n0):
                v = alpha[src0[k]] * prob0[k]
                out[dst0[k]] += v
                p_sym += v

        if not (p_sym > 0.0):
            # Should not happen in this primitive HMM.
            return float("nan")

        inv = 1.0 / p_sym
        for j in range(n):
            alpha[j] = out[j] * inv

        if t >= burn_in:
            total += -log2(p_sym)
            count += 1

        if (t & tick_mask) == 0:
            prog.tick(f"hmm entropy t={t}/{total_steps}")

    return total / float(count) if count > 0 else float("nan")


def _tex_state_name(s: str) -> str:
    # Convert internal names (0-12, 01-1, ...) to LaTeX state names.
    if "-" not in s:
        return s
    # Only patterns used in this kernel.
    if s == "0-12":
        return r"0\overline{1}2"
    if s == "1-12":
        return r"1\overline{1}2"
    if s == "01-1":
        return r"01\overline{1}"
    if s == "11-1":
        return r"11\overline{1}"
    return s.replace("-", r"\overline{1}")


def _tex_frac(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return r"\frac{" + str(x.numerator) + "}{" + str(x.denominator) + "}"


def write_tex(pi: List[Fraction], p_de: Dict[Tuple[int, int], Fraction], p_ee: Dict[Tuple[int, int], Fraction], corrs: Dict[int, Fraction], h_out: float) -> str:
    idx = {s: i for i, s in enumerate(STATES)}

    # Order for display: match paper's state set ordering in this subsection.
    disp_states = ["000", "001", "002", "010", "100", "101", "0-12", "1-12", "01-1", "11-1"]

    lines: List[str] = []
    lines.append(r"% Auto-generated by scripts/exp_sync_kernel_10_state_uniform_input_fingerprint.py")
    lines.append(r"\begin{proposition}[10 状态同步核在均匀输入下的精确稳态分布（有理数指纹）]\label{prop:sync10-uniform-stationary}")
    lines.append(r"在输入 $d_t$ 独立同分布且 $\mathbb P(d_t=0)=\mathbb P(d_t=1)=\mathbb P(d_t=2)=\frac13$ 时，")
    lines.append(r"同步核诱导一个 10 状态马尔可夫链，其稳态分布 $\pi$ 在状态集")
    lines.append(r"$Q=\{000,001,002,010,100,101,0\overline{1}2,1\overline{1}2,01\overline{1},11\overline{1}\}$ 上给出为：")
    lines.append(r"$$")
    # two lines layout
    a = disp_states[:6]
    b = disp_states[6:]
    lines.append(r"\pi(000)=" + _tex_frac(pi[idx["000"]]) + r",\ "
                 + r"\pi(001)=" + _tex_frac(pi[idx["001"]]) + r",\ "
                 + r"\pi(002)=" + _tex_frac(pi[idx["002"]]) + r",\ "
                 + r"\pi(010)=" + _tex_frac(pi[idx["010"]]) + r",\ "
                 + r"\pi(100)=" + _tex_frac(pi[idx["100"]]) + r",\ "
                 + r"\pi(101)=" + _tex_frac(pi[idx["101"]]) + r".")
    lines.append(r"$$")
    lines.append(r"$$")
    lines.append(r"\pi(0\overline{1}2)=" + _tex_frac(pi[idx["0-12"]]) + r",\ "
                 + r"\pi(1\overline{1}2)=" + _tex_frac(pi[idx["1-12"]]) + r",\ "
                 + r"\pi(01\overline{1})=" + _tex_frac(pi[idx["01-1"]]) + r",\ "
                 + r"\pi(11\overline{1})=" + _tex_frac(pi[idx["11-1"]]) + r".")
    lines.append(r"$$")
    lines.append(r"\end{proposition}")
    lines.append("")

    lines.append(r"\begin{proposition}[输出无偏与输入--输出耦合（精确联合分布）]\label{prop:sync10-uniform-de}")
    lines.append(r"在上述稳态下，联合分布 $\mathbb P(d,e)$ 满足：")
    lines.append(r"$$")
    lines.append(r"\mathbb P(d=0,e=0)=" + _tex_frac(p_de[(0, 0)]) + r",\quad"
                 + r"\mathbb P(d=0,e=1)=" + _tex_frac(p_de[(0, 1)]) + r",")
    lines.append(r"$$")
    lines.append(r"$$")
    lines.append(r"\mathbb P(d=1,e=0)=" + _tex_frac(p_de[(1, 0)]) + r",\quad"
                 + r"\mathbb P(d=1,e=1)=" + _tex_frac(p_de[(1, 1)]) + r",")
    lines.append(r"$$")
    lines.append(r"$$")
    lines.append(r"\mathbb P(d=2,e=0)=" + _tex_frac(p_de[(2, 0)]) + r",\quad"
                 + r"\mathbb P(d=2,e=1)=" + _tex_frac(p_de[(2, 1)]) + r".")
    lines.append(r"$$")
    # Consequences
    pe1 = p_de[(0, 1)] + p_de[(1, 1)] + p_de[(2, 1)]
    lines.append(r"特别地输出严格无偏：")
    lines.append(r"$$")
    lines.append(r"\mathbb P(e=1)=" + _tex_frac(pe1) + r".")
    lines.append(r"$$")
    lines.append(r"并且条件偏置为：")
    lines.append(r"$$")
    lines.append(r"\mathbb P(e=1\mid d=0)=" + _tex_frac(p_de[(0, 1)] / Fraction(1, 3)) + r",\quad"
                 + r"\mathbb P(e=1\mid d=1)=" + _tex_frac(p_de[(1, 1)] / Fraction(1, 3)) + r",\quad"
                 + r"\mathbb P(e=1\mid d=2)=" + _tex_frac(p_de[(2, 1)] / Fraction(1, 3)) + r".")
    lines.append(r"$$")
    lines.append(r"\end{proposition}")
    lines.append("")

    lines.append(r"\begin{proposition}[输出反持续：两步联合分布与短程相关（可审计有理数）]\label{prop:sync10-uniform-output-corr}")
    lines.append(r"在稳态下连续两位输出满足：")
    lines.append(r"$$")
    lines.append(r"\mathbb P(e_te_{t+1}=00)=" + _tex_frac(p_ee[(0, 0)]) + r",\quad"
                 + r"\mathbb P(11)=" + _tex_frac(p_ee[(1, 1)]) + r",\quad"
                 + r"\mathbb P(01)=" + _tex_frac(p_ee[(0, 1)]) + r",\quad"
                 + r"\mathbb P(10)=" + _tex_frac(p_ee[(1, 0)]) + r".")
    lines.append(r"$$")
    p_flip = p_ee[(0, 1)] + p_ee[(1, 0)]
    # Corr at lag 1..4
    lines.append(r"因此翻转概率")
    lines.append(r"$$")
    lines.append(r"\mathbb P(e_{t+1}\neq e_t)=" + _tex_frac(p_flip) + r".")
    lines.append(r"$$")
    lines.append(r"并且相关系数（$\mathrm{Corr}$）在小滞后处为：")
    lines.append(r"$$")
    lines.append(
        r"\mathrm{Corr}(e_t,e_{t+1})=" + _tex_frac(corrs[1]) + r",\quad"
        + r"\mathrm{Corr}(e_t,e_{t+2})=" + _tex_frac(corrs[2]) + r",\quad"
        + r"\mathrm{Corr}(e_t,e_{t+3})=" + _tex_frac(corrs[3]) + r",\quad"
        + r"\mathrm{Corr}(e_t,e_{t+4})=" + _tex_frac(corrs[4]) + r"."
    )
    lines.append(r"$$")
    lines.append(r"\end{proposition}")
    lines.append("")

    lines.append(r"\begin{remark}[输出熵率（可复现数值常数）]\label{rem:sync10-uniform-entropy-rate}")
    lines.append(r"把 10 状态同步核视为隐藏马尔可夫模型（隐藏态为 $Q$，观测为 $e_t\in\{0,1\}$），")
    lines.append(r"对输出序列的标准前向滤波递推可估计输出熵率（以 $\log_2$ 计）")
    lines.append(r"$$")
    lines.append(r"h_{\mathrm{out}}\approx " + f"{h_out:.6f}" + r"\ \mathrm{bits/step}.")
    lines.append(r"$$")
    lines.append(r"该值由脚本 \texttt{scripts/exp\_sync\_kernel\_10\_state\_uniform\_input\_fingerprint.py} 一键复现。")
    lines.append(r"\end{remark}")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Uniform-input statistical fingerprint for sync-kernel (10-state)")
    parser.add_argument("--steps", type=int, default=400000, help="Steps for entropy-rate estimation (after burn-in)")
    parser.add_argument("--burn-in", type=int, default=20000, help="Burn-in steps for entropy-rate estimation")
    parser.add_argument("--seed", type=int, default=7, help="RNG seed for entropy-rate estimation")
    parser.add_argument(
        "--output-json",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_10_state_uniform_input_fingerprint.json)",
    )
    parser.add_argument(
        "--output-tex",
        type=str,
        default="",
        help="Output TeX path (default: sections/generated/eq_sync_kernel_10_state_uniform_input_fingerprint.tex)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync10-uniform-fingerprint", every_seconds=20.0)
    edges = build_edges()
    P = transition_matrix_Q(edges)
    pi = _solve_stationary(P)

    p_de = joint_P_d_e(pi, edges)
    p_ee = joint_P_e_pair(pi, edges)
    corrs = corr_lags(pi, edges, lags=[1, 2, 3, 4])
    h_out = hmm_entropy_rate_bits(edges, steps=int(args.steps), burn_in=int(args.burn_in), seed=int(args.seed), prog=prog)

    # Export JSON (exact rationals serialized as "p/q").
    def frac_str(x: Fraction) -> str:
        return f"{x.numerator}/{x.denominator}"

    json_out = {
        "states": STATES,
        "pi": {s: frac_str(pi[i]) for i, s in enumerate(STATES)},
        "P_d_e": {f"{d},{e}": frac_str(p_de[(d, e)]) for d in (0, 1, 2) for e in (0, 1)},
        "P_e_pair": {f"{a}{b}": frac_str(p_ee[(a, b)]) for a in (0, 1) for b in (0, 1)},
        "corr": {str(k): frac_str(v) for k, v in corrs.items()},
        "h_out_bits_per_step_est": float(h_out),
        "entropy_rate_params": {"steps": int(args.steps), "burn_in": int(args.burn_in), "seed": int(args.seed)},
    }

    out_json = Path(args.output_json) if args.output_json else (export_dir() / "sync_kernel_10_state_uniform_input_fingerprint.json")
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(json_out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex = write_tex(pi=pi, p_de=p_de, p_ee=p_ee, corrs=corrs, h_out=h_out)
    out_tex = Path(args.output_tex) if args.output_tex else (generated_dir() / "eq_sync_kernel_10_state_uniform_input_fingerprint.tex")
    out_tex.parent.mkdir(parents=True, exist_ok=True)
    out_tex.write_text(tex, encoding="utf-8")

    # Quick deterministic self-checks against the expected rational fingerprint.
    expected_pi = {
        "000": Fraction(7, 48),
        "001": Fraction(1, 6),
        "002": Fraction(1, 8),
        "010": Fraction(1, 8),
        "100": Fraction(1, 6),
        "101": Fraction(7, 48),
        "0-12": Fraction(1, 24),
        "1-12": Fraction(1, 48),
        "01-1": Fraction(1, 48),
        "11-1": Fraction(1, 24),
    }
    for s, v in expected_pi.items():
        i = STATES.index(s)
        if pi[i] != v:
            raise SystemExit(f"pi mismatch at {s}: got {pi[i]}, expected {v}")

    expected_p_de = {
        (0, 0): Fraction(5, 24),
        (0, 1): Fraction(1, 8),
        (1, 0): Fraction(1, 6),
        (1, 1): Fraction(1, 6),
        (2, 0): Fraction(1, 8),
        (2, 1): Fraction(5, 24),
    }
    for k, v in expected_p_de.items():
        if p_de[k] != v:
            raise SystemExit(f"P(d,e) mismatch at {k}: got {p_de[k]}, expected {v}")

    expected_p_ee = {
        (0, 0): Fraction(79, 432),
        (1, 1): Fraction(79, 432),
        (0, 1): Fraction(137, 432),
        (1, 0): Fraction(137, 432),
    }
    for k, v in expected_p_ee.items():
        if p_ee[k] != v:
            raise SystemExit(f"P(e_t,e_t+1) mismatch at {k}: got {p_ee[k]}, expected {v}")

    expected_corr = {
        1: Fraction(-29, 108),
        2: Fraction(-1, 81),
        3: Fraction(-1, 972),
        4: Fraction(-5, 1458),
    }
    for k, v in expected_corr.items():
        if corrs[k] != v:
            raise SystemExit(f"Corr lag {k} mismatch: got {corrs[k]}, expected {v}")

    print(f"[sync10-uniform-fingerprint] wrote {out_json} and {out_tex}", flush=True)
    print(f"[sync10-uniform-fingerprint] h_out ~= {h_out:.6f} bits/step", flush=True)


if __name__ == "__main__":
    main()

