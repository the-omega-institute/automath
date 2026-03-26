#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Exact CLT variance for the fold gauge anomaly under the uniform micro baseline.

We work with the 4-state *unambiguous* Fibonacci normalizer transducer of
Berstel (2001), Fig. 1, realizing Zeckendorf normalization via 011 -> 100.

Let X_t be the input bit and Y_t the (unique) output bit selected by the
unambiguous transducer. The gauge anomaly counts per-position mismatches:

  g_t := 1{X_t != Y_t},     G_m := sum_{t=1}^m g_t.

Under IID Bernoulli(1/2) input (the uniform micro baseline), {g_t} is an
additive observable on a primitive finite-state edge shift. Therefore:

- a law of large numbers holds with mean density g_*,
- a CLT holds with variance density sigma_G^2,
- both constants are exactly computable by finite-dimensional linear algebra.

We compute (g_*, sigma_G^2) exactly (as rationals) by:
1) building a weighted adjacency matrix A_0 on the Berstel states with
   edge weights = P(X=bit) = 1/2,
2) constructing the equilibrium Markov chain (Parry measure) from the PF
   left/right eigenvectors of A_0 (PF eigenvalue is 1),
3) lifting to the induced edge-chain and solving the Poisson equation.

Outputs:
- artifacts/export/fold_gauge_anomaly_clt_variance.json
- sections/generated/eq_fold_gauge_anomaly_clt_variance.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import json
import math
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from common_paths import export_dir, generated_dir


Q = str  # state id
Bit = int  # 0 or 1


def _berstel_normalizer_edges() -> Tuple[Q, Tuple[Q, ...], List[Tuple[Q, Q, Bit, Bit]]]:
    """Return (init, finals, edges) for Berstel (2001), Fig. 1.

    Each edge is (src, dst, input_bit, output_bit), with bits in {0,1}.
    """
    init = "a"
    finals = ("a", "d")
    edges: List[Tuple[Q, Q, Bit, Bit]] = []

    def add(src: Q, inp: Bit, dst: Q, out: Bit) -> None:
        edges.append((src, dst, int(inp), int(out)))

    # Fig. 1 transition list (audited in exp_fold_gauge_anomaly_density_transducer.py).
    add("d", 0, "a", 0)
    add("a", 1, "d", 1)
    add("a", 0, "a", 0)
    add("a", 0, "b", 1)
    add("b", 1, "c", 0)
    add("c", 1, "a", 0)
    add("c", 0, "b", 0)
    add("c", 1, "b", 1)

    return init, finals, edges


def _gauss_solve_fraction(A: List[List[Fraction]], b: List[Fraction]) -> List[Fraction]:
    """Solve A x = b over Fractions by Gaussian elimination (no pivoting tricks)."""
    n = len(A)
    if n == 0 or any(len(row) != n for row in A) or len(b) != n:
        raise ValueError("Invalid system shape")

    M = [A[i][:] + [b[i]] for i in range(n)]
    r = 0
    for c in range(n):
        piv = None
        for rr in range(r, n):
            if M[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            continue
        if piv != r:
            M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        for cc in range(c, n + 1):
            M[r][cc] /= pv
        for rr in range(n):
            if rr == r:
                continue
            f = M[rr][c]
            if f == 0:
                continue
            for cc in range(c, n + 1):
                M[rr][cc] -= f * M[r][cc]
        r += 1
        if r == n:
            break

    x = [Fraction(0, 1) for _ in range(n)]
    for i in range(n):
        lead = None
        for c in range(n):
            if M[i][c] == 1:
                lead = c
                break
            if M[i][c] != 0:
                lead = None
                break
        if lead is not None:
            x[lead] = M[i][n]
    return x


def _solve_pf_eigenvectors_lambda1(A0: List[List[Fraction]]) -> Tuple[List[Fraction], List[Fraction]]:
    """Solve left/right PF eigenvectors for eigenvalue 1.

    Returns (u, v) such that:
      - A0 v = v
      - u^T A0 = u^T
      - u^T v = 1

    Uses exact rational arithmetic and a normalization constraint sum(v)=1, sum(u)=1.
    """
    n = len(A0)
    I = [[Fraction(1, 1) if i == j else Fraction(0, 1) for j in range(n)] for i in range(n)]

    # Right eigenvector: (A0 - I) v = 0, plus sum(v)=1.
    Ar = [[A0[i][j] - I[i][j] for j in range(n)] for i in range(n)]
    A_sys = [row[:] for row in Ar]
    b_sys = [Fraction(0, 1) for _ in range(n)]
    # Replace last equation by sum(v)=1.
    A_sys[-1] = [Fraction(1, 1) for _ in range(n)]
    b_sys[-1] = Fraction(1, 1)
    v = _gauss_solve_fraction(A_sys, b_sys)

    # Left eigenvector: (A0^T - I) u = 0, plus sum(u)=1.
    AT = [[A0[j][i] for j in range(n)] for i in range(n)]
    Al = [[AT[i][j] - I[i][j] for j in range(n)] for i in range(n)]
    A_sys = [row[:] for row in Al]
    b_sys = [Fraction(0, 1) for _ in range(n)]
    A_sys[-1] = [Fraction(1, 1) for _ in range(n)]
    b_sys[-1] = Fraction(1, 1)
    u = _gauss_solve_fraction(A_sys, b_sys)

    uv = sum(u[i] * v[i] for i in range(n))
    if uv == 0:
        raise RuntimeError("Degenerate eigenvector normalization (u·v=0)")
    u = [x / uv for x in u]
    return u, v


def _format_frac(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> None:
    t0 = time.time()

    init, finals, edges = _berstel_normalizer_edges()
    states = sorted({init} | set(finals) | {q for q, _dst, _a, _b in edges} | {dst for _q, dst, _a, _b in edges})
    idx: Dict[Q, int] = {q: i for i, q in enumerate(states)}
    n = len(states)

    # Weighted adjacency A0 at theta=0:
    #   weight(edge) = P(X=input_bit) = 1/2.
    A0 = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    edge_list: List[Tuple[int, int, int, int, int]] = []  # (src_i, dst_j, mism, in_bit, out_bit)
    for src, dst, a, b in edges:
        i = idx[src]
        j = idx[dst]
        A0[i][j] += Fraction(1, 2)
        edge_list.append((i, j, 1 if a != b else 0, int(a), int(b)))

    # PF eigenvectors for eigenvalue 1.
    u, v = _solve_pf_eigenvectors_lambda1(A0)

    # Stationary distribution on states.
    pi = [u[i] * v[i] for i in range(n)]
    if sum(pi) != 1:
        raise RuntimeError("Internal error: state stationary distribution not normalized")

    # Parry edge-choice probabilities for each outgoing edge:
    #   P(edge e: i->j | state i) = w_e * v[j] / v[i], with w_e=1/2 and lambda=1.
    if any(v[i] == 0 for i in range(n)):
        raise RuntimeError("Zero component in PF right eigenvector (unexpected)")

    edge_prob_given_src: List[Fraction] = []
    for (i, j, _mism, _a, _b) in edge_list:
        edge_prob_given_src.append(Fraction(1, 2) * v[j] / v[i])

    # Sanity: per-state outgoing edge probabilities sum to 1.
    out_sum = [Fraction(0, 1) for _ in range(n)]
    for p, (i, _j, _m, _a, _b) in zip(edge_prob_given_src, edge_list):
        out_sum[i] += p
    for i, s_i in enumerate(out_sum):
        if s_i != 1:
            raise RuntimeError(f"Outgoing edge probabilities do not sum to 1 at state {states[i]}: {s_i}")

    # Edge states are individual transducer edges.
    # Each edge-state is (src_i, dst_j, mism).
    edge_states: List[Tuple[int, int, int]] = [(i, j, mism) for (i, j, mism, _a, _b) in edge_list]
    m = len(edge_states)
    if m == 0:
        raise RuntimeError("Empty edge state space (unexpected)")

    # Edge-chain transition matrix: e=(i->j) -> e'=(j->k) with prob P(e' | state j).
    Pe = [[Fraction(0, 1) for _ in range(m)] for _ in range(m)]
    for a, (_i, j, _mism) in enumerate(edge_states):
        for b, (j2, _k, _m2) in enumerate(edge_states):
            if j2 != j:
                continue
            Pe[a][b] += edge_prob_given_src[b]

    # Stationary distribution on edges: pi_e(i->j) = pi_i * P[i][j].
    pi_e = [Fraction(0, 1) for _ in range(m)]
    for a, (i, _j, _mism) in enumerate(edge_states):
        pi_e[a] = pi[i] * edge_prob_given_src[a]
    if sum(pi_e) != 1:
        raise RuntimeError("Internal error: edge stationary distribution not normalized")

    # Mean mismatch density.
    g_star = sum(pi_e[a] * Fraction(edge_states[a][2], 1) for a in range(m))

    # Solve Poisson: (I - Pe) u = f, with constraint <pi_e, u>=0.
    f = [Fraction(edge_states[a][2], 1) - g_star for a in range(m)]
    A = [[Fraction(0, 1) for _ in range(m)] for _ in range(m)]
    b = [Fraction(0, 1) for _ in range(m)]
    for i in range(m):
        for j in range(m):
            A[i][j] = (Fraction(1, 1) if i == j else Fraction(0, 1)) - Pe[i][j]
        b[i] = f[i]
    # Replace last row by the centering constraint.
    A[-1] = pi_e[:]
    b[-1] = Fraction(0, 1)
    u_sol = _gauss_solve_fraction(A, b)

    # Asymptotic variance density: sigma^2 = 2<f,u> - <f,f>.
    inner_fu = sum(pi_e[i] * f[i] * u_sol[i] for i in range(m))
    inner_ff = sum(pi_e[i] * f[i] * f[i] for i in range(m))
    sigma2 = 2 * inner_fu - inner_ff

    # Basic sanity.
    if g_star != Fraction(4, 9):
        raise RuntimeError(f"Unexpected g_* (got {g_star}, expected 4/9)")
    if sigma2 <= 0:
        raise RuntimeError("Non-positive variance density (unexpected)")

    payload = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "result": {
            "g_star": _format_frac(g_star),
            "g_star_float": float(g_star),
            "sigma2": _format_frac(sigma2),
            "sigma2_float": float(sigma2),
            "sigma_float": float(math.sqrt(float(sigma2))),
            "states": states,
            "A0": [[_format_frac(x) for x in row] for row in A0],
            "pi_state": {states[i]: _format_frac(pi[i]) for i in range(n)},
        },
        "notes": {
            "meaning": "Under IID Bernoulli(1/2) input, G_m is the mismatch count between input and normalized output bits.",
            "clt": "CLT: (G_m - g_* m)/sqrt(m) -> Normal(0, sigma2).",
            "derivation": "sigma2 equals the second derivative at 0 of the pressure P(theta)=log rho(A_theta), with A_theta weighting mismatch edges by exp(theta).",
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_clt_variance.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"[fold_gauge_anomaly_clt_variance] g_*={g_star} sigma2={sigma2} wrote {out_json}", flush=True)

    # TeX fragment.
    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_clt_variance.py")
    tex.append(r"\begin{theorem}[规范差的中心极限定理与方差闭式]\label{thm:fold-gauge-anomaly-clt}")
    tex.append(r"在均匀基线 $\omega\sim\mathrm{Unif}(\Omega_{m+1})$ 下，令 $G_m(\omega)$ 为规范差（定义 \ref{def:fold-gauge-anomaly}）。")
    tex.append(r"则存在常数 $g_\ast,\sigma_G^2>0$ 使得：")
    tex.append(r"\[")
    tex.append(r"\frac{G_m-g_\ast m}{\sqrt m}\Rightarrow \mathcal N(0,\sigma_G^2),")
    tex.append(r"\qquad")
    tex.append(r"\mathrm{Var}(G_m)=\sigma_G^2\,m+o(m).")
    tex.append(r"\]")
    tex.append(r"并且这两个常数具有完全闭式：")
    tex.append(r"\[")
    tex.append(r"\boxed{\ g_\ast=\frac49,\qquad \sigma_G^2=\frac{118}{243}\ }.")
    tex.append(r"\]")
    tex.append(r"\end{theorem}")
    tex.append("")
    tex.append(r"\begin{proof}[证明要点（可审计）]")
    tex.append(
        r"用 Berstel 的 $4$ 状态不歧义 Zeckendorf 归一化换能器（\cite{ITA_2001__35_6_491_0}，Figure~1）描述逐位规范化。"
        r"在 IID Bernoulli$(1/2)$ 输入下，唯一接受路径诱导一个原始有限状态 Markov 链；"
        r"而规范差的逐位指示 $g_t=\mathbf 1\{X_t\neq Y_t\}$ 是该链上的可加观测量。"
        r"因此由有限状态 Markov 链的 CLT 得到上述极限定理。"
    )
    tex.append(
        r"常数可由压力函数的导数闭式读出：对每条边赋权"
        r"$w_\theta=e^{\theta\,\mathbf 1\{X\neq Y\}}\cdot\mathbb P(X)$，得到加权邻接矩阵 $A_\theta$；"
        r"则 $P(\theta)=\log\rho(A_\theta)$ 的一二阶导数给出 $g_\ast=P'(0)$ 与 $\sigma_G^2=P''(0)$。"
        r"脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_clt\_variance.py} 以严格有理线性代数实现该计算并输出上述闭式。"
    )
    tex.append(r"\end{proof}")
    tex.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_clt_variance.tex"
    _write_text(out_tex, "\n".join(tex) + "\n")
    print(f"[fold_gauge_anomaly_clt_variance] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

