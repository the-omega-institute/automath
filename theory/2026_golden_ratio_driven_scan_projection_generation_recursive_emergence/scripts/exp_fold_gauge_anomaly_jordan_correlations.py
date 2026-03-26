#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Jordan fingerprint + full autocovariance closed forms for the fold gauge anomaly.

English-only by repository convention.

Context (paper):
- Proposition prop:fold-gauge-anomaly-pressure defines A_theta and shows
  P_G(theta)=log rho(A_theta) for the per-position mismatch observable
    g_t := 1{X_t != Y_t}.
- At theta=0 the Perron-Frobenius eigenvectors of A_0 define the Parry
  (equilibrium) Markov kernel P on the 4 transducer states.

This script computes, exactly:
1) the Parry-normalized state kernel P and its stationary distribution pi,
2) the spectrum of P and the (size-2) Jordan block at eigenvalue -1/2,
3) the *entire* autocovariance sequence Cov(g_t, g_{t+k}) in closed form,
4) the finite-length variance Var(S_m) for S_m = sum_{t=1}^m g_t, under
   the stationary (Parry) initial condition,
5) a TeX fragment with theorems that can be directly included in the paper.

Outputs:
- artifacts/export/fold_gauge_anomaly_jordan_correlations.json
- sections/generated/eq_fold_gauge_anomaly_jordan_correlations.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _gcd_list(xs: List[int]) -> int:
    g = 0
    for x in xs:
        g = math.gcd(g, abs(int(x)))
    return g


def _as_integer_vector(v: sp.Matrix) -> List[int]:
    """Scale a sympy rational nullspace vector to a primitive integer vector."""
    if v.cols != 1:
        raise ValueError("Expected a column vector")
    entries = [sp.Rational(e) for e in list(v)]
    denoms = [int(e.q) for e in entries]
    lcm = int(sp.ilcm(*denoms)) if denoms else 1
    ints = [int(e * lcm) for e in entries]
    g = _gcd_list(ints)
    if g == 0:
        raise ValueError("Zero vector (unexpected)")
    ints = [x // g for x in ints]
    # Fix sign: make the first nonzero entry positive.
    for x in ints:
        if x != 0:
            if x < 0:
                ints = [-y for y in ints]
            break
    return ints


@dataclass(frozen=True)
class JordanInfo:
    eigenvals: Dict[str, int]
    charpoly_latex: str
    neg_half_alg_mult: int
    neg_half_geom_mult: int
    neg_half_geom_mult_sq: int


def _format_eigenvals(ev: Dict[sp.Expr, int]) -> Dict[str, int]:
    out: Dict[str, int] = {}
    for k, v in ev.items():
        out[str(sp.simplify(k))] = int(v)
    return dict(sorted(out.items(), key=lambda kv: kv[0]))


def main() -> None:
    t0 = time.time()

    # Berstel 4-state unambiguous Fibonacci normalizer (state order: a,b,c,d).
    # A_theta = (1/2) * [[1, e^theta, 0, 1], [0,0,e^theta,0], [e^theta,2,0,0], [1,0,0,0]].
    A0 = sp.Rational(1, 2) * sp.Matrix(
        [
            [1, 1, 0, 1],
            [0, 0, 1, 0],
            [1, 2, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    I4 = sp.eye(4)

    # PF eigenvectors at eigenvalue rho(A0)=1 (exact).
    r_ns = (A0 - I4).nullspace()
    l_ns = (A0.T - I4).nullspace()
    if len(r_ns) != 1 or len(l_ns) != 1:
        raise RuntimeError("Unexpected PF eigenspace dimension (expected 1)")
    r_int = _as_integer_vector(r_ns[0])
    l_int = _as_integer_vector(l_ns[0])

    # For documentation consistency (paper draft), we expect:
    #   r=(2,1,2,1)^T, l=(2,2,1,1)^T (up to scaling).
    if r_int != [2, 1, 2, 1] or l_int != [2, 2, 1, 1]:
        raise RuntimeError(f"Unexpected integer PF eigenvectors: r={r_int} l={l_int}")
    r = sp.Matrix(r_int)  # column
    ell = sp.Matrix(l_int)  # column

    lr = int((ell.T * r)[0])
    if lr <= 0:
        raise RuntimeError("Non-positive <ell,r> (unexpected)")

    # Parry normalization (rho=1): P_ij = A0_ij * r_j / r_i.
    P = sp.zeros(4, 4)
    for i in range(4):
        for j in range(4):
            if A0[i, j] != 0:
                P[i, j] = sp.simplify(A0[i, j] * r[j] / r[i])

    # Stationary distribution on states: pi_i = ell_i r_i / <ell,r>.
    pi = sp.Matrix([sp.simplify(ell[i] * r[i] / sp.Integer(lr)) for i in range(4)])  # column
    if sp.simplify(sum(pi) - 1) != 0:
        raise RuntimeError("pi does not sum to 1 (unexpected)")

    # Jordan fingerprint.
    lam = sp.Symbol("lambda")
    charpoly = sp.factor(P.charpoly(lam).as_expr())
    ev = P.eigenvals()

    neg = sp.Rational(-1, 2)
    neg_alg = int(ev.get(neg, 0))
    neg_geom = len((P - neg * I4).nullspace())
    neg_geom_sq = len(((P - neg * I4) ** 2).nullspace())

    jordan = JordanInfo(
        eigenvals=_format_eigenvals(ev),
        charpoly_latex=sp.latex(charpoly),
        neg_half_alg_mult=neg_alg,
        neg_half_geom_mult=int(neg_geom),
        neg_half_geom_mult_sq=int(neg_geom_sq),
    )

    # Mismatch observable g(i->j): supported exactly on the "e^theta-edges" in A_theta,
    # i.e. (a->b), (b->c), (c->a) in the (a,b,c,d) order.
    mismatch_edges: List[Tuple[int, int]] = [(0, 1), (1, 2), (2, 0)]
    B = sp.zeros(4, 4)
    for i, j in mismatch_edges:
        B[i, j] = P[i, j]

    ones = sp.Matrix([1, 1, 1, 1])
    Eg = sp.simplify((pi.T * B * ones)[0])  # E[g_t]
    Var_g = sp.simplify(Eg - Eg**2)  # g is {0,1}-valued

    def _Eg0gk(k: int) -> sp.Expr:
        if k < 0:
            raise ValueError("k must be nonnegative")
        if k == 0:
            return Eg  # E[g^2]=E[g]
        return sp.simplify((pi.T * B * (P ** (k - 1)) * B * ones)[0])

    def _Cov(k: int) -> sp.Expr:
        if k < 0:
            raise ValueError("k must be nonnegative")
        if k == 0:
            return Var_g
        return sp.simplify(_Eg0gk(k) - Eg**2)

    cov1, cov2, cov3 = _Cov(1), _Cov(2), _Cov(3)

    # By the Jordan structure, for k>=1 we expect:
    #   Cov(k) = a*(1/2)^k + (b + c*k)*(-1/2)^k
    a, b, c = sp.symbols("a b c")
    eqs = [
        sp.Eq(cov1 * 2**1, a + (-1) ** 1 * (b + c * 1)),
        sp.Eq(cov2 * 2**2, a + (-1) ** 2 * (b + c * 2)),
        sp.Eq(cov3 * 2**3, a + (-1) ** 3 * (b + c * 3)),
    ]
    sol = sp.solve(eqs, (a, b, c), dict=True)
    if not sol:
        raise RuntimeError("Failed to solve for (a,b,c)")
    a_val = sp.simplify(sol[0][a])
    b_val = sp.simplify(sol[0][b])
    c_val = sp.simplify(sol[0][c])

    half = sp.Rational(1, 2)
    cov_closed_k = sp.simplify(a_val * half**sp.Symbol("k") + (b_val + c_val * sp.Symbol("k")) * (-half) ** sp.Symbol("k"))

    # Validate the closed form for a modest range (exact rational identity).
    for k in range(1, 33):
        if sp.simplify(_Cov(k) - (a_val * half**k + (b_val + c_val * k) * (-half) ** k)) != 0:
            raise RuntimeError(f"Cov closed form mismatch at k={k}")

    # Generating function of the autocovariance sequence.
    z = sp.Symbol("z")
    gen = sp.simplify(
        Var_g
        + a_val * (z * half) / (1 - z * half)
        + b_val * (z * (-half)) / (1 - z * (-half))
        + c_val * (z * (-half)) / (1 - z * (-half)) ** 2
    )
    gen_together = sp.together(gen)

    # Finite-length variance in stationary regime: S_m = sum_{t=1}^m g_t.
    m = sp.Symbol("m", integer=True, positive=True)
    kk = sp.Symbol("k", integer=True, positive=True)
    cov_k_expr = a_val * half**kk + (b_val + c_val * kk) * (-half) ** kk
    Var_Sm = sp.simplify(m * Var_g + 2 * sp.summation((m - kk) * cov_k_expr, (kk, 1, m - 1)))
    Var_Sm_expected = sp.simplify(
        sp.Rational(118, 243) * m
        - sp.Rational(40, 81)
        + (sp.Integer(243) - (-1) ** m * (2 * m + 3)) / (sp.Integer(486) * (2**m))
    )
    if sp.simplify(Var_Sm - Var_Sm_expected) != 0:
        raise RuntimeError("Var(S_m) simplification check failed (unexpected)")

    # Additional numeric audit for small m (exact equality).
    for mm in range(1, 40):
        lhs = sp.simplify(mm * Var_g + 2 * sum((mm - k) * (a_val * half**k + (b_val + c_val * k) * (-half) ** k) for k in range(1, mm)))
        rhs = sp.simplify(Var_Sm_expected.subs({m: mm}))
        if sp.simplify(lhs - rhs) != 0:
            raise RuntimeError(f"Finite-length variance check failed at m={mm}")

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "A0": [[str(x) for x in row] for row in A0.tolist()],
        "pf": {
            "rho_A0": "1",
            "r": r_int,
            "ell": l_int,
            "ell_dot_r": lr,
        },
        "parry": {
            "P": [[str(sp.simplify(P[i, j])) for j in range(4)] for i in range(4)],
            "pi": [str(sp.simplify(pi[i])) for i in range(4)],
            "state_order": ["a", "b", "c", "d"],
        },
        "jordan": {
            "charpoly_lambdaI_minus_P_latex": jordan.charpoly_latex,
            "eigenvals": jordan.eigenvals,
            "neg_half_alg_mult": jordan.neg_half_alg_mult,
            "neg_half_geom_mult": jordan.neg_half_geom_mult,
            "neg_half_geom_mult_sq": jordan.neg_half_geom_mult_sq,
        },
        "observable": {
            "mismatch_edges_state_idx": mismatch_edges,
            "E_g": str(Eg),
            "Var_g": str(Var_g),
        },
        "autocovariance": {
            "a": str(a_val),
            "b": str(b_val),
            "c": str(c_val),
            "Cov_k_closed_form_note": "For k>=1: Cov(k)=a*(1/2)^k + (b+c*k)*(-1/2)^k.",
            "generating_function_together": str(gen_together),
        },
        "finite_length": {
            "Var_Sm_closed_form": str(Var_Sm_expected),
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_jordan_correlations.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"[fold_gauge_anomaly_jordan_correlations] wrote {out_json}", flush=True)

    # TeX fragment (Chinese, consistent with the paper).
    # NOTE: Keep proofs as audit stubs, pointing to this script.
    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_jordan_correlations.py")
    tex.append(r"\paragraph{规范差逐位过程的全相关闭式与 Jordan 指纹}\label{par:fold-gauge-anomaly-jordan}")
    tex.append(
        r"命题 \ref{prop:fold-gauge-anomaly-pressure} 已将逐位失配指示 $g_t=\mathbf 1\{X_t\neq Y_t\}$ 的压力写为"
        r"$P_G(\theta)=\log\rho(A_\theta)$ 并给出显式 $4\times 4$ 矩阵 $A_\theta$。"
        r"取 $\theta=0$ 得 $A_0$，对 Perron 根 $\rho(A_0)=1$ 作 Parry 归一化，可进一步得到该逐位过程的"
        r"谱指纹、完整自协方差序列与有限长度方差的完全闭式。"
    )
    tex.append("")

    tex.append(r"\begin{lemma}[Parry 归一化核与失配边势]\label{lem:fold-gauge-anomaly-parry-kernel}")
    tex.append(r"在状态次序 $(a,b,c,d)$ 下，令 $A_0:=A_\theta|_{\theta=0}$。")
    tex.append(r"取 Perron 根 $\rho(A_0)=1$ 的左右本征向量")
    tex.append(r"\[")
    tex.append(r"r=(2,1,2,1)^\top,\qquad \ell=(2,2,1,1)^\top,\qquad \ell^\top r=9,")
    tex.append(r"\]")
    tex.append(r"并定义 Parry 转移核与平稳分布为")
    tex.append(r"\[")
    tex.append(r"P_{ij}:=\frac{(A_0)_{ij}\,r_j}{r_i},\qquad \pi_i:=\frac{\ell_i r_i}{\ell^\top r}.")
    tex.append(r"\]")
    tex.append(r"则 $P$ 与 $\pi$ 具有完全有理闭式：")
    tex.append(r"\[")
    tex.append(
        r"P=\begin{pmatrix}"
        r"\frac12&\frac14&0&\frac14\\"
        r"0&0&1&0\\"
        r"\frac12&\frac12&0&0\\"
        r"1&0&0&0"
        r"\end{pmatrix},"
        r"\qquad"
        r"\pi=\Bigl(\frac49,\frac29,\frac29,\frac19\Bigr)."
    )
    tex.append(r"\]")
    tex.append(
        r"并且 $A_\theta$ 中携带 $e^\theta$ 的边恰对应 $g_t=1$ 的失配边势："
        r"在 $P$ 上仅三条转移 $(a\!\to\! b),(b\!\to\! c),(c\!\to\! a)$ 取值 $1$，其余转移取值 $0$。"
    )
    tex.append(r"\end{lemma}")
    tex.append("")

    tex.append(r"\begin{theorem}[Jordan 指纹]\label{thm:fold-gauge-anomaly-jordan-fingerprint}")
    tex.append(r"上述 $4$ 态核 $P$ 的谱为 $\{1,\tfrac12,-\tfrac12\}$，且特征值 $-\tfrac12$ 的代数重数为 $2$、几何重数为 $1$，从而存在大小为 $2$ 的 Jordan 块。")
    tex.append(
        r"因此 $P^k$ 的衰减项一般包含 $k(-\tfrac12)^k$ 的广义特征贡献：对任意中心化可加观测量，其相关衰减在一般位置呈现 $k2^{-k}$ 级的多项式修正（并伴随 $(-1)^k$ 振荡），而非纯指数。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{theorem}[自协方差核与生成函数的完全闭式]\label{thm:fold-gauge-anomaly-autocov-closed}")
    tex.append(r"在平稳分布 $\pi$ 下，逐位失配指示满足")
    tex.append(r"\[")
    tex.append(r"\mathbb E[g_t]=\frac49,\qquad \mathrm{Var}(g_t)=\frac{20}{81}.")
    tex.append(r"\]")
    tex.append(r"并且对任意 $k\ge 1$，自协方差具有闭式")
    tex.append(r"\[")
    tex.append(
        r"\mathrm{Cov}(g_t,g_{t+k})"
        r"=2^{-k}\!\left(\frac18+(-1)^k\!\left(\frac{7}{648}+\frac{k}{108}\right)\right)."
    )
    tex.append(r"\]")
    tex.append(r"其协方差生成函数为显式有理函数：")
    tex.append(r"\[")
    tex.append(
        r"\sum_{k\ge 0}\mathrm{Cov}(g_t,g_{t+k})\,z^k"
        r"=\frac{20}{81}+\frac{z}{16(1-z/2)}-\frac{7z}{1296(1+z/2)}-\frac{z}{216(1+z/2)^2}."
    )
    tex.append(r"\]")
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{theorem}[有限长度方差的完全闭式]\label{thm:fold-gauge-anomaly-finite-var-closed}")
    tex.append(r"令 $G_m:=\sum_{t=1}^{m} g_t$。则在平稳初值下有完全闭式")
    tex.append(r"\[")
    tex.append(
        r"\mathrm{Var}(G_m)"
        r"=\frac{118}{243}m-\frac{40}{81}+\frac{243-(-1)^m(2m+3)}{486\cdot 2^m}."
    )
    tex.append(r"\]")
    tex.append(
        r"因此 $\mathrm{Var}(G_m)-\frac{118}{243}m$ 的偏差不仅为 $O(1)$，而且其剩余项精确为 $O(m2^{-m})$（并带显式振荡项）。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{corollary}[Edgeworth 一阶项的可审计封口]\label{cor:fold-gauge-anomaly-edgeworth1}")
    tex.append(
        r"令 $Z_m:=\frac{G_m-\frac49 m}{\sqrt{\frac{118}{243}m}}$。"
        r"在中心极限定理尺度上，其一阶 Edgeworth 近似系数可写为完全闭式："
    )
    tex.append(r"\[")
    tex.append(
        r"\mathbb P(Z_m\le x)=\Phi(x)+\frac{1}{6\sqrt m}\,\gamma_1^{(G)}\,(1-x^2)\varphi(x)+O(m^{-1}),"
        r"\qquad"
        r"\gamma_1^{(G)}=\frac{P_G^{(3)}(0)}{(P_G''(0))^{3/2}}"
        r"=\frac{-\frac{1174}{2187}}{\left(\frac{118}{243}\right)^{3/2}}."
    )
    tex.append(r"\]")
    tex.append(
        r"其中 $\Phi,\varphi$ 分别为标准正态分布函数与密度，"
        r"$P_G^{(3)}(0)$ 与 $P_G''(0)$ 由命题 \ref{prop:fold-gauge-anomaly-pressure} 给出。"
    )
    tex.append(r"\end{corollary}")
    tex.append("")

    tex.append(r"\begin{proof}[证明要点（可审计）]")
    tex.append(
        r"引理 \ref{lem:fold-gauge-anomaly-parry-kernel} 由 $A_0$ 的 Perron 本征向量与 Parry 归一化直接计算得到。"
        r"定理 \ref{thm:fold-gauge-anomaly-jordan-fingerprint} 的特征多项式分解与 $-\tfrac12$ 处 Jordan 块由有限维有理线性代数给出。"
        r"定理 \ref{thm:fold-gauge-anomaly-autocov-closed} 通过在平稳链上把 $g_t$ 视为边势并利用 $P$ 的谱/Jordan 分解，得到自协方差生成函数的有理表达并逐项抽取系数。"
        r"定理 \ref{thm:fold-gauge-anomaly-finite-var-closed} 由"
        r"$\mathrm{Var}(G_m)=m\,\mathrm{Var}(g_t)+2\sum_{k=1}^{m-1}(m-k)\mathrm{Cov}(g_t,g_{t+k})$"
        r"与上一条协方差闭式求和得到。"
        r"以上全部代数化简与一致性校验可由脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_jordan\_correlations.py} 一键复算。"
    )
    tex.append(r"\end{proof}")
    tex.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_jordan_correlations.tex"
    _write_text(out_tex, "\n".join(tex) + "\n")
    print(f"[fold_gauge_anomaly_jordan_correlations] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

