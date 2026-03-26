#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Spectral fingerprint + correlation/Hankel certificates for the fold gauge anomaly.

This script is English-only by repository convention.

Context (paper):
- Prop. `prop:fold-gauge-anomaly-pressure` defines the weighted adjacency A_theta
  for the Berstel (2001) 4-state unambiguous Zeckendorf normalizer and sets
    P_G(theta)=log rho(A_theta).
- At theta=0, A_0 := A_theta|_{theta=0} is the *untilted* transfer operator
  for the uniform micro baseline.

Goal:
Derive a set of *auditable* closed-form, finite-statistic checkable constraints:
  (i) exact characteristic polynomial / spectrum / Jordan defect of A_0,
 (ii) exact two-point covariance Cov(g_t, g_{t+k}) in closed form,
(iii) rational covariance generating function,
 (iv) linear recurrence + Hankel rank certificate,
  (v) fully closed finite-m variance Var(G_m) with exponentially small corrections.

Outputs:
- artifacts/export/fold_gauge_anomaly_spectral_fingerprint.json
- sections/generated/eq_fold_gauge_anomaly_spectral_fingerprint.tex
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _sympy_to_tex(expr: sp.Expr) -> str:
    return sp.latex(sp.simplify(expr))


def _sign_normalize_positive(v: sp.Matrix) -> sp.Matrix:
    """Flip sign so that the first nonzero entry is positive."""
    for x in list(v):
        if x == 0:
            continue
        return v if x > 0 else -v
    return v


def _pf_left_right_lambda1(A0: sp.Matrix) -> Tuple[sp.Matrix, sp.Matrix]:
    """Return (l, r) with l^T A0 = l^T, A0 r = r, and l^T r = 1 (exact)."""
    n = int(A0.shape[0])
    I = sp.eye(n)

    r_ns = (A0 - I).nullspace()
    if not r_ns:
        raise RuntimeError("Missing right eigenvector at eigenvalue 1 (unexpected).")
    r = _sign_normalize_positive(r_ns[0])

    l_ns = (A0.T - I).nullspace()
    if not l_ns:
        raise RuntimeError("Missing left eigenvector at eigenvalue 1 (unexpected).")
    l = _sign_normalize_positive(l_ns[0])

    lr = sp.simplify((l.T * r)[0])
    if lr == 0:
        raise RuntimeError("Degenerate normalization l^T r = 0 (unexpected).")
    l = sp.simplify(l / lr)
    return l, r


def main() -> None:
    t0 = time.time()

    half = sp.Rational(1, 2)

    # Unscaled matrix M(1) from Prop. prop:fold-gauge-anomaly-pressure:
    #   A_theta = (1/2) * M(e^theta).
    M0 = sp.Matrix(
        [
            [1, 1, 0, 1],
            [0, 0, 1, 0],
            [1, 2, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    A0 = sp.simplify(half * M0)

    # Mismatch-edge weight matrix at theta=0 (same base weights as A0, but only mismatch edges kept).
    # In M(u), the mismatch edges are precisely those with coefficient u:
    #   (a->b), (b->c), (c->a).
    G0 = sp.simplify(
        half
        * sp.Matrix(
            [
                [0, 1, 0, 0],
                [0, 0, 1, 0],
                [1, 0, 0, 0],
                [0, 0, 0, 0],
            ]
        )
    )

    # Characteristic polynomial / spectrum.
    lam = sp.Symbol("lambda")
    chi = sp.factor((lam * sp.eye(4) - A0).det())
    eigs = {sp.simplify(k): int(v) for k, v in A0.eigenvals().items()}

    # Jordan defect audit at eigenvalue -1/2: compare nullities of (A0+1/2 I) and its square.
    J = sp.simplify(A0 + half * sp.eye(4))
    null1 = int(4 - J.rank())
    null2 = int(4 - (J**2).rank())

    # PF eigenvectors at eigenvalue 1 and mismatch expectation / correlations.
    l, r = _pf_left_right_lambda1(A0)
    # l^T r = 1 by construction.
    g_star = sp.simplify((l.T * G0 * r)[0])
    if sp.simplify(g_star - sp.Rational(4, 9)) != 0:
        raise RuntimeError(f"Unexpected E[g_t] (got {g_star}, expected 4/9).")

    def E_gg(k: int) -> sp.Expr:
        if k < 1:
            raise ValueError("Require k>=1")
        return sp.simplify((l.T * G0 * (A0 ** (k - 1)) * G0 * r)[0])

    # Covariance d_k := Cov(g_t, g_{t+k}), k>=1.
    d_vals: Dict[int, sp.Expr] = {}
    for k in range(1, 11):
        d_vals[k] = sp.simplify(E_gg(k) - g_star**2)

    # Fit to the expected Jordan form:
    #   d_k = a*(1/2)^{k-1} + (b + c*(k-1))*(-1/2)^{k-1}.
    a, b, c = sp.symbols("a b c")
    d1, d2, d3 = d_vals[1], d_vals[2], d_vals[3]
    sol = sp.solve(
        [
            sp.Eq(d1, a + b),
            sp.Eq(d2, a * half + (b + c) * (-half)),
            sp.Eq(d3, a * half**2 + (b + 2 * c) * ((-half) ** 2)),
        ],
        [a, b, c],
        dict=True,
    )
    if not sol:
        raise RuntimeError("Failed to solve for covariance closed-form coefficients.")
    a0 = sp.simplify(sol[0][a])
    b0 = sp.simplify(sol[0][b])
    c0 = sp.simplify(sol[0][c])

    # Keep a strict audit lock on the published closed form.
    # If upstream definitions change, this script should fail loudly rather than
    # silently emitting mismatched TeX.
    if sp.simplify(a0 - sp.Rational(1, 16)) != 0:
        raise RuntimeError(f"Unexpected covariance coefficient a (got {a0}, expected 1/16).")
    if sp.simplify(b0 - (-sp.Rational(13, 1296))) != 0:
        raise RuntimeError(f"Unexpected covariance coefficient b (got {b0}, expected -13/1296).")
    if sp.simplify(c0 - (-sp.Rational(1, 216))) != 0:
        raise RuntimeError(f"Unexpected covariance coefficient c (got {c0}, expected -1/216).")

    ksym = sp.Symbol("k", integer=True, positive=True)
    d_k_expr = sp.simplify(
        a0 * (half ** (ksym - 1)) + (b0 + c0 * (ksym - 1)) * ((-half) ** (ksym - 1))
    )

    # Verify closed form against first few exact values.
    for k in range(1, 11):
        if sp.simplify(d_k_expr.subs({ksym: k}) - d_vals[k]) != 0:
            raise RuntimeError(f"Closed-form mismatch at k={k}.")

    # Generating function C(z) = sum_{k>=1} d_k z^k (rational).
    z = sp.Symbol("z")
    r_alt = -z / 2
    C = sp.simplify(
        a0 * (z / (1 - z / 2))
        + z * (b0 / (1 - r_alt) + c0 * (r_alt / (1 - r_alt) ** 2))
    )
    C = sp.together(C)

    # Linear recurrence corresponding to (r-1/2)(r+1/2)^2.
    # d_{k+3} = -(1/2)d_{k+2} + (1/4)d_{k+1} + (1/8)d_k.
    def _rec_residual(k0: int) -> sp.Expr:
        return sp.simplify(
            d_k_expr.subs({ksym: k0 + 3})
            + half * d_k_expr.subs({ksym: k0 + 2})
            - sp.Rational(1, 4) * d_k_expr.subs({ksym: k0 + 1})
            - sp.Rational(1, 8) * d_k_expr.subs({ksym: k0})
        )

    for k0 in range(1, 8):
        if _rec_residual(k0) != 0:
            raise RuntimeError(f"Recurrence residual nonzero at k={k0}.")

    # Hankel rank audit via finite truncations.
    def hankel_block(n: int) -> sp.Matrix:
        return sp.Matrix(
            [[sp.simplify(d_k_expr.subs({ksym: i + j + 1})) for j in range(n)] for i in range(n)]
        )

    H3 = hankel_block(3)
    H4 = hankel_block(4)
    det_H3 = sp.simplify(H3.det())
    det_H4 = sp.simplify(H4.det())
    rank_H6 = int(hankel_block(6).rank())

    # Finite-m variance closed form.
    msym = sp.Symbol("m", integer=True, positive=True)
    var_g = sp.simplify(g_star * (1 - g_star))
    S = sp.summation((msym - ksym) * d_k_expr, (ksym, 1, msym - 1))
    var_Gm = sp.simplify(var_g * msym + 2 * S)
    var_Gm = sp.together(var_Gm)

    target_var = sp.simplify(
        sp.Rational(118, 243) * msym
        - sp.Rational(40, 81)
        + (sp.Integer(243) - ((-1) ** msym) * (2 * msym + 3)) / (sp.Integer(486) * (2**msym))
    )
    if sp.simplify(var_Gm - target_var) != 0:
        raise RuntimeError("Variance closed form does not match the expected simplified expression.")

    # Export JSON audit payload.
    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "A0": {
            "matrix": [[str(A0[i, j]) for j in range(4)] for i in range(4)],
            "charpoly_det_lambdaI_minus_A0": str(chi),
            "eigenvals_alg_mult": {str(k): int(v) for k, v in sorted(eigs.items(), key=lambda kv: float(kv[0]))},
            "jordan_shadow_at_minus_half": {
                "nullity(A0+1/2 I)": null1,
                "nullity((A0+1/2 I)^2)": null2,
            },
        },
        "observable": {
            "g_star_E_g": str(g_star),
            "var_g": str(var_g),
        },
        "covariance": {
            "coeff_a": str(a0),
            "coeff_b": str(b0),
            "coeff_c": str(c0),
            "closed_form": str(d_k_expr),
            "values_k_1_10": {str(k): str(d_vals[k]) for k in range(1, 11)},
            "generating_function_Cz": str(C),
            "hankel": {
                "det_H3": str(det_H3),
                "det_H4": str(det_H4),
                "rank_H6": rank_H6,
            },
        },
        "variance_Gm": {
            "closed_form": str(target_var),
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_spectral_fingerprint.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"[fold_gauge_anomaly_spectral_fingerprint] wrote {out_json}", flush=True)

    # TeX fragment (Chinese; theorem/proof-style consistent with the paper).
    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_spectral_fingerprint.py")
    tex.append(
        r"\begin{remark}[可审计的谱指纹—相位残差接口：从 $A_\theta$ 推出二点统计与 Hankel 证书]\label{rem:fold-gauge-anomaly-spectral-fingerprint-intro}"
    )
    tex.append(
        r"在命题 \ref{prop:fold-gauge-anomaly-pressure} 的矩阵接口上，"
        r"进一步可推出一组原文未显式列出的、但完全可复算的“谱指纹—相关闭式—Hankel 秩证书”结论："
        r"其中 $(-1/2)$ 的 Jordan 缺陷在二点相关中严格显影为交错相位残差。"
        r"它们把规范差的统计涨落从叙事性表述转写为“有限统计量即可核验”的硬约束。"
        r"下述所有闭式均可由脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_spectral\_fingerprint.py} 一键复算。"
    )
    tex.append(r"\end{remark}")
    tex.append("")

    tex.append(r"\paragraph{未倾斜算子的谱指纹与 Jordan 残差}")
    tex.append(r"\begin{theorem}[$A_0$ 的精确谱指纹与 Jordan 结构]\label{thm:fold-gauge-anomaly-A0-jordan}")
    tex.append(
        r"令 $A_0:=A_\theta|_{\theta=0}$ 为命题 \ref{prop:fold-gauge-anomaly-pressure} 中的未倾斜加权邻接矩阵。"
        r"则其特征多项式满足分解"
    )
    tex.append(r"\[")
    tex.append(r"\boxed{\ \chi_{A_0}(\lambda)=\det(\lambda I-A_0)=" + _sympy_to_tex(chi) + r"\ }.")
    tex.append(r"\]")
    tex.append(
        r"因此"
        r"\(\mathrm{spec}(A_0)=\{1,\frac12,-\frac12\}\)，其中 $\lambda=-\frac12$ 的代数重数为 $2$、几何重数为 $1$（存在一个 $2\times 2$ Jordan 块）。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{remark}[结构性含义：交错相位模态与一阶 nilpotent 残差]\label{rem:fold-gauge-anomaly-jordan-meaning}")
    tex.append(
        r"定理 \ref{thm:fold-gauge-anomaly-A0-jordan} 表明，规范差的涨落除常规混合模态外还携带一个载荷为 $-1/2$ 的交错相位模态；"
        r"其 Jordan 缺陷在统计投影上产生“指数衰减 $\times$ 线性多项式”的可见尾项，"
        r"从而可由二点统计直接捕捉（见下述关于二点相关闭式与 $O(k2^{-k})$ 衰减律的段落）。"
    )
    tex.append(r"\end{remark}")
    tex.append("")

    tex.append(r"\paragraph{二点相关闭式与 $O(k2^{-k})$ 衰减律}")
    tex.append(r"\begin{theorem}[失配指示过程的二点协方差闭式]\label{thm:fold-gauge-anomaly-cov-closed}")
    tex.append(
        r"令 $g_t=\mathbf 1\{X_t\neq Y_t\}$ 为命题 \ref{prop:fold-gauge-anomaly-pressure} 的逐位失配指示过程，并取其在均匀基线下的平稳极限口径。"
        r"则"
    )
    tex.append(r"\[")
    tex.append(r"\mathbb E[g_t]=P_G'(0)=\frac49.")
    tex.append(r"\]")
    tex.append(r"并且对任意 $k\ge 1$，二点协方差满足完全闭式")
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ \mathrm{Cov}(g_t,g_{t+k})"
        r"=\frac1{16}\Big(\frac12\Big)^{k-1}"
        r"+\Big(-\frac{13}{1296}-\frac{k-1}{216}\Big)\Big(-\frac12\Big)^{k-1}\ }."
    )
    tex.append(r"\]")
    tex.append(
        r"因此存在严格渐近衰减律"
        r"\(\mathrm{Cov}(g_t,g_{t+k})=O(k\,2^{-k})\)，其中线性因子 $k$ 正对应于定理 \ref{thm:fold-gauge-anomaly-A0-jordan} 的 $(-1/2)$ Jordan 残差。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{corollary}[协方差生成函数的有理闭式]\label{cor:fold-gauge-anomaly-cov-genfun}")
    tex.append(r"令")
    tex.append(r"\[")
    tex.append(r"C(z):=\sum_{k\ge 1}\mathrm{Cov}(g_t,g_{t+k})\,z^k.")
    tex.append(r"\]")
    tex.append(r"则 $C$ 为有理函数，且具有闭式")
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ C(z)=\frac{z/16}{1-z/2}"
        r"-\frac{13z/1296}{1+z/2}"
        r"+\frac{z^2/432}{(1+z/2)^2}\ }."
    )
    tex.append(r"\]")
    tex.append(r"\end{corollary}")
    tex.append("")

    tex.append(r"\paragraph{有限样本可核验的 Hankel 秩证书与递推律}")
    tex.append(r"\begin{theorem}[三阶线性递推与 Hankel 秩 $=3$]\label{thm:fold-gauge-anomaly-hankel-rank3}")
    tex.append(r"令 $d_k:=\mathrm{Cov}(g_t,g_{t+k})$（$k\ge 1$）。则对所有 $k\ge 1$ 有严格递推")
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ d_{k+3}=-\frac12\,d_{k+2}+\frac14\,d_{k+1}+\frac18\,d_k\ }."
    )
    tex.append(r"\]")
    tex.append(
        r"等价地，以 $(d_k)$ 生成的无限 Hankel 矩阵 $H=(d_{i+j+1})_{i,j\ge 0}$ 满足 $\mathrm{rank}(H)=3$。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{corollary}[无参一致性的有限数据审计口径]\label{cor:fold-gauge-anomaly-hankel-audit}")
    tex.append(
        r"任意实现若声称其“折叠归一化—投影读出”与本文均匀基线机制一致，"
        r"则其从观测数据估计得到的滞后协方差序列 $(\widehat d_k)$ 必须近似满足"
        r"定理 \ref{thm:fold-gauge-anomaly-hankel-rank3} 的递推关系（等价于低 Hankel 秩约束）。"
        r"系统性偏离意味着存在额外不可见自由度或口径结构发生改变，而非仅为参数扰动。"
    )
    tex.append(r"\end{corollary}")
    tex.append("")

    tex.append(r"\paragraph{有限长度方差的完全闭式（CLT 常数的全量校验）}")
    tex.append(r"\begin{theorem}[$G_m=\sum_{t=1}^m g_t$ 的方差全闭式]\label{thm:fold-gauge-anomaly-var-finite-closed}")
    tex.append(r"在同一平稳口径下，对任意 $m\ge 1$，有")
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ \mathrm{Var}(G_m)=\frac{118}{243}\,m-\frac{40}{81}"
        r"+\frac{243-(-1)^m(2m+3)}{486\cdot 2^m}\ }."
    )
    tex.append(r"\]")
    tex.append(
        r"从而 \(\mathrm{Var}(G_m)/m=\frac{118}{243}+O(2^{-m})\)，"
        r"并且指数小修正项携带 $(-1)^m$ 的交错相位签名，与定理 \ref{thm:fold-gauge-anomaly-A0-jordan} 的 $(-1/2)$ 模态一致。"
    )
    tex.append(r"\end{theorem}")
    tex.append("")

    tex.append(r"\begin{proposition}[可检验的相位残差定律（统一陈述）]\label{prop:fold-gauge-anomaly-spectral-residual-law}")
    tex.append(
        r"在命题 \ref{prop:fold-gauge-anomaly-pressure} 的无参数矩阵接口与均匀基线之下，"
        r"定理 \ref{thm:fold-gauge-anomaly-A0-jordan}--\ref{thm:fold-gauge-anomaly-var-finite-closed} "
        r"共同给出一个低维、可识别且可审计的残差判据："
    )
    tex.append(r"\begin{enumerate}")
    tex.append(r"\item 未倾斜算子 $A_0$ 出现 $(-1/2)$ 的 Jordan 缺陷（定理 \ref{thm:fold-gauge-anomaly-A0-jordan}）。")
    tex.append(
        r"\item 二点协方差呈 $O(k2^{-k})$ 级交错衰减，并带有线性多项式因子（定理 \ref{thm:fold-gauge-anomaly-cov-closed}）。"
    )
    tex.append(
        r"\item 协方差序列满足三阶线性递推，等价于 Hankel 秩 $=3$ 的证书约束（定理 \ref{thm:fold-gauge-anomaly-hankel-rank3}）。"
    )
    tex.append(
        r"\item 有限长度方差具有完全闭式，并含有显式 $(-1)^m$ 的交错相位修正（定理 \ref{thm:fold-gauge-anomaly-var-finite-closed}）。"
    )
    tex.append(r"\end{enumerate}")
    tex.append(
        r"因此，“是否确已把不可逆性外置为正交记录轴”的断言在该最小模型上具备了可复算、可证伪的统计硬接口，"
        r"并与命题 \ref{prop:unit-circle-phase-extension-preserving} 的扩展保存口径一致。"
    )
    tex.append(r"\end{proposition}")
    tex.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_spectral_fingerprint.tex"
    _write_text(out_tex, "\n".join(tex) + "\n")
    print(f"[fold_gauge_anomaly_spectral_fingerprint] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

