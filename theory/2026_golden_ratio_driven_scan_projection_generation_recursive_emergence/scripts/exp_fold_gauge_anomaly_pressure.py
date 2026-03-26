#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Algebraic pressure function for the fold gauge anomaly (uniform micro baseline).

This script is English-only by repository convention.

We model the per-position mismatch observable
  g_t := 1{X_t != Y_t},
where X_t is the IID Bernoulli(1/2) input bit and Y_t is the corresponding
Zeckendorf-normalized output bit (Berstel 2001 unambiguous normalizer, Fig. 1).

The cumulant generating function per step ("pressure")
  P_G(theta) := lim_{m->infty} (1/m) log E exp(theta * sum_{t=1}^m g_t)
exists and equals log rho(A_theta) for a finite weighted adjacency matrix.

Outputs:
- artifacts/export/fold_gauge_anomaly_pressure.json
- sections/generated/eq_fold_gauge_anomaly_pressure.tex
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _sympy_to_tex(expr: sp.Expr) -> str:
    # Use a compact TeX printer (no multiline environments).
    return sp.latex(sp.simplify(expr))


def main() -> None:
    t0 = time.time()

    # u = e^theta is the mismatch twist parameter; mu is the PF eigenvalue of M(u).
    u, mu = sp.symbols("u mu", positive=True, real=True)

    # Unscaled weighted adjacency M(u) for the Berstel 4-state normalizer, with
    # edge weights = P(X=input_bit) * u^{1{input!=output}} and a global factor 2
    # cleared. We choose the state order (a,b,c,d), and collect parallel edges.
    #
    # A_theta = (1/2) * M(e^theta), so rho(A_theta) = mu(u)/2.
    M = sp.Matrix(
        [
            [1, u, 0, 1],  # a -> a (0|0), a -> b (0|1 mismatch), a -> d (1|1)
            [0, 0, u, 0],  # b -> c (1|0 mismatch)
            [u, 2, 0, 0],  # c -> a (1|0 mismatch), c -> b (0|0 and 1|1)
            [1, 0, 0, 0],  # d -> a (0|0)
        ]
    )

    # Characteristic polynomial det(mu I - M(u)).
    F = sp.expand((mu * sp.eye(4) - M).det())

    # Derivatives at theta=0 via implicit differentiation at (u=1, mu=2).
    # mu'(u) = -F_u / F_mu.
    F_mu = sp.diff(F, mu)
    F_u = sp.diff(F, u)

    u0 = sp.Rational(1, 1)
    mu0 = sp.Rational(2, 1)

    mu_prime = sp.simplify((-F_u / F_mu).subs({u: u0, mu: mu0}))

    # Second derivative: differentiate F_mu*mu' + F_u = 0 once more.
    Fmu_mu = sp.diff(F_mu, mu)
    Fmu_u = sp.diff(F_mu, u)
    Fu_mu = sp.diff(F_u, mu)
    Fu_u = sp.diff(F_u, u)
    mu_second = sp.simplify(
        (-(Fmu_u * (-F_u / F_mu) + Fmu_mu * (-F_u / F_mu) ** 2 + Fu_u + Fu_mu * (-F_u / F_mu)) / F_mu).subs(
            {u: u0, mu: mu0}
        )
    )

    # Third derivative mu'''(1) via implicit differentiation (auditable, pure algebra).
    # For F(mu(u),u)=0, let:
    #   A=F_mu, B=F_mumu, C=F_mu_u,
    #   E=F_mumumu, Fm=F_mumu_u, G=F_mu_uu, I=F_uuu
    # then:
    #   mu''' = -[ 3(B mu' + C) mu'' + E (mu')^3 + 3 Fm (mu')^2 + 3 G mu' + I ] / A
    F_mumu = sp.diff(F, mu, 2)
    F_mu_u_mixed = sp.diff(F, mu, 1, u, 1)
    F_mumumu = sp.diff(F, mu, 3)
    F_mumu_u = sp.diff(F, mu, 2, u, 1)
    F_mu_uu = sp.diff(F, mu, 1, u, 2)
    F_uuu = sp.diff(F, u, 3)

    A0 = sp.simplify(F_mu.subs({u: u0, mu: mu0}))
    B0 = sp.simplify(F_mumu.subs({u: u0, mu: mu0}))
    C0 = sp.simplify(F_mu_u_mixed.subs({u: u0, mu: mu0}))
    E0 = sp.simplify(F_mumumu.subs({u: u0, mu: mu0}))
    F0 = sp.simplify(F_mumu_u.subs({u: u0, mu: mu0}))
    G0 = sp.simplify(F_mu_uu.subs({u: u0, mu: mu0}))
    I0 = sp.simplify(F_uuu.subs({u: u0, mu: mu0}))

    mu_third = sp.simplify(
        -(
            3 * (B0 * mu_prime + C0) * mu_second
            + E0 * mu_prime**3
            + 3 * F0 * mu_prime**2
            + 3 * G0 * mu_prime
            + I0
        )
        / A0
    )

    # Pressure: P(theta)=log rho(A_theta)=log(mu(u)/2), u=e^theta.
    # P'(0) = u * mu'(u)/mu(u) at u=1.
    g_star = sp.simplify((u * (-F_u / F_mu) / mu).subs({u: u0, mu: mu0}))

    # P''(0) = u * d/du (u mu'/mu) at u=1.
    # Using: d/du (u mu'/mu) = mu'/mu + u*(mu''/mu - (mu')^2/mu^2).
    P2 = sp.simplify(
        (u * ((mu_prime / mu0) + u * (mu_second / mu0 - (mu_prime**2) / (mu0**2)))).subs({u: u0})
    )

    # Third theta-derivative P_G^{(3)}(0) from mu'(1),mu''(1),mu'''(1).
    # Let r(u)=d/du log(mu(u))=mu'(u)/mu(u). Then:
    #   P'(0)=r(1), P''(0)=r(1)+r'(1), P'''(0)=r(1)+3r'(1)+r''(1).
    f0 = mu0
    f1 = mu_prime
    f2 = mu_second
    f3 = mu_third
    r0 = sp.simplify(f1 / f0)
    r1 = sp.simplify((f2 * f0 - f1**2) / (f0**2))
    r2 = sp.simplify((f3 * f0**2 - 3 * f1 * f2 * f0 + 2 * f1**3) / (f0**3))
    P3 = sp.simplify(r0 + 3 * r1 + r2)

    # Standardized per-step skewness intensity gamma1 = P'''(0) / (P''(0))^{3/2}.
    gamma1_float = float(P3) / (float(P2) ** 1.5) if float(P2) > 0 else float("nan")

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "matrix": {
            "M_u": [[str(x) for x in row] for row in M.tolist()],
            "state_order": ["a", "b", "c", "d"],
            "note": "A_theta = (1/2) * M(e^theta); mu(u)=rho(M(u)).",
        },
        "polynomial": {
            "det_muI_minus_M": str(F),
            "latex": _sympy_to_tex(F),
        },
        "derivatives_at_theta_0": {
            "u0": str(u0),
            "mu0": str(mu0),
            "mu_prime_at_u1": str(mu_prime),
            "mu_second_at_u1": str(mu_second),
            "mu_third_at_u1": str(mu_third),
            "g_star_P_prime_0": str(g_star),
            "sigma2_P_second_0": str(P2),
            "cum3_density_P_third_0": str(P3),
            "gamma1_skewness_intensity_float": float(gamma1_float),
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_pressure.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"[fold_gauge_anomaly_pressure] wrote {out_json}", flush=True)

    # TeX fragment (Chinese, consistent with the paper).
    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_pressure.py")
    tex.append(r"\begin{proposition}[规范差的压力函数（代数闭式）]\label{prop:fold-gauge-anomaly-pressure}")
    tex.append(
        r"在均匀基线 $\omega\sim\mathrm{Unif}(\Omega_{m+1})$ 下，令 $g_t=\mathbf 1\{X_t\neq Y_t\}$ 为规范差的逐位失配指示（定义 \ref{def:fold-gauge-anomaly}），并记"
    )
    tex.append(r"\[")
    tex.append(r"P_G(\theta):=\lim_{m\to\infty}\frac1m\log \mathbb E\exp\!\left(\theta\sum_{t=1}^{m} g_t\right).")
    tex.append(r"\]")
    tex.append(r"则该极限存在且可写为一个有限维加权邻接矩阵的谱半径：")
    tex.append(r"\[")
    tex.append(r"P_G(\theta)=\log\rho(A_\theta),\qquad")
    tex.append(r"A_\theta=\frac12\begin{pmatrix}")
    tex.append(r"1 & e^\theta & 0 & 1\\")
    tex.append(r"0 & 0 & e^\theta & 0\\")
    tex.append(r"e^\theta & 2 & 0 & 0\\")
    tex.append(r"1 & 0 & 0 & 0")
    tex.append(r"\end{pmatrix}.")
    tex.append(r"\]")
    tex.append(r"令 $u=e^\theta$，并记 $\mu(u):=2\,\rho(A_\theta)=\rho\!\bigl(2A_\theta\bigr)$。则 $\mu(u)$ 是以下四次多项式的最大实根：")
    tex.append(r"\[")
    tex.append(r"\boxed{\ " + _sympy_to_tex(F) + r"=0\ }.")
    tex.append(r"\]")
    tex.append(r"因此 $P_G(\theta)=\log(\mu(e^\theta)/2)$。并且在 $\theta=0$ 处可由隐式微分闭式读出：")
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ P_G'(0)="
        + _sympy_to_tex(g_star)
        + r",\qquad P_G''(0)="
        + _sympy_to_tex(P2)
        + r",\qquad P_G^{(3)}(0)="
        + _sympy_to_tex(P3)
        + r"\ }."
    )
    tex.append(r"\]")
    tex.append(r"\end{proposition}")
    tex.append("")
    tex.append(r"\begin{proof}[证明要点（可审计）]")
    tex.append(
        r"矩阵 $A_\theta$ 来自 Berstel 的 $4$ 状态不歧义 Zeckendorf 归一化换能器（\cite{ITA_2001__35_6_491_0}，Figure~1）："
        r"对每条边赋权 $w_\theta=e^{\theta\,\mathbf 1\{X\neq Y\}}\cdot\mathbb P(X)$（均匀输入下 $\mathbb P(X=0)=\mathbb P(X=1)=1/2$），"
        r"得到加权邻接矩阵 $A_\theta$。由有限状态边移位的热力学形式主义，压力 $P_G(\theta)$ 等于 $\log\rho(A_\theta)$，"
        r"并且 $\mu(u)=2\rho(A_\theta)$ 满足特征方程 $\det(\mu I-2A_\theta)=0$，即上式四次多项式。"
    )
    tex.append(
        r"在 $(u,\mu)=(1,2)$ 处对该代数关系做隐式微分，可得 $\mu'(1),\mu''(1),\mu'''(1)$，"
        r"从而由 $P_G(\theta)=\log(\mu(e^\theta)/2)$ 得到 $P_G'(0),P_G''(0),P_G^{(3)}(0)$ 的闭式。"
        r"上述推导与代数运算可由脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_pressure.py} 一键复算。"
    )
    tex.append(r"\end{proof}")
    tex.append("")

    tex.append(r"\begin{corollary}[三阶偏斜审计常数与“非自对偶”指纹]\label{cor:fold-gauge-anomaly-cumulant3}")
    tex.append(
        r"在同一均匀基线下，规范差和 $G_m=\sum_{t=1}^{m}g_t$ 的三阶累积量满足"
        r"$\mathrm{cum}_3(G_m)=P_G^{(3)}(0)\,m+o(m)$。"
        r"相应的“每步偏斜强度”（标准化偏斜系数）为"
    )
    tex.append(r"\[")
    tex.append(
        r"\boxed{\ \gamma_1^{(G)}:=\frac{P_G^{(3)}(0)}{(P_G''(0))^{3/2}}\approx %.3g\ }."
        % float(gamma1_float)
    )
    tex.append(r"\]")
    tex.append(r"其中 $P_G^{(3)}(0)<0$ 表明规范差涨落具有稳定的负偏斜（超出二次高斯近似可见范围）。")
    tex.append(r"\end{corollary}")
    tex.append("")
    tex.append(r"\begin{remark}[对照：自对偶完成化的 Gallavotti--Cohen 偶性与最低阶指纹]\label{rem:fold-gauge-anomaly-non-self-dual-fingerprint}")
    tex.append(
        r"对照自对偶完成化通道，定理 \ref{thm:sync-kernel-gallavotti-cohen} 给出"
        r"$\Lambda(\theta):=P(\theta)-\theta/2$ 的偶性 $\Lambda(\theta)=\Lambda(-\theta)$，"
        r"等价于 $P(\theta)=\theta+P(-\theta)$。"
        r"因此在自对偶类中，中心化累积母函数的所有奇阶导数严格为零，尤其有 $P^{(3)}(0)=0$。"
    )
    tex.append(
        r"相比之下，本节规范差压力满足 $P_G^{(3)}(0)=-1174/2187\neq 0$，"
        r"从而偏斜审计常数 $\gamma_1^{(G)}\neq 0$ 可被视为“非自对偶”类的最低阶可核对指纹。"
    )
    tex.append(r"\end{remark}")
    tex.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_pressure.tex"
    _write_text(out_tex, "\n".join(tex))
    print(f"[fold_gauge_anomaly_pressure] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

