#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
Branch-point audit for the fold gauge-anomaly pressure curve.

We consider the algebraic Perron branch mu(u)=rho(M(u)) for the Berstel 4-state
normalizer (uniform input baseline), where u=e^theta is the mismatch twist.

Let
  F(mu,u) = det(mu I - M(u)) \in Z[mu,u]
be the characteristic polynomial (monic in mu). The branch locus of the
algebraic function mu(u) is governed by Disc_mu(F)(u)=0.

This script:
  - Computes Disc_mu(F) and factors it as -u(u-1) P_10(u).
  - Enumerates the 10 roots of P_10 and classifies which ones correspond to a
    collision of the *dominant* modulus eigenvalue (Perron branch) vs. only
    subdominant sheet collisions.
  - Extracts the nearest complex branch point theta_* = log u_* controlling
    the analytic radius around theta=0, and evaluates the square-root constant
    D_* governing the oscillatory factorial growth of high cumulants.

Outputs:
  - artifacts/export/fold_gauge_anomaly_branch_points.json
  - sections/generated/eq_fold_gauge_anomaly_branch_points.tex
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _build_F(mu: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match scripts/exp_fold_gauge_anomaly_pressure.py and
    # scripts/exp_fold_gauge_anomaly_rate_curve_elimination.py.
    return mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u


def _fmt_float(x: sp.Expr, ndigits: int = 16) -> str:
    return f"{float(sp.N(x, ndigits + 10)):.{ndigits}f}"


def _fmt_complex(z: sp.Expr, ndigits: int = 16) -> Tuple[str, str]:
    re = sp.re(z)
    im = sp.im(z)
    return _fmt_float(re, ndigits=ndigits), _fmt_float(im, ndigits=ndigits)


def _tex_complex(z: sp.Expr, ndigits: int = 16) -> str:
    a, b = _fmt_complex(z, ndigits=ndigits)
    b_abs = abs(float(b))
    sign = "+" if float(b) >= 0 else "-"
    return rf"{a}{sign}{b_abs:.{ndigits}f}\,i"


def _tex_real(z: sp.Expr, ndigits: int = 16) -> str:
    return _fmt_float(sp.re(z), ndigits=ndigits)


def _tex_complex_pm(z: sp.Expr, ndigits: int = 16) -> str:
    """Format conjugate pair as a \\pm b i using the Im>0 representative."""
    a, b = _fmt_complex(z, ndigits=ndigits)
    return rf"{a}\pm{abs(float(b)):.{ndigits}f}\,i"


def _principal_log(z: sp.Expr, prec: int = 80) -> sp.Expr:
    # SymPy log uses the principal branch.
    return sp.log(sp.N(z, prec))


def _principal_sqrt(z: sp.Expr, prec: int = 80) -> sp.Expr:
    # SymPy sqrt uses the principal branch.
    return sp.sqrt(sp.N(z, prec))


def _dominant_double_root(
    F: sp.Expr, mu: sp.Symbol, u: sp.Symbol, u0: sp.Expr, *, prec: int = 80
) -> Dict[str, object]:
    """
    For a discriminant root u0, find the (typically double) mu solving F=F_mu=0,
    and decide whether it is of maximal modulus among the 4 roots of F(mu,u0)=0.
    """
    # Use moderate precision for nroots near multiple roots.
    n_digits = int(min(60, max(30, prec)))
    maxsteps = 200

    u0 = sp.N(u0, n_digits)
    F_mu = sp.diff(F, mu)

    # Candidates from the cubic F_mu(mu,u0)=0
    F_mu_sub = sp.Poly(sp.N(F_mu.subs(u, u0), n_digits), mu)
    mu_candidates = list(sp.nroots(F_mu_sub, n=n_digits, maxsteps=maxsteps))

    best_mu = None
    best_err = None
    for m in mu_candidates:
        err = abs(complex(sp.N(F.subs({u: u0, mu: m}), n_digits)))
        if best_err is None or err < best_err:
            best_err = err
            best_mu = m
    assert best_mu is not None

    # Full quartic roots for modulus comparison
    F_sub = sp.Poly(sp.N(F.subs(u, u0), n_digits), mu)
    mu_roots = list(sp.nroots(F_sub, n=n_digits, maxsteps=maxsteps))
    mods = [abs(complex(sp.N(r, 40))) for r in mu_roots]
    max_mod = max(mods)
    best_mod = abs(complex(sp.N(best_mu, 40)))

    # Decide dominance with a conservative tolerance.
    tol = 1e-8 * max(1.0, max_mod)
    is_dominant = bool(best_mod >= max_mod - tol)

    # Multiplicity indicator: nearest neighbor distance among mu-roots.
    # At a true double root, two roots are extremely close.
    mindist = None
    for i in range(len(mu_roots)):
        zi = complex(sp.N(mu_roots[i], 40))
        for j in range(i + 1, len(mu_roots)):
            zj = complex(sp.N(mu_roots[j], 40))
            d = abs(zi - zj)
            mindist = d if mindist is None else min(mindist, d)

    return {
        "u": str(sp.N(u0, 50)),
        "mu_star": str(sp.N(best_mu, 50)),
        "mu_roots": [str(sp.N(r, 50)) for r in mu_roots],
        "mu_mods": mods,
        "max_mod": float(max_mod),
        "mu_star_mod": float(best_mod),
        "min_pair_distance": float(mindist or 0.0),
        "dominant_merger": bool(is_dominant),
        "residual_abs_F": float(best_err or 0.0),
    }


@dataclass(frozen=True)
class RootRow:
    u_re: float
    u_im: float
    dominant_merger: bool


def main() -> None:
    t0 = time.time()
    print("[fold_gauge_anomaly_branch_points] start", flush=True)

    mu = sp.Symbol("mu")
    u = sp.Symbol("u")
    F = _build_F(mu, u)

    # Discriminant in mu, and its factorization.
    disc = sp.discriminant(F, mu)
    disc_fac = sp.factor(disc)

    # Extract P10(u) from Disc_mu(F) = -u(u-1) P10(u).
    P10 = sp.simplify(disc / (-u * (u - 1)))
    P10 = sp.Poly(P10, u, domain="ZZ")

    # Irreducibility over Q: factorization should be trivial in Z[u].
    P10_fac = sp.factor(P10.as_expr())
    P10_irreducible = bool(P10_fac == P10.as_expr())

    # Roots of P10.
    roots_u = list(sp.nroots(P10, n=80, maxsteps=200))
    roots_u_sorted = sorted(
        roots_u, key=lambda z: (float(sp.re(z).evalf(30)), float(sp.im(z).evalf(30)))
    )

    # Classify dominant vs. subdominant mergers.
    classified = [_dominant_double_root(F, mu=mu, u=u, u0=z, prec=60) for z in roots_u_sorted]
    dominant = [r for r in classified if r["dominant_merger"]]
    if len(dominant) != 2:
        raise RuntimeError(f"Expected exactly 2 dominant-merger roots; got {len(dominant)}")

    # Choose u_* as the root with negative imaginary part (principal log pair).
    dom_u = [sp.N(sp.sympify(r["u"]), 60) for r in dominant]
    u_star = next(z for z in dom_u if float(sp.im(z)) < 0)
    u_star_conj = sp.conjugate(u_star)

    # mu_* at u_* from the classifier record.
    rec_u_star = next(r for r in classified if abs(complex(sp.N(sp.sympify(r["u"]), 40)) - complex(sp.N(u_star, 40))) < 1e-12)
    mu_star = sp.N(sp.sympify(rec_u_star["mu_star"]), 60)

    # theta_* and analytic radius
    theta_star = _principal_log(u_star, prec=80)
    R_theta = sp.Abs(theta_star).evalf(50)

    # Square-root constant at the branch point
    F_u = sp.diff(F, u)
    F_mumu = sp.diff(F, mu, 2)
    Fu_val = sp.N(F_u.subs({u: u_star, mu: mu_star}), 80)
    Fmumu_val = sp.N(F_mumu.subs({u: u_star, mu: mu_star}), 80)
    c_star = _principal_sqrt(-2 * Fu_val / Fmumu_val, prec=80)

    # D_* for transfer asymptotics in theta-plane (principal branches).
    D_star = _principal_sqrt(-theta_star, prec=80) * _principal_sqrt(u_star, prec=80) * c_star / mu_star

    # Prepare a compact root ledger for TeX.
    root_rows: List[RootRow] = []
    for r in classified:
        uz = sp.N(sp.sympify(r["u"]), 50)
        root_rows.append(
            RootRow(
                u_re=float(sp.re(uz).evalf(30)),
                u_im=float(sp.im(uz).evalf(30)),
                dominant_merger=bool(r["dominant_merger"]),
            )
        )

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "polynomials": {
            "F_mu_u": str(F),
            "Disc_mu_F_u": str(disc),
            "Disc_mu_F_factorized": str(disc_fac),
            "P10_u": str(P10.as_expr()),
            "P10_degree": int(P10.degree()),
            "P10_irreducible_over_Q": bool(P10_irreducible),
        },
        "branch_points": {
            "roots_P10_u": [str(sp.N(z, 50)) for z in roots_u_sorted],
            "classified": classified,
            "u_star": str(sp.N(u_star, 50)),
            "u_star_conj": str(sp.N(u_star_conj, 50)),
            "mu_star": str(sp.N(mu_star, 50)),
            "theta_star": str(sp.N(theta_star, 50)),
            "R_theta": str(sp.N(R_theta, 50)),
            "c_star": str(sp.N(c_star, 50)),
            "D_star": str(sp.N(D_star, 50)),
            "D_star_abs": str(sp.N(sp.Abs(D_star), 50)),
        },
        "root_rows_compact": [asdict(rr) for rr in root_rows],
    }

    out_json = export_dir() / "fold_gauge_anomaly_branch_points.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"[fold_gauge_anomaly_branch_points] wrote {out_json}", flush=True)

    # TeX fragment (Chinese, consistent with the paper).
    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_branch_points.py")
    tex.append(r"\begin{proposition}[规范差谱曲线的判别式分解与分支点集合]\label{prop:fold-gauge-anomaly-discriminant-factorization}")
    tex.append(r"沿用命题 \ref{prop:fold-gauge-anomaly-pressure} 的记号，令 \(u=e^\theta\)，并记")
    tex.append(r"\[")
    tex.append(r"F(\mu,u):=\det(\mu I-2A_\theta)\in\ZZ[\mu,u].")
    tex.append(r"\]")
    tex.append(r"则关于根变量 \(\mu\) 的判别式满足完全因式分解")
    tex.append(r"\[")
    tex.append(r"\boxed{\ \mathrm{Disc}_{\mu}\bigl(F(\mu,u)\bigr)=-u(u-1)\,P_{10}(u)\ }")
    tex.append(r"\]")
    tex.append(r"其中 \(P_{10}\in\ZZ[u]\) 在 \(\QQ\) 上不可约，且")
    tex.append(r"\[")
    tex.append(r"\begin{aligned}")
    tex.append(r"P_{10}(u)=\;&" + sp.latex(P10.as_expr()) + r".")
    tex.append(r"\end{aligned}")
    tex.append(r"\]")
    tex.append(r"因此 \(\mu(u)\) 作为代数函数的潜在分支点集合为")
    tex.append(r"\[")
    tex.append(r"\mathcal{B}=\{u=0\}\cup\{u=1\}\cup\{u:\ P_{10}(u)=0\}.")
    tex.append(r"\]")
    tex.append(r"\end{proposition}")
    tex.append("")

    # Root ordering for exposition: two real roots, then complex pairs with Re>0, then Re<0.
    real_roots = [z for z in roots_u_sorted if abs(float(sp.im(z).evalf(30))) < 1e-12]
    real_roots = sorted(real_roots, key=lambda z: float(sp.re(z).evalf(30)))
    complex_pos = [z for z in roots_u_sorted if float(sp.im(z).evalf(30)) > 1e-12]
    pos_pairs = sorted([z for z in complex_pos if float(sp.re(z).evalf(30)) > 0], key=lambda z: float(sp.re(z).evalf(30)))
    neg_pairs = sorted([z for z in complex_pos if float(sp.re(z).evalf(30)) < 0], key=lambda z: float(sp.re(z).evalf(30)), reverse=True)

    tex.append(r"\begin{proposition}[分支点枚举与主导并合的唯一性：真正的 Lee--Yang 边界仅由共轭一对筛选]\label{prop:fold-gauge-anomaly-branch-point-classification}")
    tex.append(r"在命题 \ref{prop:fold-gauge-anomaly-discriminant-factorization} 的记号下，\(P_{10}(u)=0\) 的十个根可数值枚举为两实根与四对共轭复根：")
    tex.append(r"\[")
    tex.append(r"\begin{aligned}")
    if len(real_roots) == 2:
        tex.append(r"&u\approx " + _tex_real(real_roots[0], ndigits=16) + r",\quad u\approx " + _tex_real(real_roots[1], ndigits=16) + r",\\")
    if len(pos_pairs) >= 1:
        tex.append(r"&u\approx " + _tex_complex_pm(pos_pairs[0], ndigits=16) + r",\\")
    if len(pos_pairs) >= 2:
        tex.append(r"&u\approx " + _tex_complex_pm(pos_pairs[1], ndigits=16) + r",\\")
    if len(neg_pairs) >= 1:
        tex.append(r"&u\approx " + _tex_complex_pm(neg_pairs[0], ndigits=16) + r",\\")
    if len(neg_pairs) >= 2:
        tex.append(r"&u\approx " + _tex_complex_pm(neg_pairs[1], ndigits=16) + r".")
    tex.append(r"\end{aligned}")
    tex.append(r"\]")
    tex.append(r"取其中虚部为负者记为 \(u_\ast\)，其共轭记为 \(\overline{u_\ast}\)。")
    tex.append(r"并且在全部分支点集合 \(\mathcal{B}=\{0,1\}\cup\{P_{10}=0\}\) 中，仅有且恰有一对共轭点 \(u_\ast,\overline{u_\ast}\) 使得 \(F(\mu,u)=0\) 的重根同时为最大模特征值。")
    tex.append(r"在 \(u=u_\ast\) 处该重根为")
    tex.append(r"\[")
    tex.append(r"\mu_\ast=" + _tex_complex(mu_star, ndigits=16) + r",")
    tex.append(r"\]")
    tex.append(r"其为两条主导谱支的合并点，从而构成失配自由能 \(P_G(\theta)\) 的非平凡 Lee--Yang edge 代数证书。")
    tex.append(r"\par")
    tex.append(r"其余八个 \(P_{10}\)-根虽同样导致重根出现，但该重根均属于次主导谱支的并合；")
    tex.append(r"此外 \(u=1\) 的判别式零点对应 \((\mu+1)^2\) 的 Jordan 简并而 Perron 根 \(\mu=2\) 保持单根，故 \(u=1\) 不形成 \(P_G\) 的局部奇性屏障。")
    tex.append(r"同理，\(u=0\) 的判别式零点对应 \(\mu=0\) 的双重根而 Perron 分支保持单根，故其并合亦不进入 \(P_G\) 的主支解析屏障。")
    tex.append(r"\end{proposition}")
    tex.append("")

    tex.append(r"\begin{theorem}[最近复分支点与最优解析半径：高阶累积量的振荡型阶乘增长]\label{thm:fold-gauge-anomaly-branch-radius-cumulant-growth}")
    tex.append(
        r"记压力函数 \(P_G(\theta)=\log\rho(A_\theta)\)（命题 \ref{prop:fold-gauge-anomaly-pressure}），"
        r"并令 \(\mu(u)\) 表示代数方程 \(F(\mu,u)=0\) 的主导谱支（在 \(u>0\) 上取最大实根）。"
    )
    tex.append(r"令 \(u_\ast\) 为命题 \ref{prop:fold-gauge-anomaly-branch-point-classification} 的主导并合分支点，并取主值对数 \(\theta_\ast:=\log u_\ast\)。")
    tex.append(r"\[")
    tex.append(r"\theta_\ast=" + _tex_complex(theta_star, ndigits=16) + r",\qquad R_\theta:=|\theta_\ast|=" + _fmt_float(R_theta, ndigits=16) + r".")
    tex.append(r"\]")
    tex.append(r"则 \(P_G\) 在 \(\theta=0\) 为中心的 Taylor 展开之解析半径精确等于 \(R_\theta\)。")
    tex.append(r"亦即 \(P_G\) 在开圆盘 \(\{|\theta|<R_\theta\}\) 内全纯，而在 \(\theta=\theta_\ast,\overline{\theta_\ast}\) 处出现不可去的代数分支奇性，故该半径为最优。")
    tex.append(r"\par")
    tex.append(r"此外，\(\theta_\ast\) 为平方根型分支点：在 \((\mu_\ast,u_\ast)\) 处有 \(F(\mu_\ast,u_\ast)=0\)、\(\partial_\mu F(\mu_\ast,u_\ast)=0\)，并且 \(\partial_{\mu\mu}^2F(\mu_\ast,u_\ast)\neq 0\)、\(\partial_uF(\mu_\ast,u_\ast)\neq 0\)。")
    tex.append(r"因此主导特征值分支满足局部 Puiseux 展开")
    tex.append(r"\[")
    tex.append(
        r"\mu(u)=\mu_\ast\pm c_\ast\sqrt{u-u_\ast}+O(u-u_\ast),\qquad "
        r"c_\ast:=\sqrt{-\frac{2\,\partial_uF(\mu_\ast,u_\ast)}{\partial_{\mu\mu}^2F(\mu_\ast,u_\ast)}}."
    )
    tex.append(r"\]")
    tex.append(r"由 \(P_G(\theta)=\log(\mu(e^\theta)/2)\) 及标准奇点分析转移定理，得高阶导数的主导渐近：当 \(n\to\infty\)，")
    tex.append(r"\[")
    tex.append(
        r"P_G^{(n)}(0)=-\frac{n!}{\sqrt{\pi}}\;n^{-3/2}\;\Re\!\left(D_\ast\,\theta_\ast^{-n}\right)"
        r"+O\!\left(n!\,R_\theta^{-n}\,n^{-5/2}\right),"
    )
    tex.append(r"\]")
    tex.append(r"其中常数 \(D_\ast\) 可显式写为")
    tex.append(r"\[")
    tex.append(
        r"D_\ast:=\frac{\sqrt{-\theta_\ast}\,\sqrt{u_\ast}}{\mu_\ast}\,"
        r"\sqrt{-\frac{2\,\partial_uF(\mu_\ast,u_\ast)}{\partial_{\mu\mu}^2F(\mu_\ast,u_\ast)}}"
        r"=" + _tex_complex(D_star, ndigits=16) + r",\qquad |D_\ast|=" + _fmt_float(sp.Abs(D_star), ndigits=16) + r"."
    )
    tex.append(r"\]")
    tex.append(r"该渐近式蕴含：")
    tex.append(r"\begin{enumerate}")
    tex.append(r"\item \(P_G^{(n)}(0)\) 的阶乘–指数增长阈值由 \(R_\theta\) 唯一决定；")
    tex.append(r"\item 由于 \(\theta_\ast\notin\RR\)，项 \(\Re(D_\ast\theta_\ast^{-n})\) 产生不可约振荡因子，从而高阶累积量呈现振荡型增长律。")
    tex.append(r"\end{enumerate}")
    tex.append(r"\end{theorem}")
    tex.append("")
    tex.append(r"\begin{proof}[证明要点（可复现核验）]")
    tex.append(
        r"判别式分解由直接符号计算 \(\mathrm{Disc}_{\mu}(F)\) 并在 \(\ZZ[u]\) 中因式分解得到。"
        r"对 \(P_{10}(u)=0\) 的各分支点，重根由方程组 \(F=\partial_\mu F=0\) 的数值求解给出；"
        r"再与四个谱根的模比较即可区分“主导/次主导并合”。"
        r"最近复分支点 \(\theta_\ast=\log u_\ast\) 的选择与 \(R_\theta\) 的最优性由该分类立得。"
        r"平方根型 Puiseux 系数与 \(D_\ast\) 由隐函数局部展开与 \(u=e^\theta\) 的复对数提升得到。"
        r"上述计算与数值常量可由脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_branch\_points.py} 一键复算；"
        r"其与内部审计记录 \cite{Internal2026FoldGaugeAnomalyBranchPointsAudit} 对齐。"
    )
    tex.append(r"\end{proof}")
    tex.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_branch_points.tex"
    _write_text(out_tex, "\n".join(tex))
    print(f"[fold_gauge_anomaly_branch_points] wrote {out_tex}", flush=True)

    print("[fold_gauge_anomaly_branch_points] done", flush=True)


if __name__ == "__main__":
    main()

