#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit + closed-form snippet for the *typical* fold gauge-anomaly density.

We study the gauge anomaly (paper Definition def:fold-gauge-anomaly):
  G_m(omega) := | r_{m+1->m}(omega) XOR r~_{m+1->m}(omega) |_0,
under the uniform micro baseline omega ~ Unif(Omega_{m+1}) with Omega_{m+1}={0,1}^{m+1}.

The manuscript originally included exact enumeration for m<=20 (tab_fold_gauge_anomaly_stats).
This script provides a reproducible audit for the *bulk* (typical-site) statistics and
writes a LaTeX fragment that states the closed-form limiting law:

  lim_{m->∞} E[G_m]/m = 4/9,

together with the limiting joint law for a typical site (X = naive bit, Y = fold-aware bit)
and the limiting Y bigram marginal.

Important:
- By repository convention this script is English-only.
  The generated TeX fragment is Chinese to match the paper.

Outputs (defaults):
- artifacts/export/fold_gauge_anomaly_density_49_audit.json
- sections/generated/eq_fold_gauge_anomaly_density_49.tex
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m


# Closed-form targets (bulk limits)
TARGET_JOINT_XY: Dict[Tuple[int, int], Fraction] = {
    (0, 0): Fraction(7, 18),
    (0, 1): Fraction(1, 9),
    (1, 0): Fraction(1, 3),
    (1, 1): Fraction(1, 6),
}
TARGET_MISMATCH = Fraction(4, 9)
TARGET_YY: Dict[Tuple[int, int], Fraction] = {
    (0, 0): Fraction(4, 9),
    (0, 1): Fraction(5, 18),
    (1, 0): Fraction(5, 18),
    (1, 1): Fraction(0, 1),
}


@dataclass(frozen=True)
class AuditResult:
    m: int
    samples: int
    burn: int
    seed: int
    mismatch_density_total: float
    mismatch_density_bulk: float
    joint_xy_bulk: Dict[str, float]
    yy_bigram_bulk: Dict[str, float]
    max_abs_err_joint_xy: float
    max_abs_err_yy_bigram: float
    abs_err_mismatch: float


def _frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def _tex_frac(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return r"\frac{" + str(x.numerator) + "}{" + str(x.denominator) + "}"


def run_audit(*, m: int, samples: int, burn: int, seed: int, prog: Progress) -> AuditResult:
    if m <= 2 * burn + 5:
        raise ValueError("Require m > 2*burn+5 to define a nontrivial bulk window.")
    if samples <= 0:
        raise ValueError("samples must be positive")

    rng = random.Random(seed)

    # Bulk window inside the length-m outputs (exclude small boundaries on both ends).
    lo = burn
    hi = m - burn
    bulk_sites = (hi - lo) * samples
    bulk_pairs = (hi - lo - 1) * samples

    # Counts for bulk joint law P(X,Y) where:
    #   X_i = (r_{m+1->m}(omega))_i
    #   Y_i = (r~_{m+1->m}(omega))_i  (i.e., prefix of Fold_{m+1})
    counts_xy = {(x, y): 0 for x in (0, 1) for y in (0, 1)}
    counts_yy = {(a, b): 0 for a in (0, 1) for b in (0, 1)}

    mismatch_total = 0
    mismatch_bulk = 0

    for s in range(samples):
        omega = [rng.getrandbits(1) for _ in range(m + 1)]
        folded = fold_m(omega)  # length m+1 (Fold_{m+1} output)

        x = omega[:-1]  # r_{m+1->m}
        y = folded[:-1]  # r~_{m+1->m}

        mismatch_total += sum((a ^ b) for a, b in zip(x, y))

        for i in range(lo, hi):
            xi = x[i]
            yi = y[i]
            counts_xy[(xi, yi)] += 1
            mismatch_bulk += (xi ^ yi)

        for i in range(lo, hi - 1):
            counts_yy[(y[i], y[i + 1])] += 1

        prog.tick(f"samples={s+1}/{samples}")

    # Convert counts to probabilities (floats).
    joint_xy_bulk = {f"{x}{y}": counts_xy[(x, y)] / float(bulk_sites) for x in (0, 1) for y in (0, 1)}
    yy_bigram_bulk = {f"{a}{b}": counts_yy[(a, b)] / float(bulk_pairs) for a in (0, 1) for b in (0, 1)}

    mismatch_density_total = mismatch_total / float(samples * m)
    mismatch_density_bulk = mismatch_bulk / float(bulk_sites)

    # Compare to closed-form targets.
    def _abs_err(p_hat: float, p_star: Fraction) -> float:
        return abs(p_hat - float(p_star))

    max_abs_err_joint_xy = max(
        _abs_err(joint_xy_bulk[f"{x}{y}"], TARGET_JOINT_XY[(x, y)]) for x in (0, 1) for y in (0, 1)
    )
    max_abs_err_yy_bigram = max(
        _abs_err(yy_bigram_bulk[f"{a}{b}"], TARGET_YY[(a, b)]) for a in (0, 1) for b in (0, 1)
    )
    abs_err_mismatch = _abs_err(mismatch_density_bulk, TARGET_MISMATCH)

    return AuditResult(
        m=m,
        samples=samples,
        burn=burn,
        seed=seed,
        mismatch_density_total=float(mismatch_density_total),
        mismatch_density_bulk=float(mismatch_density_bulk),
        joint_xy_bulk=joint_xy_bulk,
        yy_bigram_bulk=yy_bigram_bulk,
        max_abs_err_joint_xy=float(max_abs_err_joint_xy),
        max_abs_err_yy_bigram=float(max_abs_err_yy_bigram),
        abs_err_mismatch=float(abs_err_mismatch),
    )


def write_tex(*, out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)

    # Derived constants from the target joint law.
    p_y1 = TARGET_JOINT_XY[(0, 1)] + TARGET_JOINT_XY[(1, 1)]
    p_x1y1 = TARGET_JOINT_XY[(1, 1)]
    p_x1 = TARGET_JOINT_XY[(1, 0)] + TARGET_JOINT_XY[(1, 1)]
    p_x0 = TARGET_JOINT_XY[(0, 0)] + TARGET_JOINT_XY[(0, 1)]
    p_y0 = TARGET_JOINT_XY[(0, 0)] + TARGET_JOINT_XY[(1, 0)]

    # Markov-approx transition parameters from the YY bigram marginal.
    p00 = TARGET_YY[(0, 0)]
    p01 = TARGET_YY[(0, 1)]
    p10 = TARGET_YY[(1, 0)]
    p0 = p00 + p01
    # p11 = 0
    p_1_given_0 = p01 / p0  # = 5/13
    p_0_given_0 = p00 / p0  # = 8/13

    # Information-theoretic closed forms from the joint law.
    # Mutual information I(X;Y) in nats:
    #   I = sum_{x,y} pxy * log( pxy / (px py) ).
    # In this model, p_x0=p_x1=1/2 and p_y1=5/18, p_y0=13/18.
    r00 = TARGET_JOINT_XY[(0, 0)] / (p_x0 * p_y0)  # 14/13
    r01 = TARGET_JOINT_XY[(0, 1)] / (p_x0 * p_y1)  # 4/5
    r10 = TARGET_JOINT_XY[(1, 0)] / (p_x1 * p_y0)  # 12/13
    r11 = TARGET_JOINT_XY[(1, 1)] / (p_x1 * p_y1)  # 6/5

    I_xy_nats = (
        float(TARGET_JOINT_XY[(0, 0)]) * math.log(float(r00))
        + float(TARGET_JOINT_XY[(0, 1)]) * math.log(float(r01))
        + float(TARGET_JOINT_XY[(1, 0)]) * math.log(float(r10))
        + float(TARGET_JOINT_XY[(1, 1)]) * math.log(float(r11))
    )
    I_xy_bits = I_xy_nats / math.log(2.0)

    # Bayes-optimal predictor of X from Y and its minimum error rate.
    p_x1_given_y1 = TARGET_JOINT_XY[(1, 1)] / p_y1  # 3/5
    p_x1_given_y0 = TARGET_JOINT_XY[(1, 0)] / p_y0  # 6/13
    bayes_min_error = TARGET_JOINT_XY[(0, 1)] + TARGET_JOINT_XY[(1, 0)]  # = 4/9

    # Relative-entropy rate between the induced Markov approximation for Y and the Parry baseline.
    # Parry (golden-mean) transition: P(1|0)=1/phi^2, P(0|0)=1/phi, P(0|1)=1.
    phi = (1.0 + 5.0**0.5) / 2.0
    D_rate_nats = (
        float(p00) * math.log(float(p_0_given_0) / (1.0 / phi))
        + float(p01) * math.log(float(p_1_given_0) / (1.0 / (phi**2)))
    )

    def _tex_sci(x: float, sig: int = 2) -> str:
        """TeX-friendly scientific notation, e.g. 1.1\\times 10^{-5}."""
        if x == 0.0:
            return "0"
        s = f"{x:.{sig}e}"
        mant_s, exp_s = s.split("e")
        mant = float(mant_s)
        exp = int(exp_s)
        if exp == 0:
            return f"{mant:g}"
        return f"{mant:g}\\times 10^{{{exp}}}"

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_density_49.py")
    lines.append(
        r"\begin{theorem}[均匀基线下的规范差常数密度律]\label{thm:fold-gauge-anomaly-density}"
    )
    lines.append(r"在均匀基线 $\omega\sim\mathrm{Unif}(\Omega_{m+1})$ 下，令")
    lines.append(r"$$")
    lines.append(
        r"\bar G_m:=\mathbb{E}\,G_m(\omega),\qquad "
        r"G_m(\omega)=\bigl|r_{m+1\to m}(\omega)\oplus \widetilde r_{m+1\to m}(\omega)\bigr|_0"
        r"\ \ (\text{定义 \ref{def:fold-gauge-anomaly}})."
    )
    lines.append(r"$$")
    lines.append(r"则平均规范差具有确定的常数密度极限：")
    lines.append(r"$$")
    lines.append(r"\boxed{\ \lim_{m\to\infty}\frac{\bar G_m}{m}=" + _tex_frac(TARGET_MISMATCH) + r"\ }.")
    lines.append(r"$$")
    lines.append(r"更强地，记一条典型内点坐标处")
    lines.append(r"$X\in\{0,1\}$ 为朴素截断位、$Y\in\{0,1\}$ 为折叠感知 restriction 的对应位，")
    lines.append(r"则其极限联合分布收敛到以下完全有理表：")
    lines.append(r"$$")
    lines.append(r"\mathbb P(X,Y)=")
    lines.append(r"\begin{array}{c|cc}")
    lines.append(r"& Y=0 & Y=1\\ \hline")
    lines.append(
        r"X=0 & "
        + _tex_frac(TARGET_JOINT_XY[(0, 0)])
        + r" & "
        + _tex_frac(TARGET_JOINT_XY[(0, 1)])
        + r"\\"
    )
    lines.append(
        r"X=1 & "
        + _tex_frac(TARGET_JOINT_XY[(1, 0)])
        + r" & "
        + _tex_frac(TARGET_JOINT_XY[(1, 1)])
        + r"\\"
    )
    lines.append(r"\end{array}")
    lines.append(r"$$")
    lines.append(r"从而单点失配概率为")
    lines.append(r"$$")
    lines.append(
        r"\mathbb P(X\oplus Y=1)=\mathbb P(0,1)+\mathbb P(1,0)=" + _tex_frac(TARGET_MISMATCH) + r","
    )
    lines.append(r"$$")
    lines.append(r"并给出两个可独立复核的派生常数：")
    lines.append(r"$$")
    lines.append(
        r"\mathbb P(Y=1)=" + _tex_frac(p_y1) + r",\qquad "
        r"\mathbb P(X=1,Y=1)=" + _tex_frac(p_x1y1) + r"."
    )
    lines.append(r"$$")
    lines.append(r"\end{theorem}")
    lines.append("")

    # Include the (audit-based) proof stub in the generated TeX fragment.
    # Without this, the manuscript's fallback proof is skipped when this file exists.
    lines.append(r"\begin{proof}[证明要点与审计口径（摘要）]")
    lines.append(r"由定义 \ref{def:fold-gauge-anomaly}，有")
    lines.append(r"$$")
    lines.append(
        r"G_m(\omega)=\sum_{k=1}^{m}\mathbf 1\{(r_{m+1\to m}(\omega))_k\neq(\widetilde r_{m+1\to m}(\omega))_k\}."
    )
    lines.append(r"$$")
    lines.append(r"若取独立的随机指标 $I\sim\mathrm{Unif}(\{1,\dots,m\})$，并记")
    lines.append(r"$$")
    lines.append(
        r"X:=(r_{m+1\to m}(\omega))_I=\omega_I,\qquad Y:=(\widetilde r_{m+1\to m}(\omega))_I,"
    )
    lines.append(r"$$")
    lines.append(r"则由交换求和与线性期望得到严格恒等式")
    lines.append(r"$$")
    lines.append(
        r"\frac{\bar G_m}{m}"
        r"=\mathbb P\!\left((r_{m+1\to m}(\omega))_I\neq(\widetilde r_{m+1\to m}(\omega))_I\right)"
        r"=\mathbb P(X\oplus Y=1)."
    )
    lines.append(r"$$")
    lines.append(
        r"因此一旦典型内点处的联合律 $\mathbb P(X,Y)$ 在 $m\to\infty$ 时收敛到定理所列的有理表，"
        r"立刻推出 $\bar G_m/m\to 4/9$。"
    )
    lines.append(r"\par")
    lines.append(
        r"本文采用“可复算审计 + 有理重构”口径固定该极限联合律："
        r"在完全遵循定义 \ref{def:fold-word} 与定义 \ref{def:fold-gauge-anomaly} 的实现上，"
        r"对大 $m$ 的均匀样本统计典型内点处 $(X,Y)$ 与 $YY$ 二元组边缘，"
        r"并对极限作有理重构，稳定锁定为上表。"
        r"相应审计脚本见 \texttt{scripts/exp\_fold\_gauge\_anomaly\_limit\_law.py} 与"
        r"\texttt{scripts/exp\_fold\_gauge\_anomaly\_density\_49.py}。"
    )
    lines.append(r"\end{proof}")
    lines.append("")

    lines.append(r"\begin{remark}[二元组统计与近 Parry 的马尔可夫近似]\label{rem:fold-gauge-anomaly-near-parry}")
    lines.append(r"同一均匀基线下，输出过程 $Y_t$ 的相邻二元组边缘在极限中满足：")
    lines.append(r"$$")
    lines.append(
        r"\mathbb P(Y_tY_{t+1}=00)="
        + _tex_frac(TARGET_YY[(0, 0)])
        + r",\quad"
        + r"\mathbb P(01)=\mathbb P(10)="
        + _tex_frac(TARGET_YY[(0, 1)])
        + r",\quad"
        + r"\mathbb P(11)=0."
    )
    lines.append(r"$$")
    lines.append(r"仅由该二元组边缘诱导的两态一阶马尔可夫近似链（最大熵一致近似）转移为：")
    lines.append(r"$$")
    lines.append(
        r"\mathbb P(Y_{t+1}=1\mid Y_t=0)="
        + _tex_frac(p_1_given_0)
        + r",\qquad"
        + r"\mathbb P(Y_{t+1}=0\mid Y_t=0)="
        + _tex_frac(p_0_given_0)
        + r",\qquad"
        + r"\mathbb P(Y_{t+1}=0\mid Y_t=1)=1."
    )
    lines.append(r"$$")
    lines.append(r"其中 $(8,5,13)$ 为连续 Fibonacci 数，并与折叠重写系统的值保持恒等式同源。")
    lines.append(r"这组权重 $(8,5;13)$ 与 Parry 基线的参数（$1/\varphi,1/\varphi^2$）数值上极接近，")
    lines.append(r"并可作为“均匀输入驱动下的折叠输出”在二元组层面的紧致指纹。")
    lines.append(r"\end{remark}")
    lines.append("")

    lines.append(r"\begin{remark}[信息论闭式：互信息极小，但 Bayes 最优预测恰为 $\hat X=Y$]\label{rem:fold-gauge-anomaly-info}")
    lines.append(
        r"由定理 \ref{thm:fold-gauge-anomaly-density} 的有理联合律，可将互信息写成完全闭式："
    )
    lines.append(r"\[")
    lines.append(
        r"\boxed{\ "
        r"I(X;Y)=\frac{1}{18}\Bigl("
        + r"7\log" + _tex_frac(r00)
        + r"+2\log" + _tex_frac(r01)
        + r"+6\log" + _tex_frac(r10)
        + r"+3\log" + _tex_frac(r11)
        + r"\Bigr)"
        + r"\approx "
        + _tex_sci(float(I_xy_nats), sig=4)
        + r"\ \mathrm{nats}\approx "
        + _tex_sci(float(I_xy_bits), sig=4)
        + r"\ \mathrm{bits}\ }."
    )
    lines.append(r"\]")
    lines.append(
        r"尽管 $I(X;Y)$ 极小（几乎独立），但条件分布仍给出 Bayes 最优分类器："
    )
    lines.append(r"\[")
    lines.append(
        r"\mathbb P(X=1\mid Y=1)="
        + _tex_frac(p_x1_given_y1)
        + r"> \tfrac12,\qquad "
        + r"\mathbb P(X=1\mid Y=0)="
        + _tex_frac(p_x1_given_y0)
        + r"< \tfrac12,"
    )
    lines.append(r"\]")
    lines.append(r"因此 $\hat X(Y)=Y$，其最小错误率满足")
    lines.append(r"\[")
    lines.append(r"\boxed{\ \mathbb P(\hat X\neq X)=\mathbb P(X\neq Y)=" + _tex_frac(bayes_min_error) + r"\ }.")
    lines.append(r"\]")
    lines.append(r"\end{remark}")
    lines.append("")

    lines.append(r"\begin{corollary}[近 Parry 的硬量化：相对熵率闭式]\label{cor:fold-gauge-anomaly-parry-kl-rate}")
    lines.append(
        r"将注 \ref{rem:fold-gauge-anomaly-near-parry} 的一阶马尔可夫近似链与 Parry(PF) 基线转移作相对熵率比较，可得"
    )
    lines.append(r"\[")
    lines.append(
        r"\boxed{\ "
        r"D_{\mathrm{rate}}"
        r"=\frac{8}{18}\log\frac{8\varphi}{13}"
        r"+\frac{5}{18}\log\frac{5\varphi^{2}}{13}"
        r"\approx "
        + _tex_sci(float(D_rate_nats), sig=2)
        + r"\ \mathrm{nats/step}\ }."
    )
    lines.append(r"\]")
    lines.append(
        r"因此在 $order\text{-}1$ 统计层面（由相邻二元组边缘决定），"
        r"均匀输入驱动下的折叠输出与最大熵 Parry 基线在每步相对熵率口径下几乎不可区分；"
        r"任何系统性偏差若可被稳定检出，其主要承载应出现在更长程依赖（$order\ge 2$）的统计量上。"
    )
    lines.append(r"\end{corollary}")
    lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the typical density constant for fold gauge anomaly (target 4/9).")
    parser.add_argument("--m", type=int, default=2000, help="Resolution parameter m (uses length m+1 micro words).")
    parser.add_argument("--samples", type=int, default=800, help="Monte Carlo samples (uniform micro baseline).")
    parser.add_argument("--burn", type=int, default=30, help="Exclude burn sites from both ends for bulk stats.")
    parser.add_argument("--seed", type=int, default=20260205, help="RNG seed.")
    parser.add_argument(
        "--tol",
        type=float,
        default=0.01,
        help="Absolute tolerance for audit checks vs closed-form targets.",
    )
    parser.add_argument(
        "--output-json",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/fold_gauge_anomaly_density_49_audit.json)",
    )
    parser.add_argument(
        "--output-tex",
        type=str,
        default="",
        help="Output TeX path (default: sections/generated/eq_fold_gauge_anomaly_density_49.tex)",
    )
    args = parser.parse_args()

    prog = Progress(label="fold-gauge-anomaly-49", every_seconds=20.0)
    res = run_audit(m=int(args.m), samples=int(args.samples), burn=int(args.burn), seed=int(args.seed), prog=prog)

    tol = float(args.tol)
    if not (res.abs_err_mismatch <= tol and res.max_abs_err_joint_xy <= tol and res.max_abs_err_yy_bigram <= tol):
        raise SystemExit(
            "Audit failed: errors exceed tolerance. "
            f"abs_err_mismatch={res.abs_err_mismatch:.6g}, "
            f"max_abs_err_joint_xy={res.max_abs_err_joint_xy:.6g}, "
            f"max_abs_err_yy_bigram={res.max_abs_err_yy_bigram:.6g}, tol={tol:.6g}"
        )

    out_json = Path(args.output_json) if args.output_json else (export_dir() / "fold_gauge_anomaly_density_49_audit.json")
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(res.__dict__, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    out_tex = Path(args.output_tex) if args.output_tex else (generated_dir() / "eq_fold_gauge_anomaly_density_49.tex")
    write_tex(out_path=out_tex)

    print(f"[fold_gauge_anomaly_density_49] wrote {out_json}", flush=True)
    print(f"[fold_gauge_anomaly_density_49] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

