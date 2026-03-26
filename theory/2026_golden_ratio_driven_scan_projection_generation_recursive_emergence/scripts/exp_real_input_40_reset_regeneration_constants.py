#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Reset-word regeneration constants under the Parry baseline (real-input model).

We take two independent golden-mean Parry Markov chains x,y on {0,1} with forbidden word 11,
and define d_t = x_t + y_t ∈ {0,1,2}. The sync-kernel reset word 0^5 occurs exactly when d
contains five consecutive zeros, i.e. when (x_t,y_t) = (0,0) for five consecutive times.

We define the reset sector Z_{>=5} at time t by the event {d_{t-4}...d_t = 0^5}. From this
structure we compute:
  (A) P(Z_{>=5}) in closed form Q(sqrt(5)),
  (B) the Kac mean return time 1/P(Z_{>=5}),
  (C) the mean waiting time from a typical non-reset time to the next entry,
  (D) the strict exponential tail exponent lambda_reg (Perron root of a 7x7 substochastic
      matrix on the non-reset sector), and associated time constants.

All closed forms are computed in exact Q(sqrt(5)) arithmetic using Fractions.

Outputs (default):
  - artifacts/export/real_input_40_reset_regeneration_constants.json
  - sections/generated/eq_real_input_40_reset_regeneration_constants.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from typing import List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir


# ---- Q(sqrt(5)) exact arithmetic ----

Q5 = Tuple[Fraction, Fraction]  # a + b*sqrt(5)


def q5(a: int | Fraction = 0, b: int | Fraction = 0) -> Q5:
    return (a if isinstance(a, Fraction) else Fraction(a), b if isinstance(b, Fraction) else Fraction(b))


def q5_is_zero(x: Q5) -> bool:
    return x[0] == 0 and x[1] == 0


def q5_add(x: Q5, y: Q5) -> Q5:
    return (x[0] + y[0], x[1] + y[1])


def q5_sub(x: Q5, y: Q5) -> Q5:
    return (x[0] - y[0], x[1] - y[1])


def q5_neg(x: Q5) -> Q5:
    return (-x[0], -x[1])


def q5_mul(x: Q5, y: Q5) -> Q5:
    # (a+b s)(c+d s) = (ac+5bd) + (ad+bc) s
    a, b = x
    c, d = y
    return (a * c + Fraction(5) * b * d, a * d + b * c)


def q5_inv(x: Q5) -> Q5:
    a, b = x
    den = a * a - Fraction(5) * b * b
    if den == 0:
        raise ZeroDivisionError("singular Q(sqrt5) element")
    return (a / den, -b / den)


def q5_div(x: Q5, y: Q5) -> Q5:
    return q5_mul(x, q5_inv(y))


def q5_float(x: Q5) -> float:
    return float(x[0]) + float(x[1]) * math.sqrt(5.0)


def _tex_frac(f: Fraction) -> str:
    if f.denominator == 1:
        return str(f.numerator)
    return rf"\frac{{{f.numerator}}}{{{f.denominator}}}"


def tex_q5(x: Q5) -> str:
    a, b = x
    if b == 0:
        return _tex_frac(a)
    sgn = "+" if b > 0 else "-"
    bb = b if b > 0 else -b
    if a == 0:
        if sgn == "-":
            return rf"-{_tex_frac(bb)}\sqrt5"
        return rf"{_tex_frac(bb)}\sqrt5"
    return rf"{_tex_frac(a)} {sgn} {_tex_frac(bb)}\sqrt5"


def _frac_str(f: Fraction) -> str:
    if f.denominator == 1:
        return str(f.numerator)
    return f"{f.numerator}/{f.denominator}"


def q5_str(x: Q5) -> str:
    """A JSON-friendly string, matching existing export style: a + b*sqrt(5)."""
    a, b = x
    if b == 0:
        return _frac_str(a)

    def sqrt_term(bb: Fraction) -> str:
        if bb.denominator == 1:
            return f"{bb.numerator}*sqrt(5)"
        return f"{bb.numerator}*sqrt(5)/{bb.denominator}"

    if a == 0:
        return sqrt_term(b)
    if b > 0:
        return f"{_frac_str(a)} + {sqrt_term(b)}"
    return f"{_frac_str(a)} - {sqrt_term(-b)}"


def gaussian_solve(A: List[List[Q5]], b: List[Q5]) -> List[Q5]:
    """Solve A x = b over Q(sqrt5) by Gauss-Jordan elimination (exact)."""
    n = len(A)
    M = [row[:] for row in A]
    x = b[:]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if not q5_is_zero(M[r][col]):
                piv = r
                break
        if piv is None:
            raise RuntimeError("singular system (no pivot)")
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            x[col], x[piv] = x[piv], x[col]

        inv_p = q5_inv(M[col][col])
        for j in range(col, n):
            M[col][j] = q5_mul(M[col][j], inv_p)
        x[col] = q5_mul(x[col], inv_p)

        for r in range(n):
            if r == col:
                continue
            f = M[r][col]
            if q5_is_zero(f):
                continue
            for j in range(col, n):
                M[r][j] = q5_sub(M[r][j], q5_mul(f, M[col][j]))
            x[r] = q5_sub(x[r], q5_mul(f, x[col]))
    return x


# ---- 8-state chain for zero-run tracking ----

STATE_ORDER_8 = [
    "01",
    "10",
    "11",
    "00^1",
    "00^2",
    "00^3",
    "00^4",
    "00^{>=5}",
]


def build_chain_P() -> List[List[Q5]]:
    """Return the 8x8 transition matrix in exact Q(sqrt5)."""
    # 1/phi = (sqrt5 - 1)/2,  1/phi^2 = (3 - sqrt5)/2.
    invphi = q5(Fraction(-1, 2), Fraction(1, 2))
    invphi2 = q5(Fraction(3, 2), Fraction(-1, 2))

    z = q5(0)
    P: List[List[Q5]] = [[z for _ in range(8)] for _ in range(8)]

    # from 01: to 00^1 with prob 1/phi, to 10 with prob 1/phi^2
    P[0][3] = invphi
    P[0][1] = invphi2

    # from 10: to 00^1 with prob 1/phi, to 01 with prob 1/phi^2
    P[1][3] = invphi
    P[1][0] = invphi2

    # from 11: forced to 00^1
    P[2][3] = q5(1)

    # from 00: independent next bits, hence
    #   P(00->00)=1/phi^2,
    #   P(00->01)=P(00->10)=1/phi^3,
    #   P(00->11)=1/phi^4.
    p00 = invphi2
    p01 = q5_mul(invphi, invphi2)
    p11 = q5_mul(invphi2, invphi2)

    for k in (3, 4, 5, 6):
        P[k][k + 1] = p00
        P[k][0] = p01
        P[k][1] = p01
        P[k][2] = p11

    P[7][7] = p00
    P[7][0] = p01
    P[7][1] = p01
    P[7][2] = p11

    one = q5(1)
    for i in range(8):
        s = q5(0)
        for j in range(8):
            s = q5_add(s, P[i][j])
        if s != one:
            raise RuntimeError(f"row {i} does not sum to 1: {s}")
    return P


def stationary_dist(P: List[List[Q5]]) -> List[Q5]:
    """Stationary distribution as a column vector (length 8)."""
    n = 8
    A: List[List[Q5]] = [[q5(0) for _ in range(n)] for _ in range(n)]
    b: List[Q5] = [q5(0) for _ in range(n)]

    for i in range(n):
        for j in range(n):
            A[i][j] = q5_sub(P[j][i], q5(1) if i == j else q5(0))

    # Replace last equation by normalization.
    A[n - 1] = [q5(1) for _ in range(n)]
    b[n - 1] = q5(1)

    return gaussian_solve(A, b)


def mean_hitting_time_to_reset(P: List[List[Q5]], pi: List[Q5]) -> Tuple[List[Q5], Q5]:
    """Return (h, E[T]) where h_i = E_i[T] for i in non-reset states 0..6."""
    Q = [[P[i][j] for j in range(7)] for i in range(7)]
    # (I - Q) h = 1
    A = [[q5(0) for _ in range(7)] for _ in range(7)]
    b = [q5(1) for _ in range(7)]
    for i in range(7):
        for j in range(7):
            A[i][j] = q5_sub(q5(1) if i == j else q5(0), Q[i][j])
    h = gaussian_solve(A, b)

    pZ5 = pi[7]
    mu_den = q5_sub(q5(1), pZ5)
    mu = [q5_div(pi[i], mu_den) for i in range(7)]

    ET = q5(0)
    for i in range(7):
        ET = q5_add(ET, q5_mul(mu[i], h[i]))
    return h, ET


@dataclass(frozen=True)
class Export:
    state_order_8: List[str]
    p_reset_sector_closed: str
    p_reset_sector_float: float
    mean_return_closed: str
    mean_return_float: float
    mean_wait_nonreset_closed: str
    mean_wait_nonreset_float: float
    lambda_reg: float
    c_asym: float
    c_ub_search_max_n: int
    c_ub: float
    c_ub_argmax_n: int
    tau_reg: float
    t_half: float
    Q_closed: List[List[str]]


def main() -> None:
    ap = argparse.ArgumentParser(description="Reset-word regeneration constants (Parry baseline).")
    ap.add_argument(
        "--max-n",
        type=int,
        default=20000,
        help="Search window for c_ub := max_{0<=n<=N} P(T>n)/lambda^n.",
    )
    args = ap.parse_args()

    P = build_chain_P()
    pi = stationary_dist(P)

    pZ5 = pi[7]
    mean_return = q5_inv(pZ5)
    _h, ET = mean_hitting_time_to_reset(P, pi)

    # Closed-form self-audits.
    pZ5_ref = q5(Fraction(9, 5), Fraction(-4, 5))  # (9 - 4*sqrt5)/5
    mean_return_ref = q5(45, 20)  # 45 + 20*sqrt5
    ET_ref = q5(Fraction(555, 8), Fraction(127, 4))  # 555/8 + 127/4*sqrt5
    if pZ5 != pZ5_ref:
        raise RuntimeError(f"unexpected P(Z>=5): got {pZ5}, expected {pZ5_ref}")
    if mean_return != mean_return_ref:
        raise RuntimeError(f"unexpected mean return: got {mean_return}, expected {mean_return_ref}")
    if ET != ET_ref:
        raise RuntimeError(f"unexpected E[T]: got {ET}, expected {ET_ref}")

    # Float summaries.
    pZ5_f = q5_float(pZ5_ref)
    mean_return_f = q5_float(mean_return_ref)
    ET_f = q5_float(ET_ref)

    # Numeric tail exponent on the non-reset sector.
    Qf = np.array([[q5_float(P[i][j]) for j in range(7)] for i in range(7)], dtype=float)
    eigvals, eigvecs = np.linalg.eig(Qf)
    idx = int(np.argmax(np.real(eigvals)))
    lam = float(np.real(eigvals[idx]))
    if not (0.0 < lam < 1.0):
        raise RuntimeError(f"lambda_reg should be in (0,1), got {lam}")

    # Asymptotic constant via left/right PF eigenvectors.
    vr = np.real(eigvecs[:, idx])
    if float(vr.sum()) < 0:
        vr = -vr
    eigvals_t, eigvecs_t = np.linalg.eig(Qf.T)
    idx_t = int(np.argmax(np.real(eigvals_t)))
    vl = np.real(eigvecs_t[:, idx_t])
    if float(vl.sum()) < 0:
        vl = -vl
    vl = vl / float(vl @ vr)  # normalize so that vl^T vr = 1

    # mu: stationary conditioned on non-reset.
    pi_f = np.array([q5_float(x) for x in pi], dtype=float)
    mu_f = pi_f[:7] / float(1.0 - pi_f[7])
    one = np.ones(7, dtype=float)
    c_asym = float((mu_f @ vr) * (vl @ one))

    # c_ub search: max_{0<=n<=N} P(T>n) / lam^n
    v = mu_f.copy()
    max_ratio = -1.0
    max_n = 0
    lam_pow = 1.0
    for n in range(int(args.max_n) + 1):
        surv = float(v @ one)
        ratio = surv / lam_pow
        if ratio > max_ratio:
            max_ratio = ratio
            max_n = n
        v = v @ Qf
        lam_pow *= lam

    tau_reg = 1.0 / (-math.log(lam))
    t_half = math.log(2.0) / (-math.log(lam))

    Q_closed = [[q5_str(P[i][j]) for j in range(7)] for i in range(7)]

    ex = Export(
        state_order_8=list(STATE_ORDER_8),
        p_reset_sector_closed=q5_str(pZ5_ref),
        p_reset_sector_float=float(pZ5_f),
        mean_return_closed=q5_str(mean_return_ref),
        mean_return_float=float(mean_return_f),
        mean_wait_nonreset_closed=q5_str(ET_ref),
        mean_wait_nonreset_float=float(ET_f),
        lambda_reg=float(lam),
        c_asym=float(c_asym),
        c_ub_search_max_n=int(args.max_n),
        c_ub=float(max_ratio),
        c_ub_argmax_n=int(max_n),
        tau_reg=float(tau_reg),
        t_half=float(t_half),
        Q_closed=Q_closed,
    )

    # ---- Write JSON export ----
    out_json = export_dir() / "real_input_40_reset_regeneration_constants.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(asdict(ex), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # ---- Write TeX snippet ----
    tex_path = generated_dir() / "eq_real_input_40_reset_regeneration_constants.tex"
    tex_path.parent.mkdir(parents=True, exist_ok=True)

    pZ5_tex = r"\frac{9-4\sqrt5}{5}"
    mean_return_tex = tex_q5(mean_return_ref)
    ET_tex = tex_q5(ET_ref)

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_real_input_40_reset_regeneration_constants.py")
    lines.append(r"\begin{proposition}[复位扇区的再生常数（Parry 基线；闭式）]\label{prop:real-input-40-reset-regeneration-constants}")
    lines.append(
        r"在命题 \ref{prop:real-input-40-input-memory-marginal} 的 Parry 基线下取两路独立输入 $(x_k,y_k)\in X\times X$，"
        r"并令 $d_k=x_k+y_k\in\{0,1,2\}$。定义复位扇区事件"
    )
    lines.append(r"\[")
    lines.append(r"Z_{\ge 5}:=\{d_{k-4}d_{k-3}d_{k-2}d_{k-1}d_k=0^5\}.")
    lines.append(r"\]")
    lines.append(r"则其平稳时间占比为闭式常数")
    lines.append(r"\[")
    lines.append(rf"\boxed{{\ \mathbb{{P}}(Z_{{\ge 5}})={pZ5_tex}\approx {pZ5_f:.15f}\ }}.")
    lines.append(r"\]")
    lines.append(r"因此 Kac 平均回返间隔（两次进入 $Z_{\ge 5}$ 之间的平均步数）同样闭式：")
    lines.append(r"\[")
    lines.append(
        rf"\boxed{{\ \mathbb{{E}}[\tau_{{Z_{{\ge 5}}}}]=\frac{{1}}{{\mathbb{{P}}(Z_{{\ge 5}})}}={mean_return_tex}\approx {mean_return_f:.11f}\ }}."
    )
    lines.append(r"\]")
    lines.append(
        r"并且从典型非复位时刻（条件于 $Z_{\ge 5}^c$）到下一次进入 $Z_{\ge 5}$ 的等待时间 $T$ 满足"
    )
    lines.append(r"\[")
    lines.append(rf"\boxed{{\ \mathbb{{E}}[T]={ET_tex}\approx {ET_f:.11f}\ }}.")
    lines.append(r"\]")
    lines.append(r"\end{proposition}")
    lines.append("")
    lines.append(r"\begin{proof}[证明（可审计）]")
    lines.append(
        r"事件 $Z_{\ge 5}$ 等价于 $(x_{k-4},y_{k-4})=\cdots=(x_k,y_k)=(0,0)$。"
        r"在 Parry 基线下 $(x_k)$ 与 $(y_k)$ 为独立的两状态马尔可夫链，且对单边链有 $P(0\to 0)=\varphi^{-1}$。"
        r"因此对二比特链 $P((0,0)\to(0,0))=\varphi^{-2}$；并且由命题 \ref{prop:real-input-40-input-memory-marginal}"
        r" 有 $\mathbb{P}((x_k,y_k)=(0,0))=(3+\sqrt5)/10$。于是"
    )
    lines.append(r"\[")
    lines.append(
        r"\mathbb{P}(Z_{\ge 5})=\mathbb{P}(00)\cdot(\varphi^{-2})^4=\frac{3+\sqrt5}{10}\cdot\varphi^{-8}=\frac{9-4\sqrt5}{5}."
    )
    lines.append(r"\]")
    lines.append(
        r"Kac 公式给出平稳遍历系统中集合 $Z_{\ge 5}$ 的平均回返时间为 $1/\mathbb{P}(Z_{\ge 5})$，从而得到 $\mathbb{E}[\tau_{Z_{\ge 5}}]$ 的闭式。"
    )
    lines.append(
        r"对 $\mathbb{E}[T]$，把输入记忆态与零串长度合并，得到一个 $8$ 状态马尔可夫链；"
        r"把 $Z_{\ge 5}$ 视为命中集合，写出未命中子链的均值方程 $(I-Q)h=\mathbf{1}$，"
        r"并以平稳条件初分布 $\mu(\cdot\mid Z_{\ge 5}^c)$ 加权，即得 $\mathbb{E}[T]=\mu^\mathsf{T}h$。"
        r"上述链、线性方程与闭式均由脚本一键复算。"
    )
    lines.append(r"\end{proof}")
    lines.append("")
    lines.append(r"\begin{proposition}[等待时间的严格指数尾界（Perron 根）]\label{prop:real-input-40-reset-regeneration-tail}")
    lines.append(
        r"在命题 \ref{prop:real-input-40-reset-regeneration-constants} 的记号下，"
        r"令 $Q$ 为上述 $8$ 状态链在非复位扇区 $Z_{\ge 5}^c$ 上诱导的 $7\times 7$ 子马尔可夫矩阵，"
        r"并令 $\mu$ 为平稳条件初分布（条件于 $Z_{\ge 5}^c$）。则对所有 $n\ge 0$ 有"
    )
    lines.append(r"\[")
    lines.append(r"\mathbb{P}(T>n)=\mu^\mathsf{T}Q^n\mathbf{1}.")
    lines.append(r"\]")
    lines.append(r"在状态顺序 $(01,10,11,00^1,00^2,00^3,00^4)$ 下，$Q$ 的稀疏形为")
    lines.append(r"\[")
    lines.append(r"Q=\begin{pmatrix}")
    lines.append(r"0 & \varphi^{-2} & 0 & \varphi^{-1} & 0 & 0 & 0\\")
    lines.append(r"\varphi^{-2} & 0 & 0 & \varphi^{-1} & 0 & 0 & 0\\")
    lines.append(r"0 & 0 & 0 & 1 & 0 & 0 & 0\\")
    lines.append(r"\varphi^{-3} & \varphi^{-3} & \varphi^{-4} & 0 & \varphi^{-2} & 0 & 0\\")
    lines.append(r"\varphi^{-3} & \varphi^{-3} & \varphi^{-4} & 0 & 0 & \varphi^{-2} & 0\\")
    lines.append(r"\varphi^{-3} & \varphi^{-3} & \varphi^{-4} & 0 & 0 & 0 & \varphi^{-2}\\")
    lines.append(r"\varphi^{-3} & \varphi^{-3} & \varphi^{-4} & 0 & 0 & 0 & 0")
    lines.append(r"\end{pmatrix}.")
    lines.append(r"\]")
    lines.append(
        r"并且 $Q$ 原始，存在 Perron 根 $\lambda_{\mathrm{reg}}=\rho(Q)\in(0,1)$ 及常数 $c_{\mathrm{asym}}>0$ 使得"
    )
    lines.append(r"\[")
    lines.append(
        rf"\mathbb{{P}}(T>n)\sim c_{{\mathrm{{asym}}}}\lambda_{{\mathrm{{reg}}}}^n,\qquad"
        rf"\lambda_{{\mathrm{{reg}}}}\approx {lam:.14f},\quad c_{{\mathrm{{asym}}}}\approx {c_asym:.14f}."
    )
    lines.append(r"\]")
    lines.append(
        r"相应的再生时间常数与半衰期为"
        rf"\(\tau_{{\mathrm{{reg}}}}:=1/(-\log\lambda_{{\mathrm{{reg}}}})\approx {tau_reg:.10f}\)、"
        rf"\(t_{{1/2}}:=(\log 2)/(-\log\lambda_{{\mathrm{{reg}}}})\approx {t_half:.10f}\)。"
    )
    lines.append(
        r"此外，由谱分解可知存在常数 $C_{\mathrm{reg}}<\infty$ 使得对所有 $n\ge 0$ 有 $\mathbb{P}(T>n)\le C_{\mathrm{reg}}\lambda_{\mathrm{reg}}^n$。"
        rf"数值上，脚本在 $0\le n\le {int(args.max_n)}$ 的范围内搜索得到一组可取的上界常数"
        rf" $C_{{\mathrm{{reg}}}}\approx {max_ratio:.14f}$（在 $n={max_n}$ 处达到该搜索上界）。"
    )
    lines.append(r"\end{proposition}")
    lines.append("")
    lines.append(r"\begin{corollary}[由复位机制导出的相关上界（无同步核谱隙假设）]\label{cor:real-input-40-reset-regeneration-cov-bound}")
    lines.append(
        r"在 Parry 平稳态下，令 $(S_k)$ 为真实输入核的状态过程（同步核内部状态与输入记忆的合成），"
        r"并令 $F_k=f(S_k)$ 为任意有界可观测（例如任意有限窗口函数）。则对所有 $n\ge 0$ 有"
    )
    lines.append(r"\[")
    lines.append(
        r"\bigl|\mathrm{Cov}(F_0,F_n)\bigr|\le 2\norm{f}_\infty^2\,\mathbb{P}(T>n)"
        r"\ \le\ 2C_{\mathrm{reg}}\norm{f}_\infty^2\,\lambda_{\mathrm{reg}}^n."
    )
    lines.append(r"\]")
    lines.append(r"\end{corollary}")
    lines.append("")
    lines.append(r"\begin{proof}[证明（思路）]")
    lines.append(
        r"$Z_{\ge 5}$ 为原子再生扇区：一旦出现 $0^5$，同步核内部状态被复位为同一态（命题 \ref{prop:real-input-40-reset-word}），"
        r"并且输入记忆亦处于确定的 $(0,0)$。因此在再生时刻之后，系统未来演化的条件分布与再生前的历史无关。"
        r"以 $T$ 表示从典型非复位时刻到下一次进入 $Z_{\ge 5}$ 的等待时间，则依赖性只能来自异常事件 $\{T>n\}$。"
        r"结合有界性与耦合/全变差界可得第一条不等式；第二条不等式由命题 \ref{prop:real-input-40-reset-regeneration-tail} 给出。"
    )
    lines.append(r"\end{proof}")
    lines.append("")

    tex_path.write_text("\n".join(lines), encoding="utf-8")

    print(
        "[reset_regen] wrote artifacts/export/real_input_40_reset_regeneration_constants.json and "
        "sections/generated/eq_real_input_40_reset_regeneration_constants.tex",
        flush=True,
    )


if __name__ == "__main__":
    main()

