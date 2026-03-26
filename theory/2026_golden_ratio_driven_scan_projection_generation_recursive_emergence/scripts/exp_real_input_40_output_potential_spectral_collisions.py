#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Spectral collision / degeneracy audit for the real-input 40-state kernel (output potential only).

We use the explicit factorization:
  Delta(z,u) = det(I - z M(u)) = (1 - u z^2) * Q(z,u)
with Q(z,u) of degree 8 in z (degree drops to 7 at u=1).

This script produces fully-auditable algebraic checks:
  1) Closed-form evaluations:
     - Q(±1/sqrt(u), u)  (collision with the explicit ±sqrt(u) branch)
     - Q(±1, u)          (exact ±1 eigenvalue resonance points)
  2) The z-resultant:
       Res_z(Q, dQ/dz)
     factorization and the irreducible degree-14 factor D(u) governing true Q-degeneracies.
  3) Positive real roots of D(u) and the corresponding real double root z*(u)
     (and the double eigenvalue lambda*=1/z*).

Outputs:
  - artifacts/export/real_input_40_output_potential_spectral_collisions.json
  - sections/generated/eq_real_input_40_output_potential_spectral_collision_identities.tex
  - sections/generated/tab_real_input_40_output_potential_spectral_collision_roots.tex

All terminal output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class RootRow:
    u: str
    z_double: str
    lambda_double: str


@dataclass(frozen=True)
class SpectralCollisionsReport:
    # Factor identities (SymPy string forms)
    Q_pos_sqrtu: str
    Q_neg_sqrtu: str
    Q_at_1: str
    Q_at_minus1: str
    Q_u1_factor: str
    # Resultant factorization
    resultant: str
    resultant_factorization: str
    D_u: str
    D_degree: int
    D_coeffs_descending: List[str]
    # Positive real roots of D and corresponding double roots
    positive_real_roots_count: int
    roots: List[RootRow]


class _Progress:
    def __init__(self, *, enabled: bool, every_seconds: float, prefix: str = "[spectral-collisions]") -> None:
        self._enabled = enabled and every_seconds > 0
        self._every_seconds = float(every_seconds)
        self._prefix = prefix
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._t0 = 0.0

    def start(self, msg: str) -> None:
        if not self._enabled:
            return
        self._t0 = time.time()
        print(f"{self._prefix} {msg}", flush=True)

        def _run() -> None:
            while not self._stop.wait(self._every_seconds):
                dt = time.time() - self._t0
                print(f"{self._prefix} still running... elapsed={dt:.1f}s", flush=True)

        self._thread = threading.Thread(target=_run, name="progress", daemon=True)
        self._thread.start()

    def stop(self, msg: str) -> None:
        if not self._enabled:
            return
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=1.0)
        dt = time.time() - self._t0
        print(f"{self._prefix} {msg} elapsed={dt:.1f}s", flush=True)


def _build_Q(z: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/real_input/app__real-input-40-zeta-u.tex`.
    return (
        sp.Integer(1)
        - z
        - 6 * u * z**2
        + 2 * u * z**3
        + (9 * u**2 - u) * z**4
        + (u - 3 * u**2) * z**5
        - (u**3 + 2 * u**2) * z**6
        + (4 * u**3 - 3 * u**2) * z**7
        + (u**3 - u**4) * z**8
    )


def _positive_real_roots(poly: sp.Poly, *, digits: int, maxsteps: int) -> List[sp.Expr]:
    roots = sp.nroots(poly, n=digits, maxsteps=maxsteps)
    out: List[sp.Expr] = []
    for r in roots:
        if abs(sp.im(r)) < sp.Float("1e-40") and sp.re(r) > 0:
            out.append(sp.re(r))
    return sorted(out)


def _double_root_for_u(
    Q: sp.Expr, z: sp.Symbol, u: sp.Symbol, uk: sp.Expr, *, digits: int, maxsteps: int
) -> sp.Expr:
    # Identify the double root z*(uk) via Q_z(z,uk)=0 (simple root there),
    # selecting the candidate that minimizes |Q(z,uk)|.
    Qz = sp.diff(Q, z)
    ukN = sp.N(uk, digits)

    Qzuk = sp.Poly(Qz.subs(u, ukN), z)
    try:
        zcand = sp.nroots(Qzuk, n=digits, maxsteps=maxsteps)
    except Exception:
        # Multiple roots are ill-conditioned; retry with lower precision.
        zcand = sp.nroots(Qzuk, n=max(40, min(60, digits)), maxsteps=maxsteps * 2)

    best: Optional[sp.Expr] = None
    best_val: Optional[sp.Expr] = None
    for zr in zcand:
        val = abs(sp.N(Q.subs({u: ukN, z: zr}), digits))
        if best is None or val < best_val:  # type: ignore[operator]
            best = zr
            best_val = val

    if best is None:
        raise RuntimeError("Failed to locate double root candidate (from Q_z roots).")

    # Snap tiny imaginary parts to 0 for readability.
    if abs(sp.im(best)) < sp.Float("1e-25"):
        return sp.re(best)
    return best


def _tex_identities(path: Path, *, Q: sp.Expr, z: sp.Symbol, u: sp.Symbol, D: sp.Expr) -> None:
    def _poly_multiline_tex(expr: sp.Expr, var: sp.Symbol, *, max_line_len: int = 110) -> List[str]:
        """Format a univariate integer polynomial as multiple TeX lines.

        Output lines are meant to be used inside an amsmath aligned environment.
        """
        P = sp.Poly(sp.expand(expr), var)
        terms = []
        for (e,), coeff in sorted(P.as_dict().items(), key=lambda kv: -int(kv[0][0])):
            coeff = sp.Integer(coeff)
            if coeff == 0:
                continue
            if e == 0:
                terms.append(coeff)
            else:
                terms.append(coeff * (var ** int(e)))

        if not terms:
            return ["0"]

        parts: List[str] = []
        for idx, t in enumerate(terms):
            t = sp.expand(t)
            sign = -1 if t.could_extract_minus_sign() else 1
            t_abs = -t if sign < 0 else t
            tex = sp.latex(t_abs)
            if idx == 0:
                parts.append(("- " + tex) if sign < 0 else tex)
            else:
                parts.append(("- " + tex) if sign < 0 else ("+ " + tex))

        lines_out: List[str] = []
        cur = parts[0]
        for p in parts[1:]:
            if len(cur) + 1 + len(p) > max_line_len:
                lines_out.append(cur)
                cur = p
            else:
                cur = cur + " " + p
        lines_out.append(cur)
        return lines_out

    r = sp.Symbol("r")
    Q_pos = sp.factor(Q.subs({u: r**2, z: 1 / r})).subs(r, sp.sqrt(u))
    Q_neg = sp.factor(Q.subs({u: r**2, z: -1 / r})).subs(r, sp.sqrt(u))
    Q_1 = sp.factor(Q.subs(z, 1))
    Q_m1 = sp.factor(Q.subs(z, -1))
    Q_u1 = sp.factor(Q.subs(u, 1))
    Z, U = sp.symbols("Z U")
    local_expand = sp.expand(Q.subs({z: -1 + Z, u: 1 + U}))
    local_quadratic = sp.expand(
        sum(
            local_expand.coeff(Z, i).coeff(U, j) * Z**i * U**j
            for i in range(3)
            for j in range(3)
            if i + j == 2
        )
    )
    alpha = sp.Symbol("alpha")
    beta = sp.Symbol("beta")
    gamma = sp.Symbol("gamma")
    branch_series = sp.expand(
        Q.subs({z: -1 + alpha * U + beta * U**2 + gamma * U**3, u: 1 + U})
    )
    alpha_roots = sorted(
        sp.solve(sp.Eq(sp.expand(branch_series).coeff(U, 2), 0), alpha),
        key=lambda expr: sp.N(expr),
    )
    alpha_minus, alpha_plus = alpha_roots
    beta_minus = sp.solve(
        sp.Eq(sp.expand(branch_series.subs(alpha, alpha_minus)).coeff(U, 3), 0),
        beta,
    )[0]
    beta_plus = sp.solve(
        sp.Eq(sp.expand(branch_series.subs(alpha, alpha_plus)).coeff(U, 3), 0),
        beta,
    )[0]
    gamma_minus = sp.solve(
        sp.Eq(
            sp.expand(branch_series.subs({alpha: alpha_minus, beta: beta_minus})).coeff(U, 4),
            0,
        ),
        gamma,
    )[0]
    gamma_plus = sp.solve(
        sp.Eq(
            sp.expand(branch_series.subs({alpha: alpha_plus, beta: beta_plus})).coeff(U, 4),
            0,
        ),
        gamma,
    )[0]

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_output_potential_spectral_collisions.py")
    lines.append("\\begin{proposition}[可追踪谱支的碰撞与 $Q$-谱退化（可审计）]")
    lines.append("\\label{prop:real-input-40-output-spectral-collisions}")
    lines.append("在真实输入 $40$ 状态核的输出位势加权下，")
    lines.append("取 $\\Delta(z,u)=(1-uz^2)Q(z,u)$。则有以下恒等式与判别：")
    lines.append("\\begin{enumerate}")
    lines.append("  \\item \\textbf{与显式分支 $z=\\pm 1/\\sqrt u$ 的真正碰撞：}")
    lines.append("  \\[")
    lines.append("  Q\\!\\left(\\frac{1}{\\sqrt u},u\\right)=" + sp.latex(sp.simplify(Q_pos)) + ",\\qquad")
    lines.append("  Q\\!\\left(-\\frac{1}{\\sqrt u},u\\right)=" + sp.latex(sp.simplify(Q_neg)) + ".")
    lines.append("  \\]")
    lines.append("  因而在 $u>0$ 上，$Q(\\pm 1/\\sqrt u,u)=0$ 当且仅当 $u=1$。")
    lines.append("  特别地 $u=1$ 时")
    lines.append("  \\[")
    lines.append("  Q(z,1)=" + sp.latex(Q_u1) + ",")
    lines.append("  \\]")
    lines.append("  从而 $z=1$ 为单根、$z=-1$ 为二重根。")
    lines.append("")
    lines.append("  \\item \\textbf{整数级共振点：}在 $z=\\pm 1$ 处有")
    lines.append("  \\[")
    lines.append("  Q(1,u)=" + sp.latex(Q_1) + ",\\qquad Q(-1,u)=" + sp.latex(Q_m1) + ".")
    lines.append("  \\]")
    lines.append("  因此在正参数域内，$u=4$ 时出现精确本征值 $\\lambda=1$；")
    lines.append("  $u=-3+\\sqrt{11}$ 时出现精确本征值 $\\lambda=-1$。")
    lines.append("")
    lines.append("  \\item \\textbf{$Q$ 的谱退化（重根）判别式：}令 $Q_z=\\partial Q/\\partial z$。则结式满足")
    lines.append("  \\[")
    lines.append("  \\begin{aligned}")
    lines.append("  \\mathrm{Res}_z(Q,Q_z)&=4u^{15}(u-1)^3\\,D(u),\\\\")
    d_lines = _poly_multiline_tex(D, u, max_line_len=75)
    if len(d_lines) == 1:
        lines.append("  D(u)&=" + d_lines[0] + ",")
    else:
        lines.append("  D(u)&=" + d_lines[0] + "\\\\")
        for ln in d_lines[1:-1]:
            lines.append("  &" + ln + "\\\\")
        lines.append("  &" + d_lines[-1] + ",")
    lines.append("  \\end{aligned}")
    lines.append("  \\]")
    lines.append("  其中 $D(u)\\in\\mathbb{Z}[u]$ 为次数 $" + str(sp.degree(D, u)) + "$ 的不可约多项式。")
    lines.append("  因而在 $u>0$ 上，除 $u=1$ 外，$Q$ 出现重根当且仅当 $D(u)=0$。")
    lines.append("\\end{enumerate}")
    lines.append("\\end{proposition}")
    lines.append("")
    lines.append("\\begin{proposition}[单位圆奇异环处的手性接触阶]\\label{prop:real-input-40-singular-ring-contact-order}")
    lines.append("沿用命题 \\ref{prop:real-input-40-output-spectral-collisions} 的记号，并定义两条可追踪分支")
    lines.append("\\[")
    lines.append("z_{\\mathrm{tr}}^{\\pm}(u):=\\pm u^{-1/2}.")
    lines.append("\\]")
    lines.append("则在 $u=1$ 处有")
    lines.append("\\[")
    lines.append("\\operatorname{ord}_{u=1}Q\\bigl(z_{\\mathrm{tr}}^{+}(u),u\\bigr)=1,")
    lines.append("\\qquad")
    lines.append("\\operatorname{ord}_{u=1}Q\\bigl(z_{\\mathrm{tr}}^{-}(u),u\\bigr)=2.")
    lines.append("\\]")
    lines.append("亦即，$z_{\\mathrm{tr}}^{+}$ 以横截方式穿过残谱曲线 $Q(z,u)=0$，而 $z_{\\mathrm{tr}}^{-}$ 在单位圆点 $z=-1$ 处呈现二阶接触。")
    lines.append("\\end{proposition}")
    lines.append("\\begin{proof}")
    lines.append("命题 \\ref{prop:real-input-40-output-spectral-collisions} 已给出")
    lines.append("\\[")
    lines.append("Q\\!\\left(\\frac{1}{\\sqrt u},u\\right)=" + sp.latex(sp.simplify(Q_pos)) + ",\\qquad")
    lines.append("Q\\!\\left(-\\frac{1}{\\sqrt u},u\\right)=" + sp.latex(sp.simplify(Q_neg)) + ".")
    lines.append("\\]")
    lines.append("由于第一式在 $u=1$ 处仅含一阶因子 $(\\sqrt u-1)$，而第二式在 $u=1$ 处含二阶因子 $(\\sqrt u-1)^2$，故两条接触阶分别为 $1$ 与 $2$。证毕。")
    lines.append("\\end{proof}")
    lines.append("")
    lines.append("\\begin{theorem}[单位圆双根在 $u=1$ 邻域的解析裂解与斜率场]\\label{thm:real-input-40-singular-ring-node-splitting}")
    lines.append("在点 $(z,u)=(-1,1)$ 的某邻域内，方程 $Q(z,u)=0$ 恰分裂为两条互异解析根分支 $z_+(u),z_-(u)$，满足")
    lines.append("\\[")
    lines.append("z_\\pm(1)=-1,\\qquad Q(z_\\pm(u),u)\\equiv 0,")
    lines.append("\\]")
    lines.append("并且在 $u=1$ 处具有展开")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append("z_\\pm(u)")
    lines.append("&=-1+\\alpha_\\pm (u-1)+\\beta_\\pm (u-1)^2+\\gamma_\\pm (u-1)^3+O\\bigl((u-1)^4\\bigr),")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append("其中")
    lines.append("\\[")
    lines.append("\\alpha_\\pm=\\frac{17\\pm\\sqrt{89}}{20},\\qquad")
    lines.append("\\beta_\\pm=-\\frac{23}{16}\\mp\\frac{179\\sqrt{89}}{1424},\\qquad")
    lines.append("\\gamma_\\pm=\\frac{64969}{20000}\\pm\\frac{51245797\\sqrt{89}}{158420000}.")
    lines.append("\\]")
    lines.append("特别地，局部切向方向由两条互异实斜率 $\\alpha_\\pm$ 控制，其判别式恰为 $89$。")
    lines.append("\\end{theorem}")
    lines.append("\\begin{proof}")
    lines.append("令局部坐标 $Z:=z+1$ 与 $U:=u-1$。把 $Q(-1+Z,1+U)$ 在 $(Z,U)=(0,0)$ 处展开，得到")
    lines.append("\\[")
    lines.append("Q(-1+Z,1+U)=" + sp.latex(local_quadratic) + "+O\\bigl(|(Z,U)|^3\\bigr).")
    lines.append("\\]")
    lines.append("等价地，二次主部为")
    lines.append("\\[")
    lines.append("-(10Z^2-17ZU+5U^2).")
    lines.append("\\]")
    lines.append("因此切锥由二次方程 $10Z^2-17ZU+5U^2=0$ 给出，斜率满足")
    lines.append("\\[")
    lines.append("Z=\\alpha_\\pm U,\\qquad \\alpha_\\pm=\\frac{17\\pm\\sqrt{89}}{20}.")
    lines.append("\\]")
    lines.append("由于判别式 $89>0$，该奇点为普通结点，零集在邻域内分裂为两条解析曲线。")
    lines.append("再设")
    lines.append("\\[")
    lines.append("Z_\\pm(U)=\\alpha_\\pm U+\\beta_\\pm U^2+\\gamma_\\pm U^3+O(U^4),")
    lines.append("\\]")
    lines.append("逐阶代回恒等式 $Q(-1+Z_\\pm(U),1+U)=0$ 并比较 $U^2,U^3,U^4$ 的系数，便唯一得到上述 $\\beta_\\pm,\\gamma_\\pm$。证毕。")
    lines.append("\\end{proof}")
    lines.append("")
    lines.append("\\begin{corollary}[未加权点处 $\\pm1$ 特征值的高重数与一阶漂移谱]\\label{cor:real-input-40-singular-ring-eigenvalue-drift}")
    lines.append("令 $M(u)$ 为满足 $\\Delta(z,u)=\\det(I-zM(u))$ 的碰撞位势矩阵。则当 $u=1$ 时，特征值 $+1$ 的代数重数为 $2$，特征值 $-1$ 的代数重数为 $3$。")
    lines.append("并且穿过 $\\lambda=-1$ 的三条特征值分支在 $u=1$ 处的一阶导数互异，具体为")
    lines.append("\\[")
    lines.append("\\frac{\\mathrm d}{\\mathrm du}\\bigl(-\\sqrt u\\bigr)\\Big|_{u=1}=-\\frac12,")
    lines.append("\\qquad")
    lines.append("\\lambda_\\pm'(1)=-\\alpha_\\pm.")
    lines.append("\\]")
    lines.append("\\end{corollary}")
    lines.append("\\begin{proof}")
    lines.append("由")
    lines.append("\\[")
    lines.append("\\Delta(z,u)=(1-uz^2)Q(z,u)")
    lines.append("\\]")
    lines.append("与命题 \\ref{prop:real-input-40-output-spectral-collisions} 中")
    lines.append("\\[")
    lines.append("Q(z,1)=(z-1)(z+1)^2(z^2-3z+1)(z^2-z-1)")
    lines.append("\\]")
    lines.append("可直接读出 $z=1$ 为单根、$z=-1$ 为三重零点中的二重部分来自 $Q$，另一个来自因子 $1-z^2$，从而对应特征值 $+1$ 与 $-1$ 的代数重数分别为 $2$ 与 $3$。")
    lines.append("再由 $\\lambda(u)=1/z(u)$ 在 $z(1)=-1$ 处满足")
    lines.append("\\[")
    lines.append("\\lambda'(1)=-\\frac{z'(1)}{z(1)^2}=-z'(1),")
    lines.append("\\]")
    lines.append("并结合定理 \\ref{thm:real-input-40-singular-ring-node-splitting} 的 $z_\\pm'(1)=\\alpha_\\pm$，即可得到 $\\lambda_\\pm'(1)=-\\alpha_\\pm$。证毕。")
    lines.append("\\end{proof}")
    lines.append("")
    lines.append("\\begin{conjecture}[奇异环结点判别式的 Fibonacci 指纹]\\label{conj:real-input-40-singular-ring-fibonacci-discriminant}")
    lines.append("在由 Fibonacci 替换动力学诱导的在线归一化同步核族中，若残谱因子在单位圆完成点出现二重根并形成普通结点，则其最小二次主部的判别式应落在奇指标 Fibonacci 数集合")
    lines.append("\\[")
    lines.append("\\{F_{2k+1}:k\\ge 0\\}")
    lines.append("\\]")
    lines.append("内。对当前模型，定理 \\ref{thm:real-input-40-singular-ring-node-splitting} 给出的判别式为")
    lines.append("\\[")
    lines.append("89=F_{11},")
    lines.append("\\]")
    lines.append("因而局部切向场落在二次域 $\\mathbb Q(\\sqrt{89})=\\mathbb Q(\\sqrt{F_{11}})$ 中，可视为该算术指纹现象的首个证据点。")
    lines.append("\\end{conjecture}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _tex_table(path: Path, rows: List[Tuple[sp.Expr, sp.Expr, sp.Expr]]) -> None:
    # rows are (u, z_double, lambda_double)
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_output_potential_spectral_collisions.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Positive real degeneracy parameters $u$ (roots of $D(u)$) and the associated real double root $z_\\ast$ of $Q(z,u)$, with the double eigenvalue $\\lambda_\\ast=1/z_\\ast$.}"
    )
    lines.append("\\label{tab:real_input_40_output_potential_spectral_collision_roots}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$u$ & $z_\\ast$ (double root) & $\\lambda_\\ast=1/z_\\ast$ \\\\")
    lines.append("\\midrule")
    for uk, zk, lk in rows:
        lines.append(
            f"${sp.N(uk, 20)}$ & ${sp.N(zk, 14)}$ & ${sp.N(lk, 14)}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Spectral collision / degeneracy audit for real-input 40-state kernel (output potential)."
    )
    parser.add_argument(
        "--digits",
        type=int,
        default=80,
        help="Working precision (digits) for nroots computations.",
    )
    parser.add_argument(
        "--maxsteps",
        type=int,
        default=200,
        help="Max steps for nroots.",
    )
    parser.add_argument(
        "--progress-seconds",
        type=float,
        default=20.0,
        help="Print a heartbeat progress line every N seconds (0 disables).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_output_potential_spectral_collisions.json"),
    )
    parser.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(
            generated_dir()
            / "eq_real_input_40_output_potential_spectral_collision_identities.tex"
        ),
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(
            generated_dir()
            / "tab_real_input_40_output_potential_spectral_collision_roots.tex"
        ),
    )
    args = parser.parse_args()

    digits = int(args.digits)
    maxsteps = int(args.maxsteps)

    prog = _Progress(enabled=(args.progress_seconds > 0), every_seconds=float(args.progress_seconds))
    prog.start("starting symbolic derivation (resultant + factorization)")

    z, u = sp.symbols("z u")
    Q = _build_Q(z, u)
    Qz = sp.diff(Q, z)

    try:
        Res = sp.resultant(sp.Poly(Q, z), sp.Poly(Qz, z), z)
        coef, factors = sp.factor_list(Res, u)
        # Reconstruct the fully-factored form for TeX.
        res_factor = sp.Integer(coef)
        D = sp.Integer(1)
        exp_u = 0
        exp_um1 = 0
        for f, e in factors:
            if f == u:
                exp_u = e
                res_factor *= u ** e
            elif f == u - 1:
                exp_um1 = e
                res_factor *= (u - 1) ** e
            else:
                res_factor *= f ** e
                D *= f ** e
        D = sp.factor(D)
        Dpoly = sp.Poly(D, u)
    finally:
        prog.stop("symbolic derivation finished")

    # Factor identities
    r = sp.Symbol("r")
    Q_pos_sqrtu = sp.factor(Q.subs({u: r**2, z: 1 / r})).subs(r, sp.sqrt(u))
    Q_neg_sqrtu = sp.factor(Q.subs({u: r**2, z: -1 / r})).subs(r, sp.sqrt(u))
    Q_at_1 = sp.factor(Q.subs(z, 1))
    Q_at_minus1 = sp.factor(Q.subs(z, -1))
    Q_u1_factor = sp.factor(Q.subs(u, 1))

    print(f"[spectral-collisions] Res factor exponents: u^{exp_u} (u-1)^{exp_um1}", flush=True)
    print(f"[spectral-collisions] D degree={Dpoly.degree()}", flush=True)

    # Roots of D and corresponding double roots.
    prog.start("computing positive real roots of D(u) and double roots z*")
    try:
        pos_roots = _positive_real_roots(Dpoly, digits=digits, maxsteps=maxsteps)
        rows_numeric: List[Tuple[sp.Expr, sp.Expr, sp.Expr]] = []
        rows_json: List[RootRow] = []
        for uk in pos_roots:
            zk = _double_root_for_u(Q, z, u, uk, digits=digits, maxsteps=maxsteps)
            lk = sp.simplify(1 / zk)
            rows_numeric.append((uk, zk, lk))
            rows_json.append(
                RootRow(
                    u=str(sp.N(uk, 24)),
                    z_double=str(sp.N(zk, 24)),
                    lambda_double=str(sp.N(lk, 24)),
                )
            )
    finally:
        prog.stop("root computations finished")

    # JSON report
    report = SpectralCollisionsReport(
        Q_pos_sqrtu=str(sp.simplify(Q_pos_sqrtu)),
        Q_neg_sqrtu=str(sp.simplify(Q_neg_sqrtu)),
        Q_at_1=str(Q_at_1),
        Q_at_minus1=str(Q_at_minus1),
        Q_u1_factor=str(Q_u1_factor),
        resultant=str(Res),
        resultant_factorization=str(res_factor),
        D_u=str(D),
        D_degree=int(Dpoly.degree()),
        D_coeffs_descending=[str(c) for c in Dpoly.all_coeffs()],
        positive_real_roots_count=len(pos_roots),
        roots=rows_json,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(report), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[spectral-collisions] wrote {jout}", flush=True)

    # TeX outputs
    _tex_identities(Path(args.tex_eq_out), Q=Q, z=z, u=u, D=D)
    print(f"[spectral-collisions] wrote {args.tex_eq_out}", flush=True)
    _tex_table(Path(args.tex_tab_out), rows_numeric)
    print(f"[spectral-collisions] wrote {args.tex_tab_out}", flush=True)


if __name__ == "__main__":
    main()

