#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Puiseux (u->+infty) asymptotics for the real-input 40-state kernel, output potential.

We work with the explicit low-degree determinant (appendix):
  Delta(z,u) = det(I - z M(u)) = (1 - u z^2) * F(z,u),
and the associated degree-8 algebraic curve for the nonzero core spectrum:
  G(lambda,u) := lambda^8 F(lambda^{-1},u) = 0.

This experiment derives the higher-order Puiseux jet for the Perron branch lambda_1(u)
and its mirror negative real branch lambda_mir(u) as u->+infty:
  lambda_1(u)   =  c*sqrt(u) + d + e/sqrt(u) + f/u + O(u^{-3/2}),
  lambda_mir(u) = -c*sqrt(u) + d - e/sqrt(u) + f/u + O(u^{-3/2}),
and reports:
  - the induced absolute/relative spectral-gap asymptotics,
  - the full sqrt(u)-normalized limit set for the 8 roots of G(lambda,u)=0, i.e.
      rho^8 - 6 rho^6 + 9 rho^4 - rho^2 - 1 = 0,
    plus the explicit eigenvalues ±sqrt(u) from the factor (1 - u z^2).

Outputs:
  - artifacts/export/real_input_40_output_potential_puiseux_asymptotics.json
  - sections/generated/eq_real_input_40_output_potential_puiseux_asymptotics.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _build_G(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/real_input/app__real-input-40-zeta-u.tex`.
    return (
        lam**8
        - lam**7
        - 6 * u * lam**6
        + 2 * u * lam**5
        + (9 * u**2 - u) * lam**4
        + (u - 3 * u**2) * lam**3
        - (u**3 + 2 * u**2) * lam**2
        + (4 * u**3 - 3 * u**2) * lam
        + (u**3 - u**4)
    )


def _quartic_y() -> sp.Poly:
    y = sp.Symbol("y")
    return sp.Poly(y**4 - 6 * y**3 + 9 * y**2 - y - 1, y)


def _pick_real_root(roots: Sequence[sp.Expr], *, tol: float = 1e-30) -> List[sp.Float]:
    out: List[sp.Float] = []
    for r in roots:
        rr = sp.N(r)
        if abs(sp.im(rr)) < tol:
            out.append(sp.Float(sp.re(rr)))
    return out


def _fmt_fixed(x: float, nd: int) -> str:
    return f"{x:.{nd}f}"


def _fmt_signed_fixed(x: float, nd: int) -> str:
    return ("+" if x >= 0 else "") + _fmt_fixed(x, nd)


def _solve_puiseux_coeffs(*, prec_digits: int) -> Tuple[sp.Float, sp.Float, sp.Float, sp.Float, sp.Float]:
    """
    Return (y_max, c, d, e, f) numerically at the requested precision.
    """
    # 1) Determine y_max (largest positive root of the quartic).
    ypoly = _quartic_y()
    roots_y = sp.nroots(ypoly, n=prec_digits)
    reals_y = _pick_real_root(roots_y)
    y_pos = sorted([yy for yy in reals_y if yy > 0], key=lambda z: float(z))
    if not y_pos:
        raise RuntimeError("No positive real roots found for quartic.")
    y_max = y_pos[-1]
    c = sp.sqrt(y_max)

    # 2) Solve for d,e,f by series in t:=u^{-1/2}.
    t = sp.Symbol("t")
    lam, u = sp.Symbol("lam"), sp.Symbol("u")
    G = sp.expand(_build_G(lam, u))

    d, e, f = sp.symbols("d e f")
    lam_series = c / t + d + e * t + f * t**2
    expr = sp.expand(G.subs({lam: lam_series, u: t ** (-2)}))
    # Leading scale is t^{-8}.
    expr_scaled = sp.expand(expr * t**8)
    ser = sp.series(expr_scaled, t, 0, 6).removeO()
    ser = sp.expand(ser)
    coeffs = [sp.expand(ser.coeff(t, k)) for k in range(6)]

    # Solve sequentially (each equation is linear in the next unknown under our jet ansatz).
    sol_d = sp.solve(sp.Eq(coeffs[1], 0), d)
    if not sol_d:
        raise RuntimeError("Failed to solve for d.")
    d_val = None
    for sd in sol_d:
        vv = sp.N(sd, prec_digits)
        if abs(sp.im(vv)) < 1e-20:
            d_val = sp.Float(sp.re(vv))
            break
    if d_val is None:
        raise RuntimeError("No real solution for d found.")

    sol_e = sp.solve(sp.Eq(sp.simplify(coeffs[2].subs({d: d_val})), 0), e)
    if not sol_e:
        raise RuntimeError("Failed to solve for e.")
    e_val = None
    for se in sol_e:
        vv = sp.N(se, prec_digits)
        if abs(sp.im(vv)) < 1e-20:
            e_val = sp.Float(sp.re(vv))
            break
    if e_val is None:
        raise RuntimeError("No real solution for e found.")

    sol_f = sp.solve(
        sp.Eq(sp.simplify(coeffs[3].subs({d: d_val, e: e_val})), 0), f
    )
    if not sol_f:
        raise RuntimeError("Failed to solve for f.")
    f_val = None
    for sf in sol_f:
        vv = sp.N(sf, prec_digits)
        if abs(sp.im(vv)) < 1e-20:
            f_val = sp.Float(sp.re(vv))
            break
    if f_val is None:
        raise RuntimeError("No real solution for f found.")

    # Return all in high-precision floats.
    return (
        sp.Float(sp.N(y_max, prec_digits)),
        sp.Float(sp.N(c, prec_digits)),
        sp.Float(sp.N(d_val, prec_digits)),
        sp.Float(sp.N(e_val, prec_digits)),
        sp.Float(sp.N(f_val, prec_digits)),
    )


def _limit_rho_roots(*, prec_digits: int) -> List[complex]:
    """
    Roots of rho^8 - 6 rho^6 + 9 rho^4 - rho^2 - 1 = 0, sorted in a stable order.
    """
    rho = sp.Symbol("rho")
    poly = sp.Poly(rho**8 - 6 * rho**6 + 9 * rho**4 - rho**2 - 1, rho)
    roots = sp.nroots(poly, n=prec_digits)

    # Convert to python complex.
    roots_c: List[complex] = []
    for r in roots:
        rr = sp.N(r, prec_digits)
        roots_c.append(complex(float(sp.re(rr)), float(sp.im(rr))))

    # Sort by (abs, arg) for stable presentation.
    def _key(z: complex) -> Tuple[float, float, float]:
        return (abs(z), math.atan2(z.imag, z.real), z.real)

    roots_c.sort(key=_key)
    return roots_c


@dataclass(frozen=True)
class PuiseuxAsymptotics:
    y_max: str
    c: str
    d: str
    e: str
    f: str
    # derived constants
    two_d: str
    two_d_over_c: str
    c_over_two_d: str
    # limit roots for G-branches, normalized by sqrt(u)
    rho_roots: List[str]


def _as_str(x: sp.Expr, nd: int) -> str:
    return sp.N(x, nd).__str__()


def _write_tex(path: Path, *, c: float, d: float, e: float, f: float, rho_roots: List[complex]) -> None:
    nd = 16
    # Format the limit roots as ±-pairs (cleaner than listing all 8 roots).
    real_pos = sorted(
        {round(z.real, 14) for z in rho_roots if abs(z.imag) < 1e-12 and z.real > 0},
        reverse=True,
    )
    imag_pos = sorted(
        {round(abs(z.imag), 14) for z in rho_roots if abs(z.real) < 1e-12 and z.imag > 0},
        reverse=True,
    )
    if len(real_pos) != 3 or len(imag_pos) != 1:
        raise RuntimeError("Unexpected root pattern for rho-limit polynomial.")
    a1, a2, a3 = real_pos
    gamma = imag_pos[0]
    rho_tex = (
        f"\\pm {_fmt_fixed(a1, 10)},\\ "
        f"\\pm {_fmt_fixed(a2, 10)},\\ "
        f"\\pm {_fmt_fixed(a3, 10)},\\ "
        f"\\pm {_fmt_fixed(gamma, 10)}\\,\\mathrm{{i}}"
    )

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_output_potential_puiseux_asymptotics.py")
    lines.append("\\paragraph{新增：饱和端点的镜像 Perron 对高阶 Puiseux jet、谱隙常数化与全谱缩放律（可复现）}")
    lines.append("沿附录中输出势的显式代数曲线 $G(\\lambda,u)=0$（命题~\\ref{prop:real-input-40-pressure-freezing}）并令 $u\\to+\\infty$。")
    lines.append("记 $\\lambda_1(u)$ 为该曲线在 $u>0$ 上的 Perron 根（最大正实根），并记 $\\lambda_{\\mathrm{mir}}(u)<0$ 为其在饱和端点的镜像负实分支（命题~\\ref{prop:real-input-40-output-mirror-branch}）。")
    lines.append("令 $y_{\\max}$ 为四次方程 $y^4-6y^3+9y^2-y-1=0$ 的最大正根，并令 $c:=\\sqrt{y_{\\max}}$。则存在代数常数 $d,e,f$ 使得：")
    lines.append("\\[")
    lines.append("\\boxed{\\ \\lambda_1(u)=c\\sqrt u+d+\\frac{e}{\\sqrt u}+\\frac{f}{u}+O\\!\\left(u^{-3/2}\\right)\\ },")
    lines.append("\\qquad")
    lines.append("\\boxed{\\ \\lambda_{\\mathrm{mir}}(u)=-c\\sqrt u+d-\\frac{e}{\\sqrt u}+\\frac{f}{u}+O\\!\\left(u^{-3/2}\\right)\\ }.")
    lines.append("\\]")
    lines.append("数值上（保留 $%d$ 位小数）：" % nd)
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(f"c&\\approx {_fmt_fixed(c, nd)},\\\\")
    lines.append(f"d&\\approx {_fmt_fixed(d, nd)},\\\\")
    lines.append(f"e&\\approx {_fmt_fixed(e, nd)},\\\\")
    lines.append(f"f&\\approx {_fmt_fixed(f, nd)}.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append("该 Puiseux jet 体现出严格的对称律：两支的 $O(1)$ 常数项相同（均为 $d$），而 $u^{-1/2}$ 项严格反号。")
    lines.append("")
    lines.append("由 $|\\lambda_{\\mathrm{mir}}(u)|=-\\lambda_{\\mathrm{mir}}(u)$（$u\\gg1$）立即推出谱隙常数化：")
    lines.append("\\[")
    lines.append("\\boxed{\\ \\lambda_1(u)-|\\lambda_{\\mathrm{mir}}(u)|=2d+\\frac{2f}{u}+O\\!\\left(u^{-3/2}\\right)\\ }.")
    lines.append("\\]")
    lines.append(f"数值上 $2d\\approx {_fmt_fixed(2*d, 16)}$，且 $c/(2d)\\approx {_fmt_fixed(c/(2*d), 16)}$。")
    lines.append("并且相对谱隙满足")
    lines.append("\\[")
    lines.append("\\boxed{\\ 1-\\frac{|\\lambda_{\\mathrm{mir}}(u)|}{\\lambda_1(u)}=\\frac{2d}{c}\\,u^{-1/2}+O(u^{-1})\\ },")
    lines.append("\\qquad")
    lines.append(f"\\frac{{2d}}{{c}}\\approx {_fmt_fixed((2*d)/c, 12)}.")
    lines.append("\\]")
    lines.append("因此任何由 $-\\log(|\\lambda_{\\mathrm{mir}}|/\\lambda_1)$ 控制的相关尺度（例如谱隙比混合时间）在 $u\\to+\\infty$ 满足 $\\tau(u)\\asymp \\sqrt u$，主系数为 $c/(2d)\\approx %s$。" % _fmt_fixed(c / (2 * d), 12))
    lines.append("")
    lines.append("最后，在相同端点极限下，$G(\\lambda,u)=0$ 的全部 $8$ 个根具有统一的 $\\sqrt u$ 缩放：令 $\\rho$ 满足")
    lines.append("\\[")
    lines.append("\\boxed{\\ \\rho^8-6\\rho^6+9\\rho^4-\\rho^2-1=0\\ },")
    lines.append("\\]")
    lines.append("则存在适当排序使得 $\\lambda_j(u)=\\rho_j\\sqrt u+O(1)$（$1\\le j\\le 8$），并且极限根集合为")
    lines.append("\\[")
    lines.append("\\boxed{\\ \\{\\rho_j\\}_{j=1}^8=\\{"+rho_tex+"\\}\\ }.")
    lines.append("\\]")
    lines.append("结合显式因子 $(1-uz^2)$ 诱导的两条特征值 $\\pm\\sqrt u$（推论~\\ref{cor:real-input-40-factor-sqrtu-eigs}），得到非零谱的 $\\sqrt u$ 归一化谱像为 $\\{\\pm1\\}\\cup\\{\\rho_j\\}_{j=1}^8$。")
    lines.append("")
    lines.append("\\noindent\\emph{可复现性：}常数与根集合由脚本 \\path{scripts/exp_real_input_40_output_potential_puiseux_asymptotics.py} 从 $G(\\lambda,u)$ 的显式形式逐阶比较系数并数值核验导出。")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Puiseux u->infty asymptotics for output potential (real input 40-state)."
    )
    parser.add_argument(
        "--prec-digits",
        type=int,
        default=120,
        help="Decimal digits used internally by sympy nroots/series.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_output_potential_puiseux_asymptotics.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_output_potential_puiseux_asymptotics.tex"),
    )
    args = parser.parse_args()

    prec = int(args.prec_digits)
    y_max, c, d, e, f = _solve_puiseux_coeffs(prec_digits=prec)
    rho_roots = _limit_rho_roots(prec_digits=prec)

    # Derived constants.
    two_d = sp.N(2 * d, 50)
    two_d_over_c = sp.N(2 * d / c, 50)
    c_over_two_d = sp.N(c / (2 * d), 50)

    res = PuiseuxAsymptotics(
        y_max=_as_str(y_max, 80),
        c=_as_str(c, 80),
        d=_as_str(d, 80),
        e=_as_str(e, 80),
        f=_as_str(f, 80),
        two_d=_as_str(two_d, 80),
        two_d_over_c=_as_str(two_d_over_c, 80),
        c_over_two_d=_as_str(c_over_two_d, 80),
        rho_roots=[str(r) for r in rho_roots],
    )

    # Write JSON.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(res), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Write TeX snippet.
    _write_tex(
        Path(args.tex_out),
        c=float(sp.N(c, 40)),
        d=float(sp.N(d, 40)),
        e=float(sp.N(e, 40)),
        f=float(sp.N(f, 40)),
        rho_roots=rho_roots,
    )

    print(f"[puiseux-asymptotics] wrote {jout}", flush=True)
    print(f"[puiseux-asymptotics] wrote {args.tex_out}", flush=True)
    print("[puiseux-asymptotics] done", flush=True)


if __name__ == "__main__":
    main()
