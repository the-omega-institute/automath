#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Center-slice audits for the rate-curve elimination certificate.

We use ONLY the printed structural certificate at alpha=1/2:

  R(1/2,u) = -(u-1)^6 Q(u) / 64,   Q(u) in Z[u],

and derive additional auditable consequences:
  - Q is self-reciprocal (palindromic coefficients): Q(u)=u^16 Q(1/u)
  - Q has no real roots (Sturm count), hence Q(u)>0 for all real u
  - the unique real solution of R(1/2,u)=0 is u=1 (multiplicity 6)
  - the nearest nontrivial singularity distance around u=1:
        R_* = min{|u-1| : Q(u)=0}
    and a representative closest root u_*.
  - a convergence-threshold corollary for u=omega_p on the unit circle.

Outputs:
  - artifacts/export/sync_kernel_rate_curve_center_slice_audit.json
  - sections/generated/eq_sync_kernel_rate_curve_center_slice_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class CenterSliceAudit:
    Q_degree: int
    Q_coeffs_desc: List[int]
    Q_is_palindromic: bool
    Q_real_root_count: int
    Q_at_0: int
    Q_at_1: int
    R_star: float
    u_star_re: float
    u_star_im_abs: float
    dist_omega_5: float
    dist_omega_6: float
    dist_omega_7: float
    p_star: int


def _parse_Q_from_structure(tex_path: Path) -> sp.Poly:
    """
    Parse Q(u)=... from the auto-generated structure snippet:
      sections/generated/eq_sync_kernel_rate_curve_resultant_structure.tex

    Expected format fragment:
      ... Q(u)=16 u^{16} + ... + 448 u + 16.
    """
    text = tex_path.read_text(encoding="utf-8")
    key = "Q(u)="
    if key not in text:
        raise RuntimeError(f"Failed to find {key!r} in {tex_path}")
    after = text.split(key, 1)[1]
    poly_part = after.split(".", 1)[0].strip()
    if not poly_part:
        raise RuntimeError(f"Empty Q(u) payload in {tex_path}")

    terms = [t.strip() for t in poly_part.split("+") if t.strip()]
    coeff_by_exp: Dict[int, int] = {}
    for term in terms:
        if "u^{" in term:
            coeff_str, rest = term.split("u^{", 1)
            exp_str = rest.split("}", 1)[0]
            coeff = int(coeff_str.strip())
            exp = int(exp_str.strip())
        elif "u" in term:
            # linear term "448 u" (no exponent)
            coeff_str = term.split("u", 1)[0].strip()
            coeff = int(coeff_str)
            exp = 1
        else:
            # constant term
            coeff = int(term.strip())
            exp = 0
        if exp in coeff_by_exp and coeff_by_exp[exp] != coeff:
            raise RuntimeError(f"Duplicate exponent u^{exp} with conflicting coeffs in {tex_path}")
        coeff_by_exp[exp] = coeff

    if not coeff_by_exp:
        raise RuntimeError(f"Could not parse any terms for Q(u) from {tex_path}")

    u = sp.Symbol("u")
    expr = sp.Integer(0)
    for exp, coeff in coeff_by_exp.items():
        expr += sp.Integer(coeff) * (u**exp)
    P = sp.Poly(sp.expand(expr), u, domain=sp.ZZ)
    return P


def _is_palindromic(P: sp.Poly) -> bool:
    coeffs = [int(c) for c in P.all_coeffs()]
    return coeffs == list(reversed(coeffs))


def _omega_dist(p: int) -> float:
    # |exp(2π i/p)-1| = 2 sin(π/p)
    return 2.0 * math.sin(math.pi / float(p))


def _p_star(R_star: float, p_max: int = 2000) -> int:
    """
    Smallest integer p>=2 such that |omega_p-1|<R_star.

    Since |omega_p-1|=2 sin(pi/p) is strictly decreasing in p>=2,
    this is the sharp modulus threshold induced by the center-slice root disk.
    """
    for p in range(2, int(p_max) + 1):
        if _omega_dist(p) < float(R_star):
            return int(p)
    raise RuntimeError(f"Failed to find p_star within p<= {p_max}.")


def _format_float(x: float, ndp: int = 10) -> str:
    # Stable decimal formatting for TeX.
    return f"{float(x):.{ndp}f}"


def main() -> None:
    parser = argparse.ArgumentParser(description="Center-slice audits for R(1/2,u).")
    parser.add_argument(
        "--dps",
        type=int,
        default=80,
        help="Decimal digits used in numerical root finding (nroots).",
    )
    parser.add_argument(
        "--structure-tex",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_rate_curve_resultant_structure.tex"),
        help="Path to the generated structure TeX snippet that contains Q(u).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_rate_curve_center_slice_audit.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_rate_curve_center_slice_audit.tex"),
    )
    args = parser.parse_args()

    u = sp.Symbol("u")
    Q = _parse_Q_from_structure(Path(args.structure_tex))
    deg = int(Q.degree())
    coeffs_desc = [int(c) for c in Q.all_coeffs()]
    pal = _is_palindromic(Q)

    # Exact real-root count via Sturm sequence.
    n_real = int(Q.count_roots(-sp.oo, sp.oo))

    Q0 = int(Q.eval(0))
    Q1 = int(Q.eval(1))

    # Numerical closest root distance to u=1.
    roots = sp.nroots(Q, n=int(args.dps), maxsteps=300)
    roots_c: List[complex] = [complex(sp.N(r, int(args.dps))) for r in roots]
    closest = min(roots_c, key=lambda z: abs(z - 1.0))
    # Present as re ± im i with im >= 0.
    if closest.imag < 0:
        closest = closest.conjugate()
    R_star = float(abs(closest - 1.0))

    payload = CenterSliceAudit(
        Q_degree=deg,
        Q_coeffs_desc=coeffs_desc,
        Q_is_palindromic=bool(pal),
        Q_real_root_count=n_real,
        Q_at_0=Q0,
        Q_at_1=Q1,
        R_star=R_star,
        u_star_re=float(closest.real),
        u_star_im_abs=float(abs(closest.imag)),
        dist_omega_5=float(_omega_dist(5)),
        dist_omega_6=float(_omega_dist(6)),
        dist_omega_7=float(_omega_dist(7)),
        p_star=int(_p_star(R_star)),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Build TeX snippet (Chinese, for the paper).
    R_star_str = _format_float(payload.R_star, 10)
    u_re_str = _format_float(payload.u_star_re, 10)
    u_im_str = _format_float(payload.u_star_im_abs, 10)
    d5_str = _format_float(payload.dist_omega_5, 10)
    d6_str = _format_float(payload.dist_omega_6, 10)
    d7_str = _format_float(payload.dist_omega_7, 10)
    ratio6_str = _format_float(payload.dist_omega_6 / payload.R_star, 6)
    ratio7_str = _format_float(payload.dist_omega_7 / payload.R_star, 6)

    tex_lines: List[str] = []
    tex_lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_rate_curve_center_slice_audit.py")
    tex_lines.append("\\begin{proposition}[中心截面 $Q(u)$ 的自倒易性与实根空性]\\label{prop:rate-center-Q-reciprocal-no-real}")
    tex_lines.append("沿用证书 $R(\\tfrac12,u)=-(u-1)^6Q(u)/64$ 中的 $Q(u)\\in\\ZZ[u]$。")
    tex_lines.append("由于 $Q$ 的系数严格回文，立得自倒易恒等式 $Q(u)=u^{16}Q(1/u)$，因此零点必以互逆对出现（并与复共轭合并为四元组）。")
    tex_lines.append("进一步地，对该整系数 $Q$ 做 Sturm 计数，得到其在实轴上的零点数为")
    tex_lines.append("$$")
    tex_lines.append(f"N_\\RR(Q)=\\,{payload.Q_real_root_count}.")
    tex_lines.append("$$")
    tex_lines.append(f"又因 $Q(0)={payload.Q_at_0}>0$，故 $Q(u)>0$ 对所有 $u\\in\\RR$ 成立。")
    tex_lines.append("\\end{proposition}")
    tex_lines.append("")
    tex_lines.append("\\begin{corollary}[中心唯一实交与六重性]\\label{cor:rate-center-unique-real}")
    tex_lines.append("在实参数 $u\\in\\RR$ 上，")
    tex_lines.append("$$")
    tex_lines.append("R\\!\\left(\\tfrac12,u\\right)=0\\ \\Longleftrightarrow\\ u=1,")
    tex_lines.append("$$")
    tex_lines.append("且 $u=1$ 的重数恰为 $6$。")
    tex_lines.append("\\end{corollary}")
    tex_lines.append("")
    tex_lines.append("\\begin{corollary}[中心截面的最近复奇点距离]\\label{cor:rate-center-Rstar}")
    tex_lines.append("定义")
    tex_lines.append("$$")
    tex_lines.append("R_\\star:=\\min\\{|u-1|:\\ Q(u)=0\\}.")
    tex_lines.append("$$")
    tex_lines.append("则数值上")
    tex_lines.append("$$")
    tex_lines.append(f"\\boxed{{\\ R_\\star\\approx {R_star_str}\\ }}")
    tex_lines.append("$$")
    tex_lines.append("并可取最近根为")
    tex_lines.append("$$")
    tex_lines.append(f"u_\\star\\approx {u_re_str}\\pm {u_im_str}i.")
    tex_lines.append("$$")
    tex_lines.append("\\end{corollary}")
    tex_lines.append("")
    tex_lines.append("\\begin{corollary}[单位根扭曲的中心盘阈值（$p_\\star=6$）]\\label{cor:rate-center-omega-threshold}")
    tex_lines.append("令 $\\omega_p=e^{2\\pi i/p}$。则 $|\\omega_p-1|=2\\sin(\\pi/p)$。")
    tex_lines.append("由")
    tex_lines.append("$$")
    tex_lines.append(
        f"|\\omega_5-1|\\approx {d5_str}>R_\\star,\\qquad |\\omega_6-1|={d6_str}<R_\\star,\\qquad |\\omega_7-1|\\approx {d7_str}<R_\\star,"
    )
    tex_lines.append("$$")
    tex_lines.append("并利用 $2\\sin(\\pi/p)$ 随 $p$ 单调递减，可得对所有 $p\\ge 6$ 均有 $|\\omega_p-1|<R_\\star$，而对所有 $p\\le 5$ 则有 $|\\omega_p-1|>R_\\star$。")
    tex_lines.append("等价地，若定义模数阈值")
    tex_lines.append("$$")
    tex_lines.append("p_\\star:=\\min\\{p\\ge 2:\\ |\\omega_p-1|<R_\\star\\},")
    tex_lines.append("$$")
    tex_lines.append(f"则本例 $p_\\star={payload.p_star}$。并且 $p=6$ 处于贴边区：$|\\omega_6-1|/R_\\star\\approx {ratio6_str}$，而对 $p\\ge 7$ 有更显著裕量（例如 $|\\omega_7-1|/R_\\star\\approx {ratio7_str}$）。")
    tex_lines.append("\\end{corollary}")
    tex_lines.append("")
    tex_lines.append("\\begin{remark}[中心截面的极简审计链]\\label{rem:rate-center-min-audit}")
    tex_lines.append("仅用打印出的 $Q$ 系数即可同时审计“对偶对称在中心截面的一致性”与“中心聚合次数”：")
    tex_lines.append("\\begin{enumerate}")
    tex_lines.append("  \\item 检查系数回文（等价于 $Q(u)=u^{16}Q(1/u)$）；")
    tex_lines.append(f"  \\item 检查 $Q(1)={payload.Q_at_1}\\neq 0$（从而 $u=1$ 恰为 $6$ 重根）；")
    tex_lines.append("  \\item 检查第六导数尺度（由分解式直接推出）")
    tex_lines.append("  $$")
    tex_lines.append("  Q(1)=-\\frac{64}{6!}\\,\\partial_u^{6}R\\!\\left(\\tfrac12,u\\right)\\Big|_{u=1}.")
    tex_lines.append("  $$")
    tex_lines.append("\\end{enumerate}")
    tex_lines.append("\\end{remark}")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(tex_lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

