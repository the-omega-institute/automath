#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Dual-symmetry structured reduction for the rate-curve elimination certificate.

We start from the normalized resultant R(alpha,u) in Z[alpha,u] (deg_alpha=6, deg_u=22)
with the dual self-symmetry:

  R(alpha,u) = u^22 * R(1-alpha, 1/u).

Introduce the symmetric coordinates

  a := 2*alpha - 1,   X := a^2,   s := u + 1/u.

After clearing the alpha-shift denominators (multiply by 2^6 = 64), the dual symmetry
forces a canonical even/odd split in a, which is simultaneously palindromic /
anti-palindromic in u. This yields constructive polynomials A(X,s), B(X,s) in Z[X,s]
such that:

  64 R(alpha,u) = u^11 A(X,s) + a (u^12 - u^10) B(X,s),
  with X = (2*alpha-1)^2 and s = u + 1/u.

Equivalently, defining v := a (u - 1/u) (which is invariant under (a,u)->(-a,1/u)),
we have a cubic-in-X closure on the invariant surface v^2 = X(s^2-4):

  64 u^{-11} R(alpha,u) = A(X,s) + v B(X,s),   v^2 = X(s^2-4).

This script exports a small auditable summary and a TeX snippet for the paper.

Outputs:
  - artifacts/export/sync_kernel_rate_curve_duality_reduction.json
  - sections/generated/eq_sync_kernel_rate_curve_duality_reduction.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import sympy as sp

from common_paths import export_dir, generated_dir
from exp_sync_kernel_rate_curve_elimination import _build_F, _u_adic_valuation


@dataclass(frozen=True)
class DualityReductionSummary:
    scale: int
    deg_alpha: int
    deg_u: int
    u_adic_valuation: int
    A_deg_X: int
    A_deg_s: int
    A_n_terms: int
    B_deg_X: int
    B_deg_s: int
    B_n_terms: int
    reconstruction_ok: bool
    center_A0_has_s2_cubed: bool
    center_A0_quot_deg: int
    u1_A_is_const_times_X3: bool
    u1_A_const: int
    u1_R_const: int


def _chebyshev_p_list(n: int, s: sp.Symbol) -> list[sp.Expr]:
    """p_k(s) = u^k + u^{-k} as polynomials in s=u+u^{-1}."""
    if n < 0:
        return []
    p: list[sp.Expr] = [sp.Integer(0)] * (n + 1)
    if n >= 0:
        p[0] = sp.Integer(2)
    if n >= 1:
        p[1] = s
    for k in range(1, n):
        p[k + 1] = sp.expand(s * p[k] - p[k - 1])
    return p


def _chebyshev_q_list(n: int, s: sp.Symbol) -> list[sp.Expr]:
    """
    q_k(s) = (u^{k+1} - u^{-(k+1)})/(u - u^{-1}) as polynomials in s=u+u^{-1}.
    """
    if n < 0:
        return []
    q: list[sp.Expr] = [sp.Integer(0)] * (n + 1)
    if n >= 0:
        q[0] = sp.Integer(1)
    if n >= 1:
        q[1] = s
    for k in range(1, n):
        q[k + 1] = sp.expand(s * q[k] - q[k - 1])
    return q


def _poly_u_coeffs_as_poly_in_X(PXu: sp.Poly, X: sp.Symbol, u: sp.Symbol) -> dict[int, sp.Expr]:
    """
    Given PXu in ZZ[X,u], return a dict mapping each u-exponent j to the coefficient in ZZ[X].
    """
    out: dict[int, sp.Expr] = {}
    for (eX, eU), c in PXu.terms():
        j = int(eU)
        out[j] = out.get(j, sp.Integer(0)) + sp.Integer(c) * (X ** int(eX))
    return out


def _build_R_norm(alpha: sp.Symbol, u: sp.Symbol) -> tuple[sp.Poly, int]:
    lam = sp.Symbol("lam")
    F = _build_F(lam, u)
    Fl = sp.diff(F, lam)
    Fu = sp.diff(F, u)
    G = sp.expand(alpha * lam * Fl + u * Fu)

    R_raw = sp.resultant(F, G, lam)
    PR_raw = sp.Poly(R_raw, alpha, u, domain="ZZ")

    Pu_raw = sp.Poly(PR_raw.as_expr(), u, domain=sp.ZZ[alpha])
    v_u = _u_adic_valuation(Pu_raw, u=u)
    R_norm_expr = sp.expand(Pu_raw.as_expr() / (u ** v_u))
    PR = sp.Poly(R_norm_expr, alpha, u, domain="ZZ")
    return PR, int(v_u)


def main() -> None:
    parser = argparse.ArgumentParser(description="Dual-symmetry reduction for R(alpha,u).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_rate_curve_duality_reduction.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_rate_curve_duality_reduction.tex"),
    )
    args = parser.parse_args()

    t0 = time.time()

    alpha = sp.Symbol("alpha")
    u = sp.Symbol("u")
    a = sp.Symbol("a")
    X = sp.Symbol("X")
    s = sp.Symbol("s")

    PR, v_u = _build_R_norm(alpha=alpha, u=u)
    deg_alpha = int(PR.degree(alpha))
    deg_u = int(PR.degree(u))

    # Clear denominators introduced by alpha=(a+1)/2 (deg_alpha=6 => 2^6).
    scale = 64
    expr_a_scaled = sp.expand(scale * PR.as_expr().subs(alpha, (a + 1) / 2))

    # Even/odd in a.
    expr_even = sp.expand((expr_a_scaled + expr_a_scaled.subs(a, -a)) / 2)
    expr_odd = sp.expand((expr_a_scaled - expr_a_scaled.subs(a, -a)) / 2)

    Pe = sp.Poly(expr_even, a, u, domain="ZZ")  # even in a; palindromic in u
    Po = sp.Poly(expr_odd, a, u, domain="ZZ")   # odd in a; anti-palindromic in u

    # Map a^(2k) -> X^k for even part: PeX(X,u) in ZZ[X,u]
    Pe_poly = sp.Poly(Pe.as_expr(), a, u, domain="ZZ")
    expr_Pe_X = sp.Integer(0)
    for (ea, eu), c in Pe_poly.terms():
        if int(ea) % 2 != 0:
            raise RuntimeError("Even part unexpectedly contains an odd a-power.")
        expr_Pe_X += sp.Integer(c) * (X ** (int(ea) // 2)) * (u ** int(eu))
    PeX = sp.Poly(sp.expand(expr_Pe_X), X, u, domain="ZZ")

    # Map a^(2k+1) -> a X^k for odd part: Po = a * P1X(X,u)
    Po_poly = sp.Poly(Po.as_expr(), a, u, domain="ZZ")
    expr_P1_X = sp.Integer(0)
    for (ea, eu), c in Po_poly.terms():
        if int(ea) == 0:
            if c != 0:
                raise RuntimeError("Odd part unexpectedly contains an a^0 term.")
            continue
        if (int(ea) - 1) % 2 != 0:
            raise RuntimeError("Odd part / a unexpectedly contains an odd a-power.")
        expr_P1_X += sp.Integer(c) * (X ** ((int(ea) - 1) // 2)) * (u ** int(eu))
    P1X = sp.Poly(sp.expand(expr_P1_X), X, u, domain="ZZ")

    # Convert palindromic / anti-palindromic polynomials in u to polynomials in s=u+1/u.
    # Degree is fixed at 22, so n=11.
    n = 11
    p = _chebyshev_p_list(n, s=s)         # p_k for k=0..11
    q = _chebyshev_q_list(n - 1, s=s)     # q_k for k=0..10

    coeffE = _poly_u_coeffs_as_poly_in_X(PeX, X=X, u=u)
    coeffO = _poly_u_coeffs_as_poly_in_X(P1X, X=X, u=u)

    A_expr = coeffE.get(n, sp.Integer(0))
    for k in range(1, n + 1):
        A_expr += coeffE.get(n + k, sp.Integer(0)) * p[k]
    A_poly = sp.Poly(sp.expand(A_expr), X, s, domain="ZZ")

    B_expr = sp.Integer(0)
    for k in range(1, n + 1):
        B_expr += coeffO.get(n + k, sp.Integer(0)) * q[k - 1]
    B_poly = sp.Poly(sp.expand(B_expr), X, s, domain="ZZ")

    # Reconstruction check in (a,u): substitute X=a^2, s=u+1/u, then compare numerators.
    recon = sp.expand(
        u ** n * A_poly.as_expr().subs({X: a**2, s: u + 1 / u})
        + a * (u ** (n + 1) - u ** (n - 1)) * B_poly.as_expr().subs({X: a**2, s: u + 1 / u})
    )
    num, den = sp.together(recon).as_numer_denom()
    reconstruction_ok = bool(den == 1 and sp.expand(num - expr_a_scaled) == 0)

    # Center audits.
    A0 = sp.Poly(A_poly.as_expr().subs(X, 0), s, domain="ZZ")
    div = sp.Poly((s - 2) ** 3, s, domain="ZZ")
    quot, rem = sp.div(A0, div)
    center_A0_has_s2_cubed = bool(rem.as_expr() == 0)
    center_A0_quot_deg = int(quot.degree()) if center_A0_has_s2_cubed else -1

    A_u1 = sp.Poly(A_poly.as_expr().subs(s, 2), X, domain="ZZ")
    u1_A_const = int(A_u1.LC()) if not A_u1.is_zero else 0
    u1_A_is_const_times_X3 = bool(
        (not A_u1.is_zero)
        and int(A_u1.degree()) == 3
        and A_u1.all_coeffs() == [sp.Integer(u1_A_const), sp.Integer(0), sp.Integer(0), sp.Integer(0)]
    )
    # At u=1: 64 R(alpha,1) = A(X,2) and X=(2alpha-1)^2.
    u1_R_const = int(u1_A_const // scale) if (u1_A_is_const_times_X3 and u1_A_const % scale == 0) else 0

    summary = DualityReductionSummary(
        scale=int(scale),
        deg_alpha=int(deg_alpha),
        deg_u=int(deg_u),
        u_adic_valuation=int(v_u),
        A_deg_X=int(A_poly.degree(X)) if not A_poly.is_zero else -1,
        A_deg_s=int(A_poly.degree(s)) if not A_poly.is_zero else -1,
        A_n_terms=int(len(A_poly.terms())),
        B_deg_X=int(B_poly.degree(X)) if not B_poly.is_zero else -1,
        B_deg_s=int(B_poly.degree(s)) if not B_poly.is_zero else -1,
        B_n_terms=int(len(B_poly.terms())),
        reconstruction_ok=bool(reconstruction_ok),
        center_A0_has_s2_cubed=bool(center_A0_has_s2_cubed),
        center_A0_quot_deg=int(center_A0_quot_deg),
        u1_A_is_const_times_X3=bool(u1_A_is_const_times_X3),
        u1_A_const=int(u1_A_const),
        u1_R_const=int(u1_R_const),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(summary), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX snippet (Chinese, for the paper).
    tex: list[str] = []
    tex.append("% AUTO-GENERATED by scripts/exp_sync_kernel_rate_curve_duality_reduction.py")
    tex.append("\\begin{proposition}[对偶自对称诱导的 $(X,s)$ 结构化降维与三次化封闭]\\label{prop:rate-duality-structured-reduction}")
    tex.append("令 $a:=2\\alpha-1$、$X:=a^2=(2\\alpha-1)^2$，并取对称坐标 $s:=u+1/u$。")
    tex.append("则存在 $A(X,s),B(X,s)\\in\\ZZ[X,s]$（由证书 $R(\\alpha,u)$ 可构造并可复算审计），使得恒等式")
    tex.append("$$")
    tex.append("\\boxed{\\ %d\\,R(\\alpha,u)=u^{11}A\\!\\left((2\\alpha-1)^2,\\ u+\\tfrac1u\\right)"
               "+(2\\alpha-1)\\,(u^{12}-u^{10})\\,B\\!\\left((2\\alpha-1)^2,\\ u+\\tfrac1u\\right)\\ }"
               % summary.scale)
    tex.append("$$")
    tex.append("成立。并且 $\\deg_XA=%d,\\ \\deg_XB=%d$（相应 $\\deg_{\\alpha}R=6$ 被压缩为 $X$-三次），且 $\\deg_sA=%d,\\ \\deg_sB=%d$。"
               % (summary.A_deg_X, summary.B_deg_X, summary.A_deg_s, summary.B_deg_s))
    tex.append("等价地，令不变量 $v:=a(u-1/u)$，则有")
    tex.append("$$")
    tex.append("%d\\,u^{-11}R(\\alpha,u)=A(X,s)+v\\,B(X,s),\\qquad v^2=X(s^2-4)." % summary.scale)
    tex.append("$$")
    tex.append("\\end{proposition}")
    tex.append("")
    tex.append("\\begin{corollary}[自对偶固定点的 $6=3\\times 2$ 双重降阶审计]\\label{cor:rate-duality-center-6-3x2}")
    tex.append("在自对偶点 $u=1$（即 $s=2$）上，上式退化为 $%d\\,R(\\alpha,1)=A(X,2)$。本例中脚本验证" % summary.scale)
    if summary.u1_A_is_const_times_X3 and summary.u1_R_const:
        tex.append("$$")
        tex.append("A(X,2)=%d\\,X^3,\\qquad\\text{从而}\\qquad R(\\alpha,1)=%d\\,(2\\alpha-1)^6." % (summary.u1_A_const, summary.u1_R_const))
        tex.append("$$")
        tex.append("这表明中心的六重性在 $X=(2\\alpha-1)^2$ 坐标下必降为三重（再乘 $a=\\pm\\sqrt{X}$ 的双支恢复为 $6$）。")
    else:
        tex.append("中心退化未通过本脚本的 $X^3$ 形状审计（这在未来改核/改脚本时可作为强否决项）。")
    tex.append("另一方面，在中心截面 $\\alpha=\\tfrac12$（即 $X=0$）上，奇部自动消失并得到")
    tex.append("$$")
    tex.append("%d\\,R\\!\\left(\\tfrac12,u\\right)=u^{11}A(0,u+1/u)." % summary.scale)
    tex.append("$$")
    if summary.center_A0_has_s2_cubed:
        tex.append("从证书 $R(\\tfrac12,u)=-(u-1)^6Q(u)/64$ 立得 $A(0,s)$ 必含 $(s-2)^3$ 因子（此处 $s-2=(u-1)^2/u$），即中心六重性在 $s=u+1/u$ 坐标下同样必降为三重。")
    tex.append("\\end{corollary}")
    tex.append("")
    tex.append("\\begin{remark}[侧翼四重簇在 $X$ 坐标下落到同一点]\\label{rem:rate-duality-wing-Xquarter}")
    tex.append("证书端点系数含 $(4\\alpha-1)^4$ 与 $(4\\alpha-3)^4$，故侧翼簇满足 $\\alpha\\to\\tfrac14,\\tfrac34$。")
    tex.append("在 $X=(2\\alpha-1)^2$ 坐标下二者同值：$X\\to(\\pm\\tfrac12)^2=\\tfrac14$（等价 $T=(\\alpha-\\tfrac12)^2\\to\\tfrac1{16}$）。")
    tex.append("因此在降维后的分支跟踪中可用 $X\\approx\\tfrac14$ 作为“翼分支”的全域标签。")
    tex.append("\\end{remark}")
    tex.append("")
    tex.append("\\begin{remark}[单位根扫描的降阶口径]\\label{rem:rate-duality-unit-root-scan}")
    tex.append("对单位根 $u=e^{i\\theta}$ 有 $s=u+1/u=2\\cos\\theta\\in[-2,2]$。")
    tex.append("由 $v^2=X(s^2-4)$ 可把 $v$ 消去，从而得到仅含 $(X,s)$ 的投影关系")
    tex.append("$$")
    tex.append("A(X,s)^2\\; -\\; X(s^2-4)\\,B(X,s)^2\\;=\\;0,")
    tex.append("$$")
    tex.append("它对每个固定 $s$ 给出至多 $6$ 次的一元代数方程（$\\deg_X\\le 6$）。与直接在 $R(\\alpha,u)=0$ 上处理复系数相比，这一口径把单位根扫描改写为实参数 $s$ 上的可审计多项式求根，并把共轭/互逆配对结构显式内化。")
    tex.append("\\end{remark}")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(tex) + "\n", encoding="utf-8")

    dt = time.time() - t0
    print(f"[dual-reduction] wrote {jout} and {tout} (elapsed_s={dt:.3f})", flush=True)


if __name__ == "__main__":
    main()

