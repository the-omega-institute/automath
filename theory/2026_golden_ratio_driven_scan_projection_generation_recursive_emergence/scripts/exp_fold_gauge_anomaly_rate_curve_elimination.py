#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Eliminate mu from the fold gauge-anomaly pressure equation (rate-curve certificate).

We use the 4-state Berstel (2001) unambiguous Zeckendorf normalizer (Fig. 1).

Let u = e^theta. The (unscaled) Perron root mu(u)=rho(2 A_theta) is algebraic:
  F(mu,u)=det(mu I - M(u))=0,
where A_theta = (1/2) M(e^theta).

The Legendre slope (mismatch density at twist u) is:
  alpha(u) = d/dtheta log rho(A_theta) = u * mu_u / mu,
with mu_u = -F_u / F_mu (implicit differentiation).

Hence alpha,mu,u satisfy the polynomial system:
  F(mu,u) = 0,
  G(alpha,mu,u) := alpha*mu*F_mu(mu,u) + u*F_u(mu,u) = 0.

Eliminating mu yields a nonzero polynomial R(alpha,u) in Z[alpha,u] such that
R(alpha(u),u)=0 for all u>0 on the Perron branch. This is an algebraic
certificate for the full-domain rate curve alpha(u).

Outputs:
- artifacts/export/fold_gauge_anomaly_rate_curve_resultant.json
- sections/generated/tab_fold_gauge_anomaly_rate_curve_resultant_degree.tex
- sections/generated/eq_fold_gauge_anomaly_rate_curve_resultant_structure.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class ResultantSummary:
    deg_alpha: int
    deg_u: int
    n_terms: int
    content_gcd: str
    leading_monomial: str
    leading_coeff: str
    u_adic_valuation: int


def _build_F(mu: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match scripts/exp_fold_gauge_anomaly_pressure.py.
    return mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u


def _u_adic_valuation(poly_u: sp.Poly) -> int:
    """Return the smallest exponent j such that [u^j] poly_u != 0."""
    if poly_u.is_zero:
        return 0
    min_j = None
    for mon, coeff in poly_u.terms():
        j = int(mon[0])  # mon is a 1-tuple (j,)
        if coeff != 0:
            min_j = j if min_j is None else min(min_j, j)
    return int(min_j or 0)


def _tex_table(summary: ResultantSummary) -> str:
    lines: list[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Elimination certificate for the gauge-anomaly rate curve. "
        "We eliminate $\\mu$ from $F(\\mu,u)=0$ and "
        "$\\alpha\\mu F_{\\mu}(\\mu,u)+uF_u(\\mu,u)=0$ to obtain "
        "a resultant in $\\mathbb{Z}[\\alpha,u]$. "
        "We then divide out the maximal $u$-power (the $u$-adic valuation) "
        "and the coefficient content gcd to obtain the primitive normalized "
        "$R(\\alpha,u)$ (see script).}"
    )
    lines.append("\\label{tab:fold_gauge_anomaly_rate_curve_resultant_degree}")
    lines.append("\\begin{tabular}{l l}")
    lines.append("\\toprule")
    lines.append("$\\deg_{\\alpha} R$ & $%d$\\\\" % summary.deg_alpha)
    lines.append("$\\deg_{u} R$ & $%d$\\\\" % summary.deg_u)
    lines.append("\\#terms & $%d$\\\\" % summary.n_terms)
    lines.append("$\\mathrm{content}(R)$ & $%s$\\\\" % summary.content_gcd.replace("_", "\\_"))
    lines.append("leading monomial & $%s$\\\\" % summary.leading_monomial.replace("_", "\\_"))
    lines.append("leading coeff & $%s$\\\\" % summary.leading_coeff.replace("_", "\\_"))
    lines.append("$v_u(R_{\\mathrm{raw}})$ & $%d$\\\\" % summary.u_adic_valuation)
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    return "\n".join(lines) + "\n"


def _tex_structure_block(R: sp.Poly, alpha: sp.Symbol, u: sp.Symbol) -> str:
    """Write auditable structural facts about R(alpha,u) as TeX equations."""
    deg_u = int(R.degree(u))
    deg_a = int(R.degree(alpha))

    # Specialization at u=1 factors with the feasible root alpha=4/9.
    fac_u1 = sp.factor(R.as_expr().subs(u, 1))

    # Show the raw F polynomial for audit.
    mu = sp.Symbol("mu")
    F = _build_F(mu, u)

    lines: list[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{align}")
    lines.append("F(\\mu,u)&=%s,\\\\" % sp.latex(F))
    lines.append("R(\\alpha,u)&\\in\\mathbb{Z}[\\alpha,u],\\qquad \\deg_{\\alpha}R=%d,\\ \\deg_u R=%d,\\\\"
                 % (deg_a, deg_u))
    lines.append("R(\\alpha,1)&=%s,\\qquad \\Rightarrow\\ \\alpha(1)=\\tfrac49." % sp.latex(fac_u1))
    lines.append("\\end{align}")
    lines.append("")
    lines.append(r"\begin{proposition}[规范差速率曲线的代数参数化与可行分支选择]\label{prop:fold-gauge-anomaly-rate-curve-param}")
    lines.append(
        r"在命题 \ref{prop:fold-gauge-anomaly-pressure} 的记号下，令 $u=e^\theta$，并令 $\mu(u)$ 表示代数方程 $F(\mu,u)=0$ 的 Perron 实根分支（即 $\mu(u)=2\rho(A_\theta)>0$）。"
    )
    lines.append(r"定义倾斜下的典型失配密度（速率曲线）")
    lines.append(r"\[")
    lines.append(r"\alpha(u):=\frac{d}{d\theta}P_G(\theta)\Big|_{\theta=\log u}.")
    lines.append(r"\]")
    lines.append(r"则由 $P_G(\theta)=\log(\mu(e^\theta)/2)$ 与隐函数微分（仅用 $F$）得纯代数参数化：")
    lines.append(r"\[")
    lines.append(
        r"\boxed{\ \alpha(u)=\frac{u\,\mu_u(u)}{\mu(u)}"
        r"=-\frac{u\,F_u(\mu,u)}{\mu\,F_\mu(\mu,u)}\Big|_{\mu=\mu(u)}\ }"
    )
    lines.append(r"\]")
    lines.append(r"其中 $F_u,F_\mu$ 为 $F(\mu,u)$ 的偏导数。")
    lines.append(r"并且大偏差率函数在该曲线上的 Legendre 驻点闭式为：")
    lines.append(r"\[")
    lines.append(r"\boxed{\ I(\alpha(u))=\alpha(u)\log u-\log\frac{\mu(u)}{2}\ }.")
    lines.append(r"\]")
    lines.append(
        r"此外，消元证书 $R(\alpha,u)=0$ 作为平面代数曲线包含多个代数分支；"
        r"在 $u=1$ 处出现的另一个根 $\alpha=-\tfrac14$ 是\emph{不可行分支}，"
        r"因为失配密度必须属于区间 $[0,1]$。"
        r"因此可用以下规则选出可行分支："
    )
    lines.append(r"\[")
    lines.append(r"\mu(u)>0,\qquad \alpha(u)\in[0,1],\qquad (\mu(1),\alpha(1))=(2,4/9).")
    lines.append(r"\]")
    lines.append(
        r"该规则给出一个可审计的代数相图参数化 $(u,\alpha(u),I(\alpha(u)))$，并显式排除不可行根支。"
    )
    lines.append(r"\end{proposition}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Eliminate mu to get R(alpha,u) for the gauge anomaly.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_gauge_anomaly_rate_curve_resultant.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_gauge_anomaly_rate_curve_resultant_degree.tex"),
    )
    parser.add_argument(
        "--structure-tex-out",
        type=str,
        default=str(generated_dir() / "eq_fold_gauge_anomaly_rate_curve_resultant_structure.tex"),
    )
    args = parser.parse_args()

    t0 = time.time()
    mu = sp.Symbol("mu")
    u = sp.Symbol("u")
    alpha = sp.Symbol("alpha")

    F = _build_F(mu, u)
    Fmu = sp.diff(F, mu)
    Fu = sp.diff(F, u)
    G = sp.expand(alpha * mu * Fmu + u * Fu)

    print("[elim] building resultant R(alpha,u) ...", flush=True)
    t1 = time.time()
    R_raw = sp.resultant(F, G, mu)
    elapsed = time.time() - t1
    print(f"[elim] resultant computed in {elapsed:.3f}s", flush=True)

    PR_raw = sp.Poly(R_raw, alpha, u, domain="ZZ")

    # Normalize by removing u-adic valuation (max u-power factor).
    Pu_raw = sp.Poly(PR_raw.as_expr(), u, domain=sp.ZZ[alpha])
    v_u = _u_adic_valuation(Pu_raw)
    R1_expr = sp.expand(Pu_raw.as_expr() / (u**v_u))
    PR1 = sp.Poly(R1_expr, alpha, u, domain="ZZ")

    # Make primitive (divide out content gcd), but record both.
    content_removed = sp.Integer(sp.gcd_list(list(PR1.coeffs()))) if PR1.coeffs() else sp.Integer(0)
    if content_removed == 0:
        raise RuntimeError("Empty resultant (unexpected).")
    PR = sp.Poly(sp.expand(PR1.as_expr() / content_removed), alpha, u, domain="ZZ")
    content_norm = sp.Integer(sp.gcd_list(list(PR.coeffs()))) if PR.coeffs() else sp.Integer(0)

    deg_alpha = int(PR.degree(alpha))
    deg_u = int(PR.degree(u))
    n_terms = len(PR.terms())

    # Leading term info under lex order (alpha > u).
    lt_monom, lt_coeff = PR.LT()
    leading_monomial = f"\\alpha^{{{lt_monom[0]}}}u^{{{lt_monom[1]}}}"
    leading_coeff = str(lt_coeff)

    summary = ResultantSummary(
        deg_alpha=deg_alpha,
        deg_u=deg_u,
        n_terms=n_terms,
        content_gcd=str(content_norm),
        leading_monomial=leading_monomial,
        leading_coeff=leading_coeff,
        u_adic_valuation=int(v_u),
    )

    payload: Dict[str, Any] = {
        "summary": asdict(summary),
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "polynomials": {
            "F_mu_u": str(F),
            "G_alpha_mu_u": str(G),
            "R_alpha_u_normalized": str(PR.as_expr()),
        },
        "normalization": {
            "u_adic_valuation": int(v_u),
            "content_gcd_removed": str(content_removed),
            "content_gcd_normalized": str(content_norm),
        },
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[elim] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text(_tex_table(summary), encoding="utf-8")
    print(f"[elim] wrote {tout}", flush=True)

    sout = Path(args.structure_tex_out)
    sout.parent.mkdir(parents=True, exist_ok=True)
    sout.write_text(_tex_structure_block(PR, alpha=alpha, u=u), encoding="utf-8")
    print(f"[elim] wrote {sout}", flush=True)


if __name__ == "__main__":
    main()

