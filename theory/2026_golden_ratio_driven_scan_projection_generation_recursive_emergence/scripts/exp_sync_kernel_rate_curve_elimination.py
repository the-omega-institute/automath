#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Eliminate lambda from the weighted sync-kernel pressure equation.

We have the sextic algebraic equation F(lambda,u)=0 for the Perron root lambda(u),
and the Legendre slope
  alpha(u) = u * lambda_u / lambda
with lambda_u = -F_u / F_lambda.

Hence alpha,lambda,u satisfy the polynomial system:
  F(lambda,u) = 0,
  G(alpha,lambda,u) := alpha*lambda*F_lambda(lambda,u) + u*F_u(lambda,u) = 0.

Eliminating lambda yields a nonzero polynomial R(alpha,u) in Z[alpha,u] such that
R(alpha(u),u)=0 for all u>0 on the Perron branch. This is an algebraic certificate
for the full-domain rate curve.

This script writes:
  - artifacts/export/sync_kernel_rate_curve_resultant.json
  - sections/generated/tab_sync_kernel_rate_curve_resultant_degree.tex
  - sections/generated/eq_sync_kernel_rate_curve_resultant_structure.tex

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


def _build_F(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match appendix `sections/appendix/sync_kernel/weighted/cor__sync-kernel-weighted-unit-root-finite.tex` (app:pressure-analytic).
    return (
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )


def _u_adic_valuation(poly_u: sp.Poly, u: sp.Symbol) -> int:
    """Return the smallest exponent j such that [u^j] poly_u != 0."""
    if poly_u.is_zero:
        return 0
    min_j = None
    for mon, coeff in poly_u.terms():
        # mon is a 1-tuple (j,)
        j = int(mon[0])
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
        "\\caption{Elimination certificate for the rate curve. "
        "We eliminate $\\lambda$ from $F(\\lambda,u)=0$ and "
        "$\\alpha\\lambda F_{\\lambda}(\\lambda,u)+uF_u(\\lambda,u)=0$ to obtain "
        "a resultant in $\\mathbb{Z}[\\alpha,u]$. "
        "We then divide out the maximal $u$-power (the $u$-adic valuation) "
        "to get the normalized polynomial $R(\\alpha,u)$ of minimal $u$-degree. "
        "This table records the degree/size of the normalized $R$ (see script).}"
    )
    lines.append("\\label{tab:sync_kernel_rate_curve_resultant_degree}")
    lines.append("\\begin{tabular}{l l}")
    lines.append("\\toprule")
    lines.append("$\\deg_{\\alpha} R$ & $%d$\\\\"
                 % summary.deg_alpha)
    lines.append("$\\deg_{u} R$ & $%d$\\\\"
                 % summary.deg_u)
    lines.append("\\#terms & $%d$\\\\"
                 % summary.n_terms)
    lines.append("$\\mathrm{content}(R)$ & $%s$\\\\"
                 % summary.content_gcd.replace("_", "\\_"))
    lines.append("leading monomial & $%s$\\\\"
                 % summary.leading_monomial.replace("_", "\\_"))
    lines.append("leading coeff & $%s$\\\\"
                 % summary.leading_coeff.replace("_", "\\_"))
    lines.append("$v_u(R_{\\mathrm{raw}})$ & $%d$\\\\"
                 % summary.u_adic_valuation)
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    return "\n".join(lines) + "\n"


def _tex_structure_block(
    R_norm: sp.Poly,
    alpha: sp.Symbol,
    u: sp.Symbol,
) -> str:
    """Write the auditable structural facts about R(alpha,u) as TeX equations."""
    def _poly_multiline_tex(P: sp.Poly, var: sp.Symbol, *, max_line_len: int = 110) -> list[str]:
        """Format a univariate integer polynomial as multiple TeX lines.

        Output lines are meant to be used inside an amsmath aligned environment.
        """
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

        parts: list[str] = []
        for idx, t in enumerate(terms):
            t = sp.expand(t)
            sign = -1 if t.could_extract_minus_sign() else 1
            t_abs = -t if sign < 0 else t
            tex = sp.latex(t_abs)
            if idx == 0:
                parts.append(("- " + tex) if sign < 0 else tex)
            else:
                parts.append(("- " + tex) if sign < 0 else ("+ " + tex))

        lines_out: list[str] = []
        cur = parts[0]
        for p in parts[1:]:
            if len(cur) + 1 + len(p) > max_line_len:
                lines_out.append(cur)
                cur = p
            else:
                cur = cur + " " + p
        lines_out.append(cur)
        return lines_out

    # Work as a polynomial in u with coefficients in Z[alpha].
    Pu = sp.Poly(R_norm.as_expr(), u, domain=sp.ZZ[alpha])
    deg_u = int(Pu.degree())

    r0 = sp.factor(Pu.coeff_monomial(u**0))
    rd = sp.factor(Pu.coeff_monomial(u**deg_u))
    r1 = sp.factor(Pu.coeff_monomial(u**1))
    rd1 = sp.factor(Pu.coeff_monomial(u ** (deg_u - 1)))

    # alpha=1/2 specialization factorization.
    expr_half = sp.expand(R_norm.as_expr().subs(alpha, sp.Rational(1, 2)))
    fac_half = sp.factor(expr_half)

    # Extract the palindromic Q(u) factor from the known form:
    # R(u,1/2) = -(u-1)^6 * Q(u) / 64.
    # We compute Q by dividing and clearing denominators.
    Ph = sp.Poly(expr_half, u, domain=sp.QQ)
    lin = sp.Poly(u - 1, u, domain=sp.QQ)
    Q = Ph
    for _ in range(6):
        Q, rem = sp.div(Q, lin)
        if sp.simplify(rem.as_expr()) != 0:
            break
    # Q is rational; clear denominators to get integer coefficients.
    Qq = sp.Poly(Q.as_expr(), u, domain=sp.QQ)
    den = sp.ilcm(*[sp.denom(c) for c in Qq.all_coeffs()]) if Qq.all_coeffs() else 1
    QZ = sp.Poly(sp.expand(Qq.as_expr() * den), u, domain=sp.ZZ)
    # Fix sign so that the leading coefficient is positive.
    if QZ.LC() < 0:
        QZ = sp.Poly(-QZ.as_expr(), u, domain=sp.ZZ)
        den = -den

    # Sanity: Q(u) has positive coefficients in the normalized form.
    if any(int(c) <= 0 for c in QZ.all_coeffs()):
        raise RuntimeError("Expected Q(u) to have strictly positive coefficients.")

    lines: list[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{align}")
    lines.append(
        "R(\\alpha,u)&=\\sum_{j=0}^{%d} r_j(\\alpha)\\,u^j\\in\\mathbb{Z}[\\alpha,u],\\\\"
        % deg_u
    )
    lines.append(
        "R(\\alpha,u)&=u^{%d}\\,R(1-\\alpha,1/u),\\\\"
        % deg_u
    )
    lines.append("r_0(\\alpha)&=%s,\\\\" % sp.latex(r0))
    lines.append("r_{%d}(\\alpha)&=%s,\\\\" % (deg_u, sp.latex(rd)))
    lines.append("r_1(\\alpha)&=%s,\\\\" % sp.latex(r1))
    lines.append("r_{%d}(\\alpha)&=%s,\\\\" % (deg_u - 1, sp.latex(rd1)))
    lines.append("R\\!\\left(\\tfrac12,u\\right)&=-\\frac{(u-1)^6}{64}\\,Q(u),\\\\")
    q_lines = _poly_multiline_tex(QZ, u, max_line_len=75)
    if len(q_lines) == 1:
        lines.append(f"Q(u)&={q_lines[0]}.")
    else:
        lines.append(f"Q(u)&={q_lines[0]}\\\\")
        for ln in q_lines[1:-1]:
            lines.append(f"&{ln}\\\\")
        lines.append(f"&{q_lines[-1]}.")
    lines.append("\\end{align}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Eliminate lambda to get R(alpha,u).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_rate_curve_resultant.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_rate_curve_resultant_degree.tex"),
    )
    parser.add_argument(
        "--structure-tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_rate_curve_resultant_structure.tex"),
    )
    args = parser.parse_args()

    t0 = time.time()
    lam = sp.Symbol("lam")
    u = sp.Symbol("u")
    alpha = sp.Symbol("alpha")

    F = _build_F(lam, u)
    Fl = sp.diff(F, lam)
    Fu = sp.diff(F, u)
    G = sp.expand(alpha * lam * Fl + u * Fu)

    # Eliminate lam by resultant. This can take time; print a heartbeat.
    print("[elim] building resultant R(alpha,u) ...", flush=True)
    t1 = time.time()
    R_raw = sp.resultant(F, G, lam)
    elapsed = time.time() - t1
    print(f"[elim] resultant computed in {elapsed:.3f}s", flush=True)

    PR_raw = sp.Poly(R_raw, alpha, u, domain="ZZ")
    # Normalize by removing the maximal u-power factor (u-adic valuation).
    Pu_raw = sp.Poly(PR_raw.as_expr(), u, domain=sp.ZZ[alpha])
    v_u = _u_adic_valuation(Pu_raw, u=u)
    R_norm_expr = sp.expand(Pu_raw.as_expr() / (u**v_u))
    PR = sp.Poly(R_norm_expr, alpha, u, domain="ZZ")

    deg_alpha = int(PR.degree(alpha))
    deg_u = int(PR.degree(u))
    n_terms = len(PR.terms())
    content = sp.Integer(sp.gcd_list(list(PR.coeffs()))) if PR.coeffs() else sp.Integer(0)

    # Leading term info under lex order (alpha > u).
    lt_monom, lt_coeff = PR.LT()
    leading_monomial = f"\\alpha^{{{lt_monom[0]}}}u^{{{lt_monom[1]}}}"
    leading_coeff = str(lt_coeff)

    summary = ResultantSummary(
        deg_alpha=deg_alpha,
        deg_u=deg_u,
        n_terms=n_terms,
        content_gcd=str(content),
        leading_monomial=leading_monomial,
        leading_coeff=leading_coeff,
        u_adic_valuation=int(v_u),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(summary), indent=2, sort_keys=True) + "\n", encoding="utf-8")
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

