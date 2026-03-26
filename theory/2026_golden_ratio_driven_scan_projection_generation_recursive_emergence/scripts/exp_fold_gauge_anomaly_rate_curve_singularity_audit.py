#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit singularity structure for the fold gauge-anomaly rate-curve elimination model.

Scope:
- Build the normalized elimination polynomial R(alpha,u) from F(mu,u)=0 and
  alpha*mu*F_mu + u*F_u = 0.
- Compute the affine singular-locus elimination in u via Groebner elimination:
  <R, R_alpha, R_u> intersect Q[u].
- Verify the u-projection factor u^5 * D19(u).
- Extract local leading forms at:
  (alpha,u)=(0,0), (1/2,0), and (alpha,u)=(1, infinity).
- Verify that all 19 D19-fiber singular points are nondegenerate double points
  by checking Hessian determinant != 0 numerically.

Outputs:
- artifacts/export/fold_gauge_anomaly_rate_curve_singularity_audit.json
- sections/generated/eq_fold_gauge_anomaly_rate_curve_singularity_audit.tex
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def _build_F(mu: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    return mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u


def _build_D19(u: sp.Symbol) -> sp.Poly:
    expr = (
        137781 * u**19
        + 629856 * u**18
        + 934578 * u**17
        - 1546209 * u**16
        - 6187752 * u**15
        + 1402704 * u**14
        + 15349014 * u**13
        - 3368736 * u**12
        - 17688806 * u**11
        + 2216732 * u**10
        + 17425320 * u**9
        - 4765670 * u**8
        - 11620472 * u**7
        + 7448180 * u**6
        + 2529720 * u**5
        - 4736240 * u**4
        + 2386300 * u**3
        - 612800 * u**2
        + 81800 * u
        - 4500
    )
    return sp.Poly(sp.expand(expr), u, domain="ZZ")


def _normalized_R(alpha: sp.Symbol, mu: sp.Symbol, u: sp.Symbol) -> sp.Poly:
    F = _build_F(mu, u)
    F_mu = sp.diff(F, mu)
    F_u = sp.diff(F, u)
    G = sp.expand(alpha * mu * F_mu + u * F_u)

    print("[rate-curve-singularity-audit] resultant build start", flush=True)
    t0 = time.time()
    R_raw = sp.resultant(F, G, mu)
    print(
        f"[rate-curve-singularity-audit] resultant built in {time.time() - t0:.3f}s",
        flush=True,
    )

    PR_raw = sp.Poly(R_raw, alpha, u, domain="ZZ")
    Pu_raw = sp.Poly(PR_raw.as_expr(), u, domain=sp.ZZ[alpha])
    v_u = min(int(mon[0]) for mon, coeff in Pu_raw.terms() if coeff != 0)
    R1 = sp.expand(Pu_raw.as_expr() / (u**v_u))
    PR1 = sp.Poly(R1, alpha, u, domain="ZZ")
    content = sp.gcd_list(PR1.coeffs()) if PR1.coeffs() else sp.Integer(1)
    R = sp.Poly(sp.expand(PR1.as_expr() / content), alpha, u, domain="ZZ")
    return R


def _minimal_total_degree_part(expr: sp.Expr, x: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    P = sp.Poly(sp.expand(expr), x, y, domain="QQ")
    terms = [(mon, coeff) for mon, coeff in P.terms() if coeff != 0]
    min_deg = min(mon[0] + mon[1] for mon, _ in terms)
    out = sp.Integer(0)
    for mon, coeff in terms:
        if mon[0] + mon[1] == min_deg:
            out += coeff * x**mon[0] * y**mon[1]
    return sp.expand(out)


def main() -> None:
    start = time.time()
    print("[rate-curve-singularity-audit] start", flush=True)

    alpha, mu, u = sp.symbols("alpha mu u")
    R = _normalized_R(alpha=alpha, mu=mu, u=u)
    R_expr = sp.expand(R.as_expr())
    R_alpha = sp.expand(sp.diff(R_expr, alpha))
    R_u = sp.expand(sp.diff(R_expr, u))
    R_aa = sp.expand(sp.diff(R_alpha, alpha))
    R_au = sp.expand(sp.diff(R_alpha, u))
    R_uu = sp.expand(sp.diff(R_u, u))

    print("[rate-curve-singularity-audit] groebner elimination start", flush=True)
    t1 = time.time()
    G = sp.groebner([R_expr, R_alpha, R_u], [alpha, u], order="lex", domain=sp.QQ)
    print(
        f"[rate-curve-singularity-audit] groebner elimination done in {time.time() - t1:.3f}s",
        flush=True,
    )

    basis_exprs = [sp.expand(p.as_expr()) for p in G.polys]
    univariate = [p for p in basis_exprs if p.free_symbols == {u}]
    if len(univariate) != 1:
        raise RuntimeError("Expected exactly one univariate elimination polynomial.")
    elim_u_expr = sp.expand(univariate[0])
    elim_u_poly = sp.Poly(elim_u_expr, u, domain="QQ")

    linear_alpha = [p for p in basis_exprs if p.has(alpha) and sp.Poly(p, alpha, u).degree(alpha) == 1]
    if len(linear_alpha) != 1:
        raise RuntimeError("Expected exactly one alpha-linear Groebner basis polynomial.")
    lin_expr = sp.expand(linear_alpha[0])
    coeff_alpha = sp.expand(sp.diff(lin_expr, alpha))
    if sp.simplify(coeff_alpha - u**4) != 0:
        raise RuntimeError("Unexpected alpha-coefficient in Groebner linear relation.")
    phi_u = sp.expand(lin_expr - alpha * u**4)

    D19 = _build_D19(u)
    singular_u_target = sp.expand(u**5 * D19.as_expr())
    ratio = sp.simplify(elim_u_expr / singular_u_target)
    if ratio == 0:
        raise RuntimeError("Unexpected zero ratio in elimination check.")
    if sp.simplify(elim_u_expr - ratio * singular_u_target) != 0:
        raise RuntimeError("u-elimination polynomial does not match u^5*D19 up to scalar.")

    R_u0_factor = sp.factor(sp.expand(R_expr.subs(u, 0)))

    c = sp.symbols("c")
    local_p0 = sp.expand(R_expr.subs(alpha, c * u**3))
    P0 = sp.Poly(local_p0, u, domain="QQ[c]")
    p0_min_deg = min(int(mon[0]) for mon, coeff in P0.terms() if coeff != 0)
    p0_leading_coeff = sp.factor(sp.expand(P0.coeff_monomial(u**p0_min_deg)))
    p0_c_roots = [sp.simplify(r) for r in sp.solve(sp.Eq(p0_leading_coeff, 0), c)]

    k, s = sp.symbols("k s")
    local_half = sp.expand(R_expr.subs({alpha: sp.Rational(1, 2) + k * s**5, u: s**2}))
    P_half = sp.Poly(local_half, s, domain="QQ[k]")
    half_min_deg = min(int(mon[0]) for mon, coeff in P_half.terms() if coeff != 0)
    half_leading_coeff = sp.factor(sp.expand(P_half.coeff_monomial(s**half_min_deg)))
    half_k_roots = [sp.simplify(r) for r in sp.solve(sp.Eq(half_leading_coeff, 0), k)]

    beta, v = sp.symbols("beta v")
    inf_local = sp.expand((v**11) * R_expr.subs({alpha: 1 + beta, u: 1 / v}))
    inf_initial = sp.factor(_minimal_total_degree_part(inf_local, beta, v))

    roots_d19 = list(sp.nroots(D19, n=100, maxsteps=300))
    max_residual = 0.0
    min_abs_hdet = None
    for ur in roots_d19:
        ur_num = sp.N(ur, 90)
        alpha_num = sp.N(-phi_u.subs(u, ur_num) / (ur_num**4), 90)
        vals = [
            sp.N(R_expr.subs({alpha: alpha_num, u: ur_num}), 70),
            sp.N(R_alpha.subs({alpha: alpha_num, u: ur_num}), 70),
            sp.N(R_u.subs({alpha: alpha_num, u: ur_num}), 70),
        ]
        local_max = max(abs(complex(vv)) for vv in vals)
        max_residual = max(max_residual, local_max)

        hdet = sp.N((R_aa * R_uu - R_au**2).subs({alpha: alpha_num, u: ur_num}), 70)
        abs_hdet = abs(complex(hdet))
        min_abs_hdet = abs_hdet if min_abs_hdet is None else min(min_abs_hdet, abs_hdet)

    if min_abs_hdet is None:
        raise RuntimeError("No D19 roots found.")

    hdet_u0_a0 = sp.simplify((R_aa * R_uu - R_au**2).subs({alpha: 0, u: 0}))
    hdet_u0_ahalf = sp.simplify((R_aa * R_uu - R_au**2).subs({alpha: sp.Rational(1, 2), u: 0}))

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "seconds": float(time.time() - start),
        },
        "R_summary": {
            "deg_alpha": int(R.degree(alpha)),
            "deg_u": int(R.degree(u)),
            "R_alpha_u0_factorized": str(R_u0_factor),
        },
        "singular_elimination": {
            "groebner_univariate_u": str(elim_u_expr),
            "target_u5D19": str(singular_u_target),
            "ratio": str(sp.simplify(ratio)),
            "alpha_linear_relation": str(lin_expr),
            "phi_u": str(phi_u),
        },
        "local_forms": {
            "P0": {
                "ansatz": "alpha = c*u^3",
                "leading_u_degree": int(p0_min_deg),
                "leading_coeff_in_c": str(p0_leading_coeff),
                "c_roots": [str(r) for r in p0_c_roots],
            },
            "P_half": {
                "ansatz": "u = s^2, alpha = 1/2 + k*s^5",
                "leading_s_degree": int(half_min_deg),
                "leading_coeff_in_k": str(half_leading_coeff),
                "k_roots": [str(r) for r in half_k_roots],
            },
            "P_infinity": {
                "chart": "v=1/u, beta=alpha-1, equation v^11*R(1+beta,1/v)=0",
                "initial_form": str(inf_initial),
            },
        },
        "node_checks_over_D19": {
            "roots_count": int(len(roots_d19)),
            "max_abs_residual_R_Ra_Ru": float(max_residual),
            "min_abs_hessian_det": float(min_abs_hdet),
            "hessian_det_at_(0,0)": str(hdet_u0_a0),
            "hessian_det_at_(1/2,0)": str(hdet_u0_ahalf),
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_rate_curve_singularity_audit.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_lines: List[str] = []
    tex_lines.append("% Auto-generated by exp_fold_gauge_anomaly_rate_curve_singularity_audit.py")
    tex_lines.append("\\begin{align}")
    tex_lines.append(
        "R(\\alpha,0)&=%s,\\\\"
        % sp.latex(R_u0_factor)
    )
    tex_lines.append(
        "\\langle R,R_{\\alpha},R_u\\rangle\\cap\\QQ[u]"
        "&=\\left\\langle u^5 D_{19}(u)\\right\\rangle,\\\\"
    )
    tex_lines.append(
        "R(cu^3,u)&=\\left(%s\\right)u^%d+O\\!\\left(u^{%d}\\right),\\\\"
        % (sp.latex(p0_leading_coeff), p0_min_deg, p0_min_deg + 1)
    )
    tex_lines.append(
        "R\\!\\left(\\tfrac12+ks^5,s^2\\right)"
        "&=\\left(%s\\right)s^%d+O\\!\\left(s^{%d}\\right),\\\\"
        % (sp.latex(half_leading_coeff), half_min_deg, half_min_deg + 1)
    )
    tex_lines.append(
        "v^{11}R(1+\\beta,1/v)&=%s+\\text{(higher total degree)}."
        % sp.latex(inf_initial)
    )
    tex_lines.append("\\end{align}")
    out_tex = generated_dir() / "eq_fold_gauge_anomaly_rate_curve_singularity_audit.tex"
    out_tex.parent.mkdir(parents=True, exist_ok=True)
    out_tex.write_text("\n".join(tex_lines) + "\n", encoding="utf-8")

    print(f"[rate-curve-singularity-audit] wrote {out_json}", flush=True)
    print(f"[rate-curve-singularity-audit] wrote {out_tex}", flush=True)
    print(
        f"[rate-curve-singularity-audit] done seconds={time.time() - start:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()
