#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Cyclotomic elimination for mod-m prime-shadow error exponents of the weighted sync-kernel.

We work with the weighted zeta of the 10-state sync-kernel:
  B(u) = B0 + u B1,  Δ(z,u)=det(I - z B(u)),  ζ(z,u)=1/Δ(z,u),
where u tracks the output-bit count along an orbit.

The appendix gives the Perron root λ(u) as the largest-modulus root of a degree-6 polynomial:
  F(λ,u)=0  in Z[u][λ],
and Δ(z,u) = z^6 F(1/z, u) (since only 6 eigenvalues are nonzero).

This script builds the "completion" invariant variables:
  u = r^2,   s = r + r^{-1} (invariant under r -> r^{-1}),   w = z r (invariant under u->1/u symmetry).
It then constructs an invariant determinant polynomial:
  Δ̂(w,s) in Z[s][w]  such that  Δ̂(w, r + r^{-1}) = Δ(w/r, r^2).

For a given modulus m>=3, set
  s_m = 2 cos(pi/m),  Φ_m^+(s) = minpoly(s_m) in Z[s],
and define the cyclotomic elimination polynomial
  R_m(w) = Res_s( Δ̂(w,s), Φ_m^+(s) ) in Z[w].

Numerically (and in the paper's conventions), the prime-shadow residue-class mixing exponent is:
  ρ_m = max_{r=1..m-1} |λ(ω_m^r)| = 1 / min{|w| : R_m(w)=0}.

We also compare ρ_m against the pressure-based asymptotic prediction from the appendix:
  Re P(i t) = log 3 - (11/204) t^2 + (1559/1414944) t^4 + (17123893/1177686190080) t^6
             - (122803509253/25412897733672960) t^8 + (518906628614669/10575831520845339033600) t^10
             + (24353138488976295223/880247609142999258444595200) t^12 + O(t^14),
  t=2π/m.

Outputs (default):
  - artifacts/export/sync_kernel_cyclotomic_elimination.json
  - sections/generated/tab_sync_kernel_cyclotomic_elimination_summary.tex
  - sections/generated/tab_sync_kernel_cyclotomic_elimination_polys.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def poly_F(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # From appendix: `sections/appendix/sync_kernel/weighted/cor__sync-kernel-weighted-unit-root-finite.tex`, Eq. F(λ,u)=0 (app:pressure-analytic).
    return (
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )


def poly_Delta(z: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    lam = sp.Symbol("lam")
    F = poly_F(lam, u)
    return sp.expand(z**6 * F.subs(lam, 1 / z))


def completion_hat_delta(*, prog: Progress) -> sp.Expr:
    """
    Construct Δ̂(w,s) in Z[s][w] with the defining identity:
      Δ̂(w, r + r^{-1}) = Δ(w/r, r^2).
    """
    w, s, r, z, u = sp.symbols("w s r z u")
    Delta = poly_Delta(z, u)

    # D(r) := Δ(w/r, r^2) is invariant under r -> 1/r (w fixed), hence depends only on s=r+r^{-1}.
    D = sp.together(Delta.subs({z: w / r, u: r**2}))
    num = sp.factor(sp.together(D).as_numer_denom()[0])

    rel = r**2 - s * r + 1  # r + r^{-1} = s
    prog.tick("computing resultant to eliminate r (completion)")
    res = sp.resultant(num, rel, r)

    # The resultant may be a perfect square (quadratic elimination). Take squarefree part and normalize.
    res = sp.factor(sp.Poly(res, w, s).primitive()[1].as_expr())
    sqf = sp.factor(sp.Poly(res, w, s).sqf_part().as_expr())

    # Choose the factor that is degree 6 in w (the determinant degree).
    facs = sp.factor_list(sqf)[1]
    cand: sp.Expr | None = None
    for f, e in facs:
        fw = sp.Poly(f, w, s)
        if fw.total_degree() == 0:
            continue
        if fw.degree(w) == 6:
            cand = f
            break
    if cand is None:
        # Fallback: use the whole squarefree polynomial.
        cand = sqf
    cand = sp.Poly(cand, w, s).primitive()[1].as_expr()
    # Normalize sign by making leading coefficient in w positive.
    lc = sp.Poly(cand, w, s).LC()
    if sp.sign(lc) == -1:
        cand = -cand
    prog.tick("completion Δ̂(w,s) built")
    return sp.factor(cand)


def phi_m_plus(m: int, s: sp.Symbol) -> sp.Expr:
    # Minimal polynomial of s_m = 2 cos(pi/m).
    # Sympy returns a monic integer polynomial in s.
    return sp.minimal_polynomial(2 * sp.cos(sp.pi / m), s)


def resultant_Rm(hatDelta: sp.Expr, m: int, *, prog: Progress) -> sp.Poly:
    w, s = sp.symbols("w s")
    Phi = phi_m_plus(m, s)
    prog.tick(f"computing resultant for m={m}")
    R = sp.resultant(sp.Poly(hatDelta, w, s), sp.Poly(Phi, s), s)
    R = sp.Poly(R, w)
    # Primitive integer polynomial normalization.
    R = sp.Poly(R.primitive()[1], w)
    if sp.sign(R.LC()) == -1:
        R = -R
    return R


def roots_min_modulus(R: sp.Poly, prec: int = 80) -> Tuple[float, List[complex]]:
    w = R.gens[0]
    rr = [complex(r) for r in sp.nroots(R.as_expr(), n=prec)]  # type: ignore[arg-type]
    rr_abs = [(abs(z), z) for z in rr]
    rr_abs.sort(key=lambda t: t[0])
    return float(rr_abs[0][0]), rr


def rho_exact_from_F(m: int, *, prog: Progress, prec: int = 80) -> float:
    lam, u = sp.symbols("lam u")
    F = sp.Poly(poly_F(lam, u), lam)

    best = 0.0
    for r in range(1, m):
        angle = 2.0 * math.pi * r / m
        u0 = complex(math.cos(angle), math.sin(angle))
        # Substitute u=u0 into F and solve for roots in λ.
        Fr = sp.Poly(F.as_expr().subs(u, sp.nsimplify(u0)), lam)
        # nsimplify(u0) may fail to keep it numeric; fallback to complex float.
        if not all(isinstance(c, (sp.Number, sp.Expr)) for c in Fr.all_coeffs()):
            Fr = sp.Poly(F.as_expr().subs(u, u0), lam)
        roots = [complex(z) for z in sp.nroots(Fr.as_expr(), n=prec)]  # type: ignore[arg-type]
        mx = max(abs(z) for z in roots)
        if mx > best:
            best = mx
        prog.tick(f"m={m} r={r}/{m-1} |λ|max≈{mx:.12f} best≈{best:.12f}")
    return best


def rho_pred_from_pressure(m: int) -> float:
    t = 2.0 * math.pi / m
    # Re P(i t) ≈ log 3 - a2 t^2 + a4 t^4 + a6 t^6 - a8 t^8 + a10 t^10.
    a2 = 11.0 / 204.0
    a4 = 1559.0 / 1414944.0
    a6 = 17123893.0 / 1177686190080.0
    a8 = 122803509253.0 / 25412897733672960.0
    a10 = 518906628614669.0 / 10575831520845339033600.0
    a12 = 24353138488976295223.0 / 880247609142999258444595200.0
    return 3.0 * math.exp(
        -(a2) * (t**2)
        + a4 * (t**4)
        + a6 * (t**6)
        - a8 * (t**8)
        + a10 * (t**10)
        + a12 * (t**12)
    )


def poly_to_compact_latex(P: sp.Poly, var: str = "w") -> str:
    w = sp.Symbol(var)
    expr = sp.expand(P.as_expr().subs(P.gens[0], w))
    return sp.latex(expr)


def write_summary_table(path: Path, rows: List[Dict[str, object]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Cyclotomic elimination for mod-$m$ prime-shadow mixing exponents of the weighted sync-kernel. "
        "$R_m(w)$ is an integer resultant polynomial; $\\rho_m$ is obtained as $\\rho_m=1/\\min\\{|w|:R_m(w)=0\\}$. "
        "We also list the pressure-based prediction $\\rho_m^{\\mathrm{pred}}$ from the Taylor expansion of $P(\\theta)$.}"
    )
    lines.append("\\label{tab:sync_kernel_cyclotomic_elimination_summary}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $\\deg R_m$ & $\\rho_m$ (resultant) & $\\rho_m^{\\mathrm{pred}}$ & abs err\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{int(r['m'])} & {int(r['deg'])} & {float(r['rho']):.12f} & {float(r['rho_pred']):.12f} & {float(r['abs_err']):.3e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_polys_tex(path: Path, polys: Dict[int, sp.Poly]) -> None:
    def _poly_multiline_tex(P: sp.Poly, var: sp.Symbol, *, max_line_len: int = 110) -> List[str]:
        """Format a univariate integer polynomial as multiple TeX lines.

        Output lines are meant to be used inside an amsmath aligned environment.
        """
        # Collect terms in descending degree order.
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

        # Greedy line packing by character length.
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

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_cyclotomic_elimination.py")
    lines.append("\\begin{align*}")
    for m in sorted(polys.keys()):
        P = polys[m]
        tex_lines = _poly_multiline_tex(P, sp.Symbol("w"))
        if len(tex_lines) == 1:
            lines.append(f"R_{{{m}}}(w)&={tex_lines[0]}\\\\")
            continue
        lines.append(f"R_{{{m}}}(w)&=\\begin{{aligned}}[t]")
        for j, ln in enumerate(tex_lines):
            if j < len(tex_lines) - 1:
                lines.append(f"& {ln}\\\\")
            else:
                lines.append(f"& {ln}")
        lines.append("\\end{aligned}\\\\")
    lines.append("\\end{align*}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Cyclotomic elimination for sync-kernel weighted zeta.")
    parser.add_argument("--m-list", type=str, default="3,4,5,6,7,8,9,10,11,12", help="Comma-separated m values.")
    parser.add_argument("--prec", type=int, default=80, help="Working precision for nroots.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_cyclotomic_elimination.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-summary-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_cyclotomic_elimination_summary.tex"),
        help="Output LaTeX summary table.",
    )
    parser.add_argument(
        "--tex-polys-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_cyclotomic_elimination_polys.tex"),
        help="Output LaTeX polynomial block.",
    )
    args = parser.parse_args()

    m_list = [int(x.strip()) for x in str(args.m_list).split(",") if x.strip()]
    if any(m < 3 for m in m_list):
        raise SystemExit("Require m >= 3")

    prog = Progress("cyclotomic-elim", every_seconds=20.0)

    hatDelta = completion_hat_delta(prog=prog)
    w, s = sp.symbols("w s")

    rows: List[Dict[str, object]] = []
    polys: Dict[int, sp.Poly] = {}
    for m in m_list:
        Rm = resultant_Rm(hatDelta, m, prog=prog)
        polys[m] = Rm
        min_mod, roots = roots_min_modulus(Rm, prec=int(args.prec))
        rho = 1.0 / min_mod
        rho_pred = rho_pred_from_pressure(m)
        rows.append(
            {
                "m": m,
                "deg": int(Rm.degree()),
                "rho": float(rho),
                "rho_pred": float(rho_pred),
                "abs_err": float(abs(rho - rho_pred)),
            }
        )
        prog.tick(f"m={m} rho(resultant)≈{rho:.12f} rho(pred)≈{rho_pred:.12f}")

    payload: Dict[str, object] = {
        "m_list": m_list,
        "hatDelta_ws": sp.srepr(hatDelta),
        "R_m": {
            str(m): [int(c) for c in sp.Poly(polys[m]).all_coeffs()]  # JSON-safe
            for m in m_list
        },
        "rows": rows,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[cyclotomic-elim] wrote {jout}", flush=True)

    write_summary_table(Path(args.tex_summary_out), rows)
    print(f"[cyclotomic-elim] wrote {args.tex_summary_out}", flush=True)

    write_polys_tex(Path(args.tex_polys_out), polys)
    print(f"[cyclotomic-elim] wrote {args.tex_polys_out}", flush=True)

    print("[cyclotomic-elim] done", flush=True)


if __name__ == "__main__":
    main()

