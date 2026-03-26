#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Derive the completed (s,y)-curve Q(s,y)=0 from the 6th-degree Perron equation F(lambda,u)=0.

We start from the paper's polynomial:
  F(λ,u)=λ^6-(1+u)λ^5-5uλ^4+3u(1+u)λ^3
        -u(u^2-3u+1)λ^2+u(u^3-3u^2-3u+1)λ+u^2(u^2+u+1).

Completion variables:
  u = r^2,
  y = λ / r,
  s = r + r^{-1}.

Then r^{-6}F(r y, r^2) is invariant under r -> 1/r, hence lies in Q[s,y].
This script computes the resulting polynomial Q(s,y) with integer coefficients,
writes a LaTeX snippet, and exports JSON metadata.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Out:
    Q_latex: str
    Q_expanded: str


def _chebyshev_Ck_in_s(k: int, s: sp.Symbol) -> sp.Expr:
    """C_k(s)=r^k+r^{-k} as polynomial in s=r+r^{-1}."""
    if k < 0:
        raise ValueError("k must be >= 0")
    if k == 0:
        return sp.Integer(2)
    if k == 1:
        return s
    Ckm1 = sp.Integer(2)
    Ck = s
    for _ in range(1, k):
        Ckp1 = sp.expand(s * Ck - Ckm1)
        Ckm1, Ck = Ck, Ckp1
    return Ck


def main() -> None:
    parser = argparse.ArgumentParser(description="Derive completed Q(s,y) curve from F(lambda,u)=0.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_completion_Q_sy.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_weighted_completion_Q_sy.tex"),
    )
    args = parser.parse_args()

    lam, u = sp.symbols("lam u")
    r, y, s = sp.symbols("r y s")

    # Define F(lam,u) exactly as in the paper.
    F = (
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )

    # Completion substitution.
    expr = sp.expand(F.subs({u: r**2, lam: r * y}))
    # Eliminate r using s=r+r^{-1} <=> r^2 - s r + 1 = 0.
    # This is robust and produces the completed curve Q(s,y)=0.
    print("[completion-Q] computing resultant (may take a few seconds)...", flush=True)
    poly_r = sp.Poly(expr, r, domain=sp.ZZ[y])
    rel = sp.Poly(r**2 - s * r + 1, r, domain=sp.ZZ[s])
    res = sp.resultant(poly_r, rel, r)
    res = sp.factor(res)

    # Pick the factor that vanishes at (s=2,y=3), corresponding to u=1, r=1, λ(1)=3.
    factors = sp.factor_list(res)[1]
    target = None
    for fac, mult in factors:
        val = sp.simplify(fac.subs({s: 2, y: 3}))
        if val == 0:
            target = fac
            break
    if target is None:
        raise RuntimeError("Failed to select the correct resultant factor at (s,y)=(2,3).")

    Q = sp.expand(target)
    # Put in Z[s,y] with content normalized to gcd 1 and leading sign fixed.
    P = sp.Poly(Q, s, y, domain=sp.QQ)
    content = sp.Integer(0)
    for c in P.coeffs():
        num = sp.Integer(sp.factor(c).as_numer_denom()[0])
        content = abs(num) if content == 0 else sp.gcd(content, abs(num))
    if content not in (0, 1):
        P = sp.Poly(P.as_expr() / content, s, y, domain=sp.QQ)
    # Clear denominators (should already be integers).
    den_lcm = sp.ilcm(*[sp.denom(c) for c in P.coeffs()]) if P.coeffs() else 1
    P = sp.Poly(sp.expand(P.as_expr() * den_lcm), s, y, domain=sp.ZZ)
    # Fix overall sign for a stable representation: make y^6 coefficient positive.
    if P.coeff_monomial(y**6) < 0:
        P = sp.Poly(-P.as_expr(), s, y, domain=sp.ZZ)

    Q_final = sp.expand(P.as_expr())
    Q_latex = sp.latex(Q_final)

    out = Out(Q_latex=Q_latex, Q_expanded=str(Q_final))

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(out), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[completion-Q] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)

    def _latex_multiline(tex: str, *, max_line_len: int = 95) -> List[str]:
        """Split a TeX polynomial string into multiple lines (greedy by length)."""
        s = tex.strip()
        # Turn binary '-' into an additive signed term to split on ' + ' safely.
        s = s.replace(" - ", " + - ")
        raw = [p.strip() for p in s.split(" + ") if p.strip()]
        if not raw:
            return ["0"]
        terms: List[str] = []
        for i, p in enumerate(raw):
            if i == 0:
                terms.append(p)
                continue
            if p.startswith("-"):
                terms.append("- " + p[1:].lstrip())
            else:
                terms.append("+ " + p)

        out_lines: List[str] = []
        cur = terms[0]
        for t in terms[1:]:
            if len(cur) + 1 + len(t) > max_line_len:
                out_lines.append(cur)
                cur = t
            else:
                cur = cur + " " + t
        out_lines.append(cur)
        return out_lines

    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{equation}")
    lines.append("\\boxed{")
    lines.append("\\begin{aligned}")
    poly_lines = _latex_multiline(Q_latex, max_line_len=70)
    for i, ln in enumerate(poly_lines):
        if i < len(poly_lines) - 1:
            lines.append(f"& {ln}\\\\")
        else:
            lines.append(f"& {ln}=0")
    lines.append("\\end{aligned}")
    lines.append("}")
    lines.append("\\end{equation}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[completion-Q] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

