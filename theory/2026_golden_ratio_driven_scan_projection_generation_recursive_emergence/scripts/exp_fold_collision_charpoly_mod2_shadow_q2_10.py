#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Mod-2 shadows of the audited Fold collision moment recurrences (q=2..10).

From exact integer recurrences for S_q(m) in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
we form the characteristic polynomial
  P_q(λ) = λ^d - c_1 λ^{d-1} - ... - c_d.

Reducing coefficients modulo 2 defines an element of F_2[λ]. In the audited window
q=2..10, these mod-2 polynomials collapse to pure powers of λ and (λ+1):
  P_q(λ) (mod 2) = λ^{a_q} (λ+1)^{b_q}.

Outputs:
  - artifacts/export/fold_collision_charpoly_mod2_shadow_q2_10.json
  - sections/generated/tab_fold_collision_charpoly_mod2_shadow_q2_10.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from exp_fold_collision_moment_recursions import RECS as RECS_2_8
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17


def _poly_from_coeffs(coeffs: List[int]) -> sp.Expr:
    d = len(coeffs)
    lam = sp.Symbol("lambda")
    poly = lam**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * lam ** (d - i)
    return sp.expand(poly)


def _mod2_poly(poly: sp.Expr) -> sp.Poly:
    lam = sp.Symbol("lambda")
    return sp.Poly(poly, lam, modulus=2)


def _factor_ab_mod2(P2: sp.Poly) -> Tuple[int, int, sp.Expr]:
    """Return (a,b,factored_expr) where P2 = λ^a (λ+1)^b in F_2[λ]."""
    lam = sp.Symbol("lambda")
    coeff, factors = sp.factor_list(P2.as_expr(), modulus=2)
    if int(coeff) % 2 != 1:
        raise RuntimeError(f"Unexpected leading unit in F2 factorization: coeff={coeff}")
    a = 0
    b = 0
    for f, e in factors:
        fP = sp.Poly(f, lam, modulus=2)
        if fP.degree() == 1 and fP.all_coeffs() == [1, 0]:
            a += int(e)
            continue
        if fP.degree() == 1 and fP.all_coeffs() == [1, 1]:
            b += int(e)
            continue
        raise RuntimeError(f"Unexpected non-(λ),(λ+1) factor over F2: {f} ^ {e}")
    return a, b, sp.factor(P2.as_expr(), modulus=2)


@dataclass(frozen=True)
class Row:
    q: int
    order_d: int
    mod2_poly_expr: str
    a_q: int
    b_q: int
    mod2_factor_expr: str
    annihilator_E: str


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Mod-2 shadows of the audited Fold collision moment characteristic polynomials "
        "$P_q(\\lambda)$ for $q=2,\\dots,10$. "
        "The reduction $P_q(\\lambda)\\ (\\mathrm{mod}\\ 2)$ factors in $\\mathbb{F}_2[\\lambda]$ "
        "as $\\lambda^{a_q}(\\lambda+1)^{b_q}$, yielding the annihilator "
        "$E^{a_q}(E+1)^{b_q}S_q\\equiv 0\\ (\\mathrm{mod}\\ 2)$ for the forward shift $E$.}"
    )
    lines.append("\\label{tab:fold_collision_charpoly_mod2_shadow_q2_10}")
    lines.append("\\begin{tabular}{r r l l l}")
    lines.append("\\toprule")
    lines.append("$q$ & order $d_q$ & $P_q(\\lambda)\\ (\\mathrm{mod}\\ 2)$ & factorization in $\\mathbb{F}_2[\\lambda]$ & annihilator\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.order_d} & ${r.mod2_poly_expr}$ & ${r.mod2_factor_expr}$ & ${r.annihilator_E}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute mod-2 factorizations of P_q for q=2..10.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_charpoly_mod2_shadow_q2_10.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_charpoly_mod2_shadow_q2_10.tex"),
    )
    args = ap.parse_args()

    # Collect coefficients for q=2..8 from the audited exact recurrences, and q=9,10
    # from the precomputed modular-DP audit records.
    coeffs_by_q: dict[int, List[int]] = {}
    for rec in RECS_2_8:
        k = int(rec.k)
        if 2 <= k <= 8:
            coeffs_by_q[k] = [int(x) for x in rec.coeffs]
    for rec in PRECOMPUTED_RECS_9_17:
        k = int(rec["k"])
        if k in {9, 10}:
            coeffs_by_q[k] = [int(x) for x in rec["coeffs"]]

    rows_out: List[Row] = []
    for q in sorted(coeffs_by_q.keys()):
        coeffs = coeffs_by_q[q]
        poly = _poly_from_coeffs(coeffs)
        P2 = _mod2_poly(poly)
        a, b, fexpr = _factor_ab_mod2(P2)
        d = len(coeffs)
        if a + b != d:
            raise RuntimeError(f"Bad (a,b) sum for q={q}: a+b={a+b} != d={d}")

        lam = sp.Symbol("lambda")
        mod2_expr = sp.latex(sp.Poly(P2.as_expr(), lam, modulus=2).as_expr())
        fac_expr = sp.latex(fexpr)
        annih = sp.latex(lam**a * (lam + 1) ** b).replace("\\lambda", "E")

        rows_out.append(
            Row(
                q=q,
                order_d=d,
                mod2_poly_expr=mod2_expr,
                a_q=a,
                b_q=b,
                mod2_factor_expr=fac_expr,
                annihilator_E=annih,
            )
        )

        print(f"[charpoly-mod2] q={q:2d} d={d:2d} P(mod2) = lambda^{a} (lambda+1)^{b}", flush=True)

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": [asdict(r) for r in rows_out]}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[charpoly-mod2] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    write_table_tex(tout, rows_out)
    print(f"[charpoly-mod2] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

