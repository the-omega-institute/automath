#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Mod-5 branching fingerprints for audited Fold collision moment characteristic polynomials.

Even within the odd-q class, the mod-5 factorization distinguishes q=13 from q=15:
  - q=13: contains a nontrivial zero-eigenvalue factor λ^2 (two-step nil component).
  - q=15: no λ factor (no zero-mode in F_5).

From the audited exact integer recurrences for S_q(m) in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
we form the characteristic polynomial
  P_q(λ) = λ^d - c_1 λ^{d-1} - ... - c_d,
and factor it in F_5[λ].

Outputs:
  - artifacts/export/fold_collision_charpoly_mod5_branch_q13_15.json
  - sections/generated/tab_fold_collision_charpoly_mod5_branch_q13_15.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)

from common_paths import export_dir, generated_dir
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17


def _poly_from_coeffs(coeffs: Sequence[int]) -> sp.Expr:
    d = len(coeffs)
    lam = sp.Symbol("lambda")
    poly = lam**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * lam ** (d - i)
    return sp.expand(poly)


def _format_root_for_latex(root: int, p: int) -> str:
    if p == 5:
        r = root % 5
        if r == 4:
            return "-1"
        if r == 3:
            return "-2"
        return str(r)
    return str(root % p)


def _linear_spectrum_from_factors(factors: List[Tuple[sp.Expr, int]], p: int) -> str:
    lam = sp.Symbol("lambda")
    mult: Dict[int, int] = {}
    for f, e in factors:
        fp = sp.Poly(f, lam, modulus=p)
        if fp.degree() != 1:
            continue
        coeffs = [int(x) % p for x in fp.all_coeffs()]
        if len(coeffs) != 2 or coeffs[0] % p != 1:
            continue
        b = coeffs[1] % p
        root = (-b) % p
        mult[root] = mult.get(root, 0) + int(e)

    parts: List[str] = []
    for r in sorted(mult.keys()):
        e = mult[r]
        if e <= 0:
            continue
        rr = _format_root_for_latex(r, p)
        rr_tex = f"({rr})" if rr.startswith("-") else rr
        parts.append(f"{rr_tex}^{{{e}}}")
    return ",\\,".join(parts) if parts else "\\varnothing"


def _zero_multiplicity_from_factors(factors: List[Tuple[sp.Expr, int]], p: int) -> int:
    lam = sp.Symbol("lambda")
    for f, e in factors:
        fp = sp.Poly(f, lam, modulus=p)
        if fp.degree() == 1 and [int(x) % p for x in fp.all_coeffs()] == [1, 0]:
            return int(e)
    return 0


@dataclass(frozen=True)
class Row:
    q: int
    order_d: int
    mod5_factor_expr: str
    linear_spectrum: str
    zero_mult: int
    annihilator_E: str


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Mod-5 branching fingerprints of the audited Fold collision moment characteristic polynomials "
        "$P_q(\\lambda)$ for $q=13,15$. The mod-5 factorization distinguishes the presence/absence of "
        "a zero-eigenvalue factor $\\lambda^{a_0}$ (a nil component) within the same odd-$q$ class.}"
    )
    lines.append("\\label{tab:fold_collision_charpoly_mod5_branch_q13_15}")
    lines.append("\\begin{tabular}{r r l r l}")
    lines.append("\\toprule")
    lines.append("$q$ & order $d_q$ & factorization in $\\mathbb{F}_5[\\lambda]$ & $a_0$ & annihilator\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.order_d} & ${r.mod5_factor_expr}$ & {r.zero_mult} & ${r.annihilator_E}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _pick_rec(q: int) -> Dict[str, object]:
    for rec in PRECOMPUTED_RECS_9_17:
        if int(rec["k"]) == int(q):
            return rec
    raise KeyError(f"Missing precomputed recurrence for q={q}")


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute mod-5 factorizations of P_q for q=13,15.")
    ap.add_argument("--q-list", type=str, default="13,15", help="Comma-separated q list.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_charpoly_mod5_branch_q13_15.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_charpoly_mod5_branch_q13_15.tex"),
    )
    args = ap.parse_args()

    q_list = [int(x.strip()) for x in str(args.q_list).split(",") if x.strip()]
    p = 5
    lam = sp.Symbol("lambda")

    rows_out: List[Row] = []
    for q in q_list:
        rec = _pick_rec(q)
        coeffs = [int(x) for x in rec["coeffs"]]  # type: ignore[index]
        poly = _poly_from_coeffs(coeffs)
        Pp = sp.Poly(poly, lam, modulus=p)
        coeff_unit, factors = sp.factor_list(Pp.as_expr(), modulus=p)
        if int(coeff_unit) % p != 1:
            raise RuntimeError(f"Unexpected leading unit in F_{p} factorization for q={q}: {coeff_unit}")

        fexpr = sp.factor(Pp.as_expr(), modulus=p)
        fac_ltx = sp.latex(fexpr)
        lin_spec = _linear_spectrum_from_factors(factors, p)
        a0 = _zero_multiplicity_from_factors(factors, p)
        annih = fac_ltx.replace("\\lambda", "E")

        rows_out.append(
            Row(
                q=int(q),
                order_d=len(coeffs),
                mod5_factor_expr=fac_ltx,
                linear_spectrum=lin_spec,
                zero_mult=a0,
                annihilator_E=annih,
            )
        )
        print(
            f"[charpoly-mod5] q={q:2d} d={len(coeffs):2d} a0={a0} linear={lin_spec}",
            flush=True,
        )

    rows_out = sorted(rows_out, key=lambda r: r.q)

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps({"rows": [asdict(r) for r in rows_out]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"[charpoly-mod5] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    write_table_tex(tout, rows_out)
    print(f"[charpoly-mod5] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

