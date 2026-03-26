#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Mod-p factorization fingerprints for audited Fold collision moment characteristic polynomials.

Given audited integer recurrences for S_q(m) in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
we form the characteristic polynomial
  P_q(λ) = λ^d - c_1 λ^{d-1} - ... - c_d,
reduce it modulo a prime p, and factor in F_p[λ].

We also compute three derived, auditable indicators from the factor structure:
  - max irreducible degree among nonzero factors (extension-field scale)
  - whether a repeated nonzero factor exists (non-squarefree → polynomial modulation is possible/typical)
  - a coarse eventual period upper bound:
        Per_p(q) | (p if repeated_nonzero else 1) * lcm_{f != λ}(p^{deg f} - 1)
    (the λ^a_0 factor only affects a finite transient).

Finally, we check the fixed cubic
  χ_{A2}(λ) := λ^3 - 2λ^2 - 2λ + 2
as an “A_2 embedding fingerprint”: whether χ_{A2} divides P_q in F_p[λ].

Outputs:
  - artifacts/export/<name>.json
  - sections/generated/<name>.tex   (a TeX table)

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

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


def _sym_rep(c: int, p: int) -> int:
    """Return symmetric representative in [-(p-1)/2, ..., (p-1)/2]."""
    cc = int(c) % int(p)
    half = (int(p) - 1) // 2
    return cc - int(p) if cc > half else cc


def _poly_to_latex(poly: sp.Poly, p: int) -> str:
    lam = "\\lambda"
    d = int(poly.degree())
    coeffs = [_sym_rep(int(x), p) for x in poly.all_coeffs()]

    parts: List[str] = []
    for i, a in enumerate(coeffs):
        if a == 0:
            continue
        power = d - i
        sign = "-" if a < 0 else "+"
        aa = abs(a)

        if power == 0:
            term = str(aa)
        else:
            if power == 1:
                var = lam
            else:
                var = f"{lam}^{{{power}}}"
            if aa == 1:
                term = var
            else:
                term = f"{aa}{var}"

        if not parts:
            parts.append(term if sign == "+" else f"-{term}")
        else:
            parts.append(f" {sign} {term}")

    return "".join(parts) if parts else "0"


def _is_lambda_factor(f: sp.Expr, p: int) -> bool:
    lam = sp.Symbol("lambda")
    fp = sp.Poly(f, lam, modulus=p)
    coeffs = [int(x) % p for x in fp.all_coeffs()]
    return fp.degree() == 1 and coeffs == [1, 0]


def _lcm(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return abs(a // math.gcd(a, b) * b)


def _lcm_many(xs: Iterable[int]) -> int:
    out = 1
    for x in xs:
        out = _lcm(out, int(x))
    return int(out)


def _factor_product_latex(
    factors: List[Tuple[sp.Expr, int]],
    p: int,
    pull_out_a2: bool,
    a2_poly: sp.Poly,
) -> Tuple[str, bool]:
    """Return (latex_expr, a2_divides) for P_q in F_p[λ].

    If pull_out_a2 and χ_{A2} divides, we factor it out and display it as χ_{A2}(λ).
    """
    lam = sp.Symbol("lambda")

    # Reconstruct P from irreducible factor list (in F_p[λ]) to test divisibility robustly.
    # This avoids relying on exact syntactic factor matching.
    P_expr = sp.Integer(1)
    for f, e in factors:
        P_expr *= sp.expand(f) ** int(e)
    Pp = sp.Poly(P_expr, lam, modulus=p)

    q_div, r_div = Pp.div(a2_poly)
    a2_divides = bool(r_div.as_expr() == 0)

    shown_factors: List[Tuple[str, int]] = []
    if pull_out_a2 and a2_divides:
        shown_factors.append((r"\chi_{A_2}(\lambda)", 1))
        # Factor the quotient irreducibly for display.
        q_expr = q_div.as_expr()
        _, q_factors = sp.factor_list(q_expr, modulus=p)
        for f, e in q_factors:
            fp = sp.Poly(f, lam, modulus=p)
            f_ltx = _poly_to_latex(fp, p)
            if fp.degree() >= 1 and f_ltx != "\\lambda":
                f_ltx = rf"\left({f_ltx}\right)"
            shown_factors.append((f_ltx, int(e)))
    else:
        # Display the irreducible factors directly.
        for f, e in factors:
            fp = sp.Poly(f, lam, modulus=p)
            f_ltx = _poly_to_latex(fp, p)
            if fp.degree() >= 1 and f_ltx != "\\lambda":
                f_ltx = rf"\left({f_ltx}\right)"
            shown_factors.append((f_ltx, int(e)))

    # Multiply with exponent formatting.
    parts: List[str] = []
    for f_ltx, e in shown_factors:
        if e == 1:
            parts.append(f_ltx)
            continue
        if f_ltx == "\\lambda":
            parts.append(rf"\lambda^{{{e}}}")
        else:
            parts.append(rf"{f_ltx}^{{{e}}}")
    expr = " ".join(parts) if parts else "1"
    return expr, a2_divides


@dataclass(frozen=True)
class Row:
    q: int
    order_d: int
    factor_expr: str
    max_irred_deg_nonzero: int
    repeated_nonzero: int
    embeds_A2: int
    period_bound: int


def _pick_rec(q: int) -> Dict[str, object]:
    for rec in PRECOMPUTED_RECS_9_17:
        if int(rec["k"]) == int(q):
            return rec
    raise KeyError(f"Missing precomputed recurrence for q={q}")


def write_table_tex(path: Path, p: int, rows: List[Row], label: str, caption: str) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(f"\\caption{{{caption}}}")
    lines.append(f"\\label{{{label}}}")
    lines.append("\\begin{tabular}{r r l r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$q$ & order $d_q$ & factorization in $\\mathbb{F}_{%d}[\\lambda]$ & max deg & repeat? & $\\chi_{A_2}\\mid P_q$ & period bound\\\\"
        % int(p)
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.order_d} & ${r.factor_expr}$ & {r.max_irred_deg_nonzero} & "
            f"{r.repeated_nonzero} & {r.embeds_A2} & {r.period_bound}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Factor audited P_q(λ) modulo a prime p.")
    ap.add_argument("--p", type=int, required=True, help="Prime modulus p.")
    ap.add_argument("--q-list", type=str, required=True, help="Comma-separated q list.")
    ap.add_argument("--pull-out-a2", action="store_true", help="Display χ_{A2}(λ) as a grouped factor when it divides.")
    ap.add_argument("--json-out", type=str, default="", help="Output JSON path (default: export/<name>.json).")
    ap.add_argument("--tex-out", type=str, default="", help="Output TeX path (default: generated/<name>.tex).")
    ap.add_argument("--name", type=str, default="", help="Base name for outputs (without extension).")
    ap.add_argument("--caption", type=str, default="", help="TeX table caption (English).")
    args = ap.parse_args()

    p = int(args.p)
    if p <= 1:
        raise SystemExit("p must be > 1")

    q_list = [int(x.strip()) for x in str(args.q_list).split(",") if x.strip()]
    if not q_list:
        raise SystemExit("Empty --q-list")

    name = str(args.name).strip()
    if not name:
        q_tag = f"q{min(q_list)}_{max(q_list)}" if len(q_list) > 1 else f"q{q_list[0]}"
        name = f"fold_collision_charpoly_mod{p}_factorization_{q_tag}"

    json_out = Path(args.json_out) if str(args.json_out).strip() else (export_dir() / f"{name}.json")
    tex_out = Path(args.tex_out) if str(args.tex_out).strip() else (generated_dir() / f"tab_{name}.tex")

    # Default label follows the repository convention: tab:<stem without leading tab_>.
    stem = tex_out.stem
    base_for_label = stem[4:] if stem.startswith("tab_") else stem
    label = f"tab:{base_for_label}"

    caption = str(args.caption).strip()
    if not caption:
        caption = (
            f"Mod-{p} factorization fingerprints of the audited Fold collision moment characteristic polynomials "
            f"$P_q(\\lambda)$ (for the listed $q$). We report max irreducible degree, a non-squarefree flag "
            f"(repeated nonzero factors), an $A_2$ embedding flag $\\chi_{{A_2}}\\mid P_q$, and a coarse "
            f"eventual period upper bound derived from factor degrees."
        )

    lam = sp.Symbol("lambda")
    chiA2_expr = lam**3 - 2 * lam**2 - 2 * lam + 2
    chiA2_poly = sp.Poly(chiA2_expr, lam, modulus=p)

    rows_out: List[Row] = []
    for q in q_list:
        rec = _pick_rec(q)
        coeffs = [int(x) for x in rec["coeffs"]]  # type: ignore[index]
        P = _poly_from_coeffs(coeffs)
        Pp = sp.Poly(P, lam, modulus=p)
        unit, factors = sp.factor_list(Pp.as_expr(), modulus=p)
        if int(unit) % p != 1:
            raise RuntimeError(f"Unexpected leading unit in F_{p} factorization for q={q}: {unit}")

        # Irreducible degrees and repetition flags (exclude λ = zero-eigenvalue factor).
        degs_nonzero: List[int] = []
        repeated_nonzero = 0
        for f, e in factors:
            fp = sp.Poly(f, lam, modulus=p)
            if _is_lambda_factor(fp.as_expr(), p):
                continue
            degs_nonzero.append(int(fp.degree()))
            if int(e) >= 2:
                repeated_nonzero = 1

        if not degs_nonzero:
            # Degenerate: only λ^a_0. Eventual period is 1.
            max_deg = 0
            base_lcm = 1
        else:
            max_deg = int(max(degs_nonzero))
            base_lcm = _lcm_many([p**d - 1 for d in sorted(set(degs_nonzero))])

        period_bound = int((p if repeated_nonzero else 1) * base_lcm)

        factor_expr, a2_divides = _factor_product_latex(
            factors=factors,
            p=p,
            pull_out_a2=bool(args.pull_out_a2),
            a2_poly=chiA2_poly,
        )

        rows_out.append(
            Row(
                q=int(q),
                order_d=len(coeffs),
                factor_expr=factor_expr,
                max_irred_deg_nonzero=int(max_deg),
                repeated_nonzero=int(repeated_nonzero),
                embeds_A2=int(1 if a2_divides else 0),
                period_bound=int(period_bound),
            )
        )
        print(
            f"[charpoly-mod{p}] q={q:2d} d={len(coeffs):2d} maxdeg={max_deg} repeat={repeated_nonzero} "
            f"A2={1 if a2_divides else 0} Per|{period_bound}",
            flush=True,
        )

    rows_out = sorted(rows_out, key=lambda r: r.q)

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(
        json.dumps({"p": p, "q_list": q_list, "rows": [asdict(r) for r in rows_out]}, indent=2, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    print(f"[charpoly-mod{p}] wrote {json_out}", flush=True)

    write_table_tex(tex_out, p=p, rows=rows_out, label=label, caption=caption)
    print(f"[charpoly-mod{p}] wrote {tex_out}", flush=True)


if __name__ == "__main__":
    main()

