#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificate: irreducibility and (small-degree) Galois groups for the
replica-softcore exceptional characteristic polynomial chi_exc^(q).

This script is English-only by repository convention.

Definitions (paper notation):
  - The exceptional block A^(q) is the restriction of T^(q) to the S_q-symmetric
    subspace, of dimension q+1.
  - We work with the integer-scaled matrix A2^(q) := 2 A^(q), whose entries are
    (see exp_replica_softcore_binary_necklace_trace_audit.py):
        A2^(q)[k,l] = binom(q,l) + binom(q-k,l)  (with binom(q-k,l)=0 if l>q-k).
  - Let P_q(x) := det(x I - A2^(q)) in Z[x]. The exceptional characteristic
    polynomial satisfies
        chi_exc^(q)(x) = 2^{-(q+1)} P_q(2x),
    hence irreducibility over Q and the Galois group are identical for P_q and
    chi_exc^(q) (up to the rational scaling of roots).

We certify:
  - irreducibility of P_q over Q for 2 <= q <= 10;
  - Gal(P_q/Q) = S_{q+1} for 2 <= q <= 5 (degree <= 6, within SymPy support).

Outputs:
  - artifacts/export/replica_softcore_exceptional_charpoly_galois_audit.json
  - sections/generated/tab_replica_softcore_exceptional_charpoly_galois_audit.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp
from sympy.polys.numberfields.galoisgroups import galois_group

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_A2(q: int) -> sp.Matrix:
    """A2^(q) = 2 A^(q) on the S_q-symmetric subspace (size q+1)."""
    if q < 0:
        raise ValueError("q must be >= 0")
    M = [[0] * (q + 1) for _ in range(q + 1)]
    for k in range(q + 1):
        for l in range(q + 1):
            term = math.comb(q - k, l) if 0 <= l <= q - k else 0
            M[k][l] = math.comb(q, l) + term
    return sp.Matrix(M)


def charpoly_Z(A: sp.Matrix, x: sp.Symbol) -> sp.Poly:
    """Return the monic characteristic polynomial in Z[x]."""
    expr = sp.expand(A.charpoly(x).as_expr())
    return sp.Poly(expr, x, domain="ZZ")


def factor_degrees(poly: sp.Poly) -> List[int]:
    """Return degrees (with multiplicity) of irreducible factors over Z (hence over Q)."""
    _c, facs = sp.factor_list(poly)
    degs: List[int] = []
    for f, e in facs:
        degs.extend([int(f.degree())] * int(e))
    return sorted(degs, reverse=True)


def is_irreducible_over_Q(poly: sp.Poly) -> bool:
    """Irreducible over Q iff irreducible over Z for primitive polynomials (Gauss)."""
    degs = factor_degrees(poly)
    return len(degs) == 1 and degs[0] == int(poly.degree())


@dataclass(frozen=True)
class Row:
    q: int
    degree: int
    poly_Zx: str
    irreducible_Qx: bool
    factor_degrees_Qx: List[int]
    gal_order: Optional[int]
    gal_is_symmetric: Optional[bool]
    gal_label: Optional[str]
    gal_error: Optional[str]


def _gal_label_from_order(deg: int, order: int) -> str:
    if order == math.factorial(deg):
        return f"S_{deg}"
    if deg >= 2 and order == math.factorial(deg) // 2:
        return f"A_{deg}"
    return f"|G|={order}"


def main() -> None:
    t0 = time.time()
    print("[replica-softcore-exc-charpoly-galois] start", flush=True)

    x = sp.Symbol("x")
    q_min = 2
    q_max_irred = 10
    q_max_gal = 5

    rows: List[Row] = []
    for q in range(q_min, q_max_irred + 1):
        A2 = build_A2(q)
        P = charpoly_Z(A2, x)
        deg = int(P.degree())

        degs = factor_degrees(P)
        irred = is_irreducible_over_Q(P)

        gal_order: Optional[int] = None
        gal_is_sym: Optional[bool] = None
        gal_label: Optional[str] = None
        gal_error: Optional[str] = None
        if q <= q_max_gal:
            try:
                G, _is_real = galois_group(P)
                gal_order = int(G.order())
                gal_is_sym = bool(gal_order == math.factorial(deg))
                gal_label = _gal_label_from_order(deg, gal_order)
            except Exception as e:  # pragma: no cover
                gal_error = f"{type(e).__name__}: {e}"

        rows.append(
            Row(
                q=int(q),
                degree=int(deg),
                poly_Zx=sp.sstr(P.as_expr()),
                irreducible_Qx=bool(irred),
                factor_degrees_Qx=degs,
                gal_order=gal_order,
                gal_is_symmetric=gal_is_sym,
                gal_label=gal_label,
                gal_error=gal_error,
            )
        )

    payload: Dict[str, object] = {
        "q_min": q_min,
        "q_max_irreducible": q_max_irred,
        "q_max_galois": q_max_gal,
        "rows": [asdict(r) for r in rows],
        "notes": {
            "poly": "P_q(x)=det(x I - A2^(q)) in Z[x], with A2^(q)=2A^(q)",
            "equivalence": "Irreducibility/Galois group match chi_exc^(q) since chi_exc^(q)(x)=2^{-(q+1)}P_q(2x)",
            "sympy": sp.__version__,
        },
    }

    out_json = export_dir() / "replica_softcore_exceptional_charpoly_galois_audit.json"
    _write_json(out_json, payload)

    # TeX table snippet.
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_replica_softcore_exceptional_charpoly_galois_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{8pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.12}")
    lines.append("\\begin{tabular}{rrrr}")
    lines.append("\\toprule")
    lines.append("$q$ & $\\deg\\chi_{\\mathrm{exc}}^{(q)}$ & irreducible over $\\QQ$ & $\\mathrm{Gal}$ (SymPy, $q\\le 5$) \\\\")
    lines.append("\\midrule")
    for r in rows:
        irred_tex = "yes" if r.irreducible_Qx else "no"
        gal_tex = f"${r.gal_label}$" if (r.gal_label is not None) else "--"
        lines.append(f"{r.q} & {r.degree} & {irred_tex} & {gal_tex} \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{Computational audit for the exceptional characteristic polynomial "
        "$\\chi_{\\mathrm{exc}}^{(q)}$: irreducibility for $2\\le q\\le 10$ and "
        "Galois group for $2\\le q\\le 5$ (degree $\\le 6$, within SymPy support).}"
    )
    lines.append("\\label{tab:replica_softcore_exceptional_charpoly_galois_audit}")
    lines.append("\\end{table}")
    lines.append("")

    out_tex = generated_dir() / "tab_replica_softcore_exceptional_charpoly_galois_audit.tex"
    _write_text(out_tex, "\n".join(lines))

    dt = time.time() - t0
    print(f"File: {out_json.relative_to(out_json.parents[2])}", flush=True)
    print(f"File: {out_tex.relative_to(out_tex.parents[2])}", flush=True)
    print(f"[replica-softcore-exc-charpoly-galois] done elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

