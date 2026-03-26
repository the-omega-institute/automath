#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from math import factorial
from pathlib import Path
from typing import Dict, List, Optional

import sympy as sp
from sympy.polys.numberfields import galois_group


@dataclass(frozen=True)
class Row:
    q: int
    degree: int
    chi_q: str
    irreducible_over_QQ: bool
    galois_group_order: Optional[int]
    is_full_symmetric_by_order: Optional[bool]


def paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def M_q_matrix(q: int) -> sp.Matrix:
    return sp.Matrix(
        [[sp.binomial(q, l) + sp.binomial(q - k, l) for l in range(q + 1)] for k in range(q + 1)]
    )


def poly_is_irreducible_over_QQ(poly: sp.Poly) -> bool:
    fac = sp.factor_list(poly.as_expr(), gens=poly.gens, domain=sp.QQ)
    # factor_list returns (coeff, [(f1, e1), ...]); irreducible iff single factor with exponent 1.
    _, factors = fac
    return len(factors) == 1 and int(factors[0][1]) == 1


def main() -> None:
    x = sp.Symbol("x")
    rows: List[Row] = []

    for q in range(2, 11):
        M = M_q_matrix(q)
        chi_expr = sp.expand(M.charpoly(x).as_expr())
        chi = sp.Poly(chi_expr, x, domain=sp.QQ)

        irreducible = poly_is_irreducible_over_QQ(chi)

        g_order: Optional[int] = None
        is_sym: Optional[bool] = None
        if q <= 5:
            G, _ = galois_group(chi)
            g_order = int(G.order())
            is_sym = g_order == factorial(q + 1)

        rows.append(
            Row(
                q=q,
                degree=q + 1,
                chi_q=str(chi_expr),
                irreducible_over_QQ=bool(irreducible),
                galois_group_order=g_order,
                is_full_symmetric_by_order=is_sym,
            )
        )

    out: Dict[str, object] = {
        "schema_version": 1,
        "rows": [asdict(r) for r in rows],
        "notes": {
            "chi_q_definition": "chi_q(x) = det(x I_{q+1} - M_q), where (M_q)_{k,l} = binom(q,l) + binom(q-k,l).",
            "irreducible_test": "Sympy factorization over QQ: irreducible iff factor_list returns a single factor with exponent 1.",
            "galois_group_test": "For q<=5, compute PermutationGroup via sympy.polys.numberfields.galois_group; full symmetric certified by |G|=(q+1)!.",
        },
    }

    export_path = paper_root() / "artifacts" / "export" / "xi_exceptional_integer_model_Mq_galois_audit.json"
    export_path.parent.mkdir(parents=True, exist_ok=True)
    export_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

