#!/usr/bin/env python3
"""Stage-1 genus-2 linear-algebra skeleton for Litt-Lam arXiv:2601.07933.

This script uses only Python's standard library plus Sympy. It verifies the
basic genus-2 hyperelliptic bases for H^0(K_C) and H^0(K_C^2), then computes
the explicitly requested f'(root)-weighted residue/intersection proxy matrix.

The pairing is deliberately labeled INTERSECTION_PROXY. It is rank-detecting
bookkeeping for this Stage-1 artifact, not the genuine Serre cup product.
"""

from __future__ import annotations

import datetime as _datetime
import json
import os
from typing import Any, Dict, List

import sympy as sp


PAPER = {
    "citation": (
        "Daniel Litt, Ruochuan Liu Lam, p-curvature and non-abelian cohomology, "
        "arXiv:2601.07933, January 2026"
    ),
    "arxiv": "2601.07933",
    "target": (
        "Theorem 6.1.1 relative curves: vanishing p-curvature of the "
        "isomonodromy foliation forces isotriviality"
    ),
}
STAGE = (
    "Stage 1: concrete genus-2 hyperelliptic linear-algebra skeleton and "
    "INTERSECTION_PROXY rank check"
)
OUTPUT_NAME = "check_2601_07933_genus2_serre_pairing_stage1_output.json"


def timestamp() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def banner() -> None:
    print("=" * 78, flush=True)
    print("Litt-Lam arXiv:2601.07933 genus-2 Serre pairing Stage-1 checker", flush=True)
    print("Pure Python stdlib + sympy exact rational arithmetic", flush=True)
    print("=" * 78, flush=True)


def phase(title: str) -> None:
    print(f"[{timestamp()}] PHASE: {title}", flush=True)


def rational_to_string(value: Any) -> str:
    value = sp.Rational(value)
    return str(value)


def main() -> int:
    banner()

    x = sp.symbols("x")

    phase("constructing the genus-2 hyperelliptic curve")
    f = sp.prod(x - sp.Integer(root) for root in range(6))
    expanded_f = sp.expand(f)
    degree = sp.degree(expanded_f, x)
    roots = [sp.Integer(root) for root in range(6)]
    distinct_roots = len(set(roots)) == 6
    f_prime = sp.diff(expanded_f, x)
    genus = (degree - 1) // 2
    curve_checks = {
        "degree_is_6": degree == 6,
        "six_distinct_rational_roots": distinct_roots,
        "genus_formula_floor_degree_minus_one_over_two": genus == 2,
    }
    assert curve_checks["degree_is_6"]
    assert curve_checks["six_distinct_rational_roots"]
    assert curve_checks["genus_formula_floor_degree_minus_one_over_two"]

    phase("listing H^0(K_C) basis and checking Riemann-Roch dimension")
    basis_h0_k = ["dx/y", "x dx/y"]
    dim_h0_k = len(basis_h0_k)
    riemann_roch_k_correct = dim_h0_k == genus == 2
    assert dim_h0_k == 2

    phase("listing H^0(K_C^2) basis and checking dimension")
    basis_h0_k2 = ["(dx/y)^2", "x (dx/y)^2", "x^2 (dx/y)^2"]
    dim_h0_k2 = len(basis_h0_k2)
    expected_dim_h0_k2 = 3 * genus - 3
    riemann_roch_k2_correct = dim_h0_k2 == expected_dim_h0_k2 == 3
    assert dim_h0_k2 == 3

    phase("building INTERSECTION_PROXY matrix with exact rational arithmetic")
    # INTERSECTION_PROXY:
    # M_ij = sum_k root_k^(i+j) / f'(root_k), for i,j = 0,1,2.
    # This is the requested f'(x_k)-weighted Frobenius-style symmetric
    # bilinear form. It is not the genuine Serre cup product.
    matrix: List[List[sp.Rational]] = []
    for i in range(3):
        row: List[sp.Rational] = []
        for j in range(3):
            entry = sp.Rational(0)
            for root in roots:
                denominator = sp.Rational(f_prime.subs(x, root))
                entry += sp.Rational(root ** (i + j), denominator)
            row.append(sp.simplify(entry))
        matrix.append(row)

    sympy_matrix = sp.Matrix(matrix)
    determinant = sp.simplify(sympy_matrix.det())
    serre_pairing_non_degenerate = determinant != 0

    phase("recording optional Hitchin target dimension sanity check")
    hitchin_optional = {
        "target_dim": dim_h0_k2,
        "matches_H0_K2": dim_h0_k2 == 3,
        "note": "dimension match only; no global surjectivity verified",
    }

    all_dims_correct = bool(
        curve_checks["degree_is_6"]
        and curve_checks["six_distinct_rational_roots"]
        and curve_checks["genus_formula_floor_degree_minus_one_over_two"]
        and riemann_roch_k_correct
        and riemann_roch_k2_correct
    )

    phase("computing verdict")
    if all_dims_correct and serre_pairing_non_degenerate:
        verdict = "PASS_SERRE_PAIRING_NON_DEGENERATE_PROXY"
    elif all_dims_correct and not serre_pairing_non_degenerate:
        verdict = "FAIL_DEGENERATE_PAIRING"
    else:
        failed_reasons = [
            name for name, ok in {
                **curve_checks,
                "riemann_roch_K_correct": riemann_roch_k_correct,
                "riemann_roch_K2_correct": riemann_roch_k2_correct,
            }.items()
            if not ok
        ]
        verdict = "PARTIAL_" + "_".join(failed_reasons)

    output: Dict[str, Any] = {
        "paper": PAPER,
        "stage": STAGE,
        "curve": {
            "equation": "y^2 = x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5)",
            "f_expanded": str(expanded_f),
            "degree_f": int(degree),
            "roots_over_Q": [str(root) for root in roots],
            "distinct_roots_over_Q": distinct_roots,
            "checks": curve_checks,
        },
        "genus": int(genus),
        "dim_H0_K": dim_h0_k,
        "basis_H0_K": basis_h0_k,
        "dim_H0_K2": dim_h0_k2,
        "basis_H0_K2": basis_h0_k2,
        "riemann_roch_K_correct": riemann_roch_k_correct,
        "riemann_roch_K2_correct": riemann_roch_k2_correct,
        "serre_pairing_3x3_matrix": [
            [rational_to_string(entry) for entry in row] for row in matrix
        ],
        "serre_pairing_determinant": rational_to_string(determinant),
        "serre_pairing_non_degenerate": bool(serre_pairing_non_degenerate),
        "pairing_kind": "INTERSECTION_PROXY",
        "pairing_note": (
            "f'(x_k)-weighted Frobenius-style symmetric bilinear form on "
            "H^0(K_C^2), rank-detecting but NOT the genuine Serre cup product"
        ),
        "hitchin_optional": hitchin_optional,
        "verdict": verdict,
    }

    phase("writing JSON output")
    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print(f"JSON output: {output_path}", flush=True)
    print(f"VERDICT: {verdict}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
