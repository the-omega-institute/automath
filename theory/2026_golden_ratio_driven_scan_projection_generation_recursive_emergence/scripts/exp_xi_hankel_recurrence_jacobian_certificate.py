#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: Jacobian and Toeplitz–Hankel factorization for recurrence parametrization.

This script certifies, for small d, the identities used in:
  - thm:xi-hankel-recurrence-jacobian-identity
  - prop:xi-hankel-jacobian-toeplitz-hankel-factorization

Outputs:
  - artifacts/export/xi_hankel_recurrence_jacobian_certificate.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _series_inverse_coeffs_Q(
    coeffs_t1_to_td: Sequence[sp.Expr], max_m: int
) -> List[sp.Expr]:
    """Given Q(t)=1+q1 t+...+qd t^d, return s0..s_max where 1/Q=Σ s_m t^m."""
    q = [sp.Integer(0)] + list(coeffs_t1_to_td)
    d = len(coeffs_t1_to_td)
    s: List[sp.Expr] = [sp.Integer(0)] * (max_m + 1)
    s[0] = sp.Integer(1)
    for m in range(1, max_m + 1):
        acc = sp.Integer(0)
        for r in range(1, min(d, m) + 1):
            acc += q[r] * s[m - r]
        s[m] = sp.expand(-acc)
    return s


def _build_sequence(
    d: int,
    c: Sequence[sp.Symbol],
    a_init: Sequence[sp.Integer],
    n_max: int,
) -> List[sp.Expr]:
    """Recurrence a_{n+d} + Σ_{j=0}^{d-1} c_j a_{n+j} = 0."""
    a: List[sp.Expr] = [sp.Integer(0)] * (n_max + 1)
    for i in range(d):
        a[i] = sp.Integer(a_init[i])
    for n in range(0, n_max + 1 - d):
        a[n + d] = sp.expand(-sum(c[j] * a[n + j] for j in range(d)))
    return a


def _hankel_block(a: Sequence[sp.Expr], d: int) -> sp.Matrix:
    return sp.Matrix([[a[i + j] for j in range(d)] for i in range(d)])


def _toeplitz_lower(s: Sequence[sp.Expr], d: int) -> sp.Matrix:
    return sp.Matrix([[s[n - i] if i <= n else 0 for i in range(d)] for n in range(d)])


@dataclass(frozen=True)
class Row:
    d: int
    det_identity_holds: bool
    factorization_holds: bool
    detH: str
    detJ: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Jacobian determinant and Toeplitz–Hankel factorization for recurrence parametrization.")
    parser.add_argument(
        "--max-d",
        type=int,
        default=5,
        help="Maximum d to certify symbolically (default: 5).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_hankel_recurrence_jacobian_certificate.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    rows: List[Row] = []
    for d in range(1, args.max_d + 1):
        c = sp.symbols(f"c0:{d}", commutative=True)
        # Deterministic initial values (small, nondegenerate).
        a_init = [sp.Integer(i + 2) for i in range(d)]
        a = _build_sequence(d, c, a_init, n_max=2 * d - 1)
        Phi = sp.Matrix([a[d + i] for i in range(d)])

        # Jacobian J_{i,j} = ∂ a_{d+i} / ∂ c_j.
        J = Phi.jacobian(list(c))

        # Hankel block H_{i,j} = a_{i+j}.
        H = _hankel_block(a, d)

        detJ = sp.factor(J.det())
        detH = sp.factor(H.det())
        det_identity = sp.simplify(detJ - ((-1) ** d) * detH) == 0

        # Toeplitz factor from 1/Q(t), where Q(t)=1+c_{d-1} t + ... + c0 t^d.
        q_t1_to_td: List[sp.Expr] = []
        for r in range(1, d + 1):
            q_t1_to_td.append(c[d - r])
        s = _series_inverse_coeffs_Q(q_t1_to_td, max_m=d - 1)
        T = _toeplitz_lower(s, d)
        fact_identity = sp.simplify(J + T * H) == sp.zeros(d, d)

        rows.append(
            Row(
                d=d,
                det_identity_holds=bool(det_identity),
                factorization_holds=bool(fact_identity),
                detH=str(detH),
                detJ=str(detJ),
            )
        )

    payload: Dict[str, object] = {
        "max_d": args.max_d,
        "rows": [asdict(r) for r in rows],
        "all_det_identities_hold": all(r.det_identity_holds for r in rows),
        "all_factorizations_hold": all(r.factorization_holds for r in rows),
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-hankel-recurrence-jacobian] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

