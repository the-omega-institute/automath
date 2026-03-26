#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit identities for the golden involution Sym^q(G).

We verify (for a finite range of q) the exact matrix identities used in:
  subsubsec__xi-time-protocol-conclusions-part31i.tex

Let phi = (1+sqrt(5))/2 and
  G = [[phi, 1],
       [ 1, -phi]],
so G^2 = (phi+2) I_2. For each q >= 2, let C_q be the matrix of the induced
substitution operator on homogeneous binary polynomials of degree q:
  f(x,y) -> f(phi x + y, x - phi y),
in the monomial basis {x^{q-k} y^k}_{k=0..q}.

We audit:
- C_q^2 = (phi+2)^q I
- C_q^T W_q = W_q C_q, where W_q = diag(1/binom(q,k))
- trace parity law
- determinant closed form, and its Q(sqrt(5))/Q norm collapse to 5^{q(q+1)/2}

Outputs:
- artifacts/export/symq_golden_involution_matrix_audit.json
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


@dataclass(frozen=True)
class CheckRow:
    q: int
    ok_square: bool
    ok_weighted_selfadjoint: bool
    ok_trace: bool
    ok_det: bool
    ok_norm: bool


def _all_zero(M: sp.Matrix) -> bool:
    return all(sp.simplify(x) == 0 for x in list(M))


def _golden_phi() -> sp.Expr:
    return (sp.Integer(1) + sp.sqrt(5)) / 2


def _C_q(q: int, phi: sp.Expr) -> sp.Matrix:
    x, y = sp.symbols("x y")
    C = sp.zeros(q + 1, q + 1)
    for j in range(q + 1):
        expr = sp.expand((phi * x + y) ** (q - j) * (x - phi * y) ** j)
        poly = sp.Poly(expr, x, y, domain=sp.QQ.algebraic_field(sp.sqrt(5)))
        for k in range(q + 1):
            C[k, j] = poly.coeff_monomial(x ** (q - k) * y**k)
    return C


def _W_q(q: int) -> sp.Matrix:
    return sp.diag(*[sp.Rational(1, sp.binomial(q, k)) for k in range(q + 1)])


def _conjugate_in_Qsqrt5(expr: sp.Expr) -> sp.Expr:
    """Field conjugation for QQ(sqrt(5)) via sqrt(5) -> -sqrt(5)."""
    s5 = sp.sqrt(5)
    return sp.simplify(expr.subs({s5: -s5}))


def main() -> None:
    phi = _golden_phi()
    s = sp.simplify(phi + 2)

    max_q = 12
    max_q_det = 10
    rows: List[CheckRow] = []

    for q in range(2, max_q + 1):
        C = _C_q(q, phi)
        W = _W_q(q)

        ok_square = _all_zero(C * C - (s**q) * sp.eye(q + 1))
        ok_weighted_selfadjoint = _all_zero(C.T * W - W * C)

        expected_tr = (s ** (q // 2)) if (q % 2 == 0) else sp.Integer(0)
        ok_trace = sp.simplify(C.trace() - expected_tr) == 0

        if q <= max_q_det:
            detC = sp.simplify(C.det())
            expected_det = sp.Integer((-1) ** (q * (q + 1) // 2)) * (s ** (q * (q + 1) // 2))
            ok_det = sp.simplify(detC - expected_det) == 0
            det_conj = _conjugate_in_Qsqrt5(detC)
            norm = sp.simplify(detC * det_conj)
            expected_norm = sp.Integer(5) ** (q * (q + 1) // 2)
            ok_norm = sp.simplify(norm - expected_norm) == 0
        else:
            ok_det = True
            ok_norm = True

        rows.append(
            CheckRow(
                q=q,
                ok_square=bool(ok_square),
                ok_weighted_selfadjoint=bool(ok_weighted_selfadjoint),
                ok_trace=bool(ok_trace),
                ok_det=bool(ok_det),
                ok_norm=bool(ok_norm),
            )
        )

    out: Dict[str, object] = {
        "phi": str(phi),
        "s": str(s),
        "q_range": [2, max_q],
        "q_det_range": [2, max_q_det],
        "results": [
            {
                "q": r.q,
                "ok_square": r.ok_square,
                "ok_weighted_selfadjoint": r.ok_weighted_selfadjoint,
                "ok_trace": r.ok_trace,
                "ok_det": r.ok_det,
                "ok_norm": r.ok_norm,
            }
            for r in rows
        ],
    }

    p = export_dir() / "symq_golden_involution_matrix_audit.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {p.relative_to(export_dir().parent)}", flush=True)


if __name__ == "__main__":
    main()

