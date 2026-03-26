#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Operator-algebra / flow-equivalence invariants for low-order Fold collision kernels A2, A3, A4(t).

We compute (for the explicit nonnegative integer kernels in the manuscript):
  - det(I-A) and Smith normal form (SNF) of I-A and I-A^T
  - Bowen--Franks group BF(A) = Z^n / (I-A) Z^n
  - K0/K1 of the Cuntz--Krieger algebra O_A via coker/ker(I-A^T)
  - order of the unit class [1] in K0 (via an adjugate certificate)
  - discriminant formula of p_t(x)=det(xI-A4(t)) and its sign for t>=0
  - mod-p factorization fingerprints and discriminant value for p_7(x)

Outputs:
  - artifacts/export/collision_kernel_A234_operator_algebra_flow_invariants.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _A2() -> sp.Matrix:
    return sp.Matrix(
        [
            [0, 0, 1],
            [0, 1, 1],
            [2, 1, 1],
        ]
    )


def _A3() -> sp.Matrix:
    return sp.Matrix(
        [
            [0, 2, 2],
            [1, 0, 2],
            [0, 1, 2],
        ]
    )


def _A4(t: int) -> sp.Matrix:
    if int(t) != t:
        raise ValueError("t must be an integer")
    if t < 0:
        raise ValueError("t must be >= 0 for a nonnegative adjacency matrix")
    return sp.Matrix(
        [
            [0, 1, 0, 0, 0],
            [0, 0, int(t), 0, 1],
            [0, 1, 2, 0, 0],
            [1, 0, 1, 0, 0],
            [0, 0, 0, 1, 0],
        ]
    )


def _smith_diag(M: sp.Matrix) -> List[int]:
    from sympy.matrices.normalforms import smith_normal_form

    S = smith_normal_form(M, domain=sp.ZZ)
    diag = [abs(int(S[i, i])) for i in range(int(S.rows))]
    return diag


def _bf_from_snf(diag: Sequence[int]) -> Dict[str, object]:
    free_rank = sum(1 for d in diag if d == 0)
    torsion = [int(d) for d in diag if d not in (0, 1)]
    return {"free_rank": free_rank, "torsion": torsion}


def _is_primitive(A: sp.Matrix, *, max_k: int = 200) -> Tuple[bool, int]:
    """Return (is_primitive, smallest_k_with_all_positive_or_-1_if_none).

    For a nonnegative integer matrix, primitivity means A^k has all entries > 0 for some k.
    """
    if any(int(x) < 0 for x in list(A)):
        raise ValueError("A must be entrywise nonnegative")
    n = int(A.rows)
    P = A.copy()
    for k in range(1, max_k + 1):
        if all(int(P[i, j]) > 0 for i in range(n) for j in range(n)):
            return True, k
        P = P * A
    return False, -1


def _factor_degrees_mod_p(poly_expr: sp.Expr, x: sp.Symbol, p: int) -> List[int]:
    P = sp.Poly(poly_expr, x, modulus=int(p))
    _c, facs = P.factor_list()
    degs: List[int] = []
    for f, e in facs:
        degs.extend([int(f.degree())] * int(e))
    degs.sort(reverse=True)
    return degs


def _discriminant_A4_family() -> Dict[str, object]:
    x = sp.Symbol("x")
    t = sp.Symbol("t")
    p_t = x**5 - 2 * x**4 - t * x**3 - 2 * x + 2
    disc = sp.discriminant(p_t, x)
    expected = -16 * (27 * t**5 + 35 * t**4 + 434 * t**3 + 4394 * t**2 + 10832 * t + 7403)
    ok = sp.expand(disc - expected) == 0
    if not ok:
        raise RuntimeError("Discriminant formula mismatch for p_t(x).")
    disc = sp.expand(expected)
    inside = sp.expand(-disc / 16)
    poly_inside = sp.Poly(inside, t, domain=sp.ZZ)
    coeffs = [int(poly_inside.coeff_monomial(t**k)) for k in range(0, 6)]
    # coeffs are for the positive polynomial inside the parentheses, in increasing degree (t^0..t^5).
    return {
        "disc_formula": str(disc),
        "disc_factor": "-16",
        "inside_poly_coeffs_t0_to_t5": coeffs,
        "disc_negative_for_t_ge_0_reason": "inside polynomial has strictly positive coefficients",
    }


def _adjugate_unit_certificate_A4() -> Dict[str, object]:
    t = sp.Symbol("t", integer=True, nonnegative=True)
    A = sp.Matrix(
        [
            [0, 1, 0, 0, 0],
            [0, 0, t, 0, 1],
            [0, 1, 2, 0, 0],
            [1, 0, 1, 0, 0],
            [0, 0, 0, 1, 0],
        ]
    )
    M = sp.eye(5) - A.T
    v = sp.Matrix([1, 1, 1, 1, 1])
    adjMv = sp.simplify(M.adjugate() * v)
    entries = [sp.expand(adjMv[i, 0]) for i in range(5)]
    # We record the symbolic entries as strings.
    return {"adjM_times_ones_vector": [str(e) for e in entries]}


@dataclass(frozen=True)
class MatrixInvariants:
    n: int
    det_I_minus_A: int
    snf_I_minus_A: List[int]
    snf_I_minus_AT: List[int]
    bf: Dict[str, object]
    primitive: bool
    primitive_k: int


def _matrix_invariants(A: sp.Matrix) -> MatrixInvariants:
    n = int(A.rows)
    I = sp.eye(n)
    det = int((I - A).det())
    snf = _smith_diag(I - A)
    snfT = _smith_diag(I - A.T)
    bf = _bf_from_snf(snf)
    prim, k = _is_primitive(A, max_k=200)
    return MatrixInvariants(n=n, det_I_minus_A=det, snf_I_minus_A=snf, snf_I_minus_AT=snfT, bf=bf, primitive=prim, primitive_k=k)


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute BF/K-theory/flow-equivalence related invariants for A2,A3,A4(t).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A234_operator_algebra_flow_invariants.json"),
    )
    parser.add_argument("--t-check", type=str, default="0,1,2,3,4,5,6,7,8,9,10", help="comma-separated t values to verify A4(t) SNF pattern")
    args = parser.parse_args()

    A2 = _A2()
    A3 = _A3()
    inv_A2 = _matrix_invariants(A2)
    inv_A3 = _matrix_invariants(A3)

    # Verify the explicit unit-class certificate for A3: (I-A3^T)x = 1-vector.
    xA3 = sp.Matrix([1, 0, -3])
    unit_vec_3 = sp.Matrix([1, 1, 1])
    cert_A3_unit_zero = (sp.eye(3) - A3.T) * xA3 == unit_vec_3

    # A4(t) checks across several t values (integer).
    t_vals = [int(s.strip()) for s in str(args.t_check).split(",") if s.strip() != ""]
    A4_checks = []
    for tv in t_vals:
        A4t = _A4(tv)
        inv = _matrix_invariants(A4t)
        expected_det = -(tv + 1)
        expected_snf = [1, 1, 1, 1, tv + 1]
        A4_checks.append(
            {
                "t": tv,
                "det_I_minus_A": inv.det_I_minus_A,
                "snf_I_minus_A": inv.snf_I_minus_A,
                "snf_I_minus_AT": inv.snf_I_minus_AT,
                "primitive": inv.primitive,
                "primitive_k": inv.primitive_k,
                "matches_expected_det": inv.det_I_minus_A == expected_det,
                "matches_expected_snf": inv.snf_I_minus_A == expected_snf,
                "matches_expected_snf_T": inv.snf_I_minus_AT == expected_snf,
            }
        )
        if inv.det_I_minus_A != expected_det or inv.snf_I_minus_A != expected_snf:
            raise RuntimeError(f"Unexpected invariant for A4(t) at t={tv}: det={inv.det_I_minus_A}, snf={inv.snf_I_minus_A}")

    disc_info = _discriminant_A4_family()
    adj_unit_cert = _adjugate_unit_certificate_A4()

    # p7(x) fingerprints (t=7).
    x = sp.Symbol("x")
    p7 = x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2
    disc_p7 = int(sp.discriminant(p7, x))
    disc_expected = -16 * 985219
    if disc_p7 != disc_expected:
        raise RuntimeError(f"Unexpected Disc(p7): got {disc_p7}, expected {disc_expected}")
    mod5_degs = _factor_degrees_mod_p(p7, x, 5)
    mod29_degs = _factor_degrees_mod_p(p7, x, 29)

    payload: Dict[str, object] = {
        "A2": asdict(inv_A2),
        "A3": asdict(inv_A3),
        "A3_unit_class_zero_certificate": {
            "x": [int(v) for v in list(xA3)],
            "ok": bool(cert_A3_unit_zero),
        },
        "A4_family_checks": A4_checks,
        "A4_adjugate_unit_certificate": adj_unit_cert,
        "A4_discriminant": disc_info,
        "p7": {
            "disc": disc_p7,
            "disc_factorization": "-16 * 985219",
            "mod5_factor_degrees": mod5_degs,
            "mod29_factor_degrees": mod29_degs,
        },
    }

    out_path = Path(args.json_out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Minimal stdout summary (English-only).
    print(f"[ok] wrote {out_path}")
    print(f"[A2] det(I-A2)={inv_A2.det_I_minus_A} snf={inv_A2.snf_I_minus_A}")
    print(f"[A3] det(I-A3)={inv_A3.det_I_minus_A} snf={inv_A3.snf_I_minus_A} unit_zero={bool(cert_A3_unit_zero)}")
    print(f"[A4] checked t values: {t_vals}")
    print(f"[p7] Disc={disc_p7} mod5_degs={mod5_degs} mod29_degs={mod29_degs}")


if __name__ == "__main__":
    main()

