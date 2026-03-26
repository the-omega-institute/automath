#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: closed-form formulas for the exceptional integer model matrix M_q.

This script is English-only by repository convention.

We verify, for a finite range of q>=2, the identities stated in:
  sections/body/zeta_finite_part/xi/subsubsec__xi-time-protocol-conclusions-part31d.tex

Checks:
- M_q inverse entrywise closed form
- rank-one decompositions (Pascal/reversal/diagonal sign matrices)
- determinant formula det(M_q)=2*(-1)^{q(q+1)/2}
- Smith normal form SNF(M_q)=diag(1,...,1,2)
- Diophantine solvability obstruction depends only on b_0 mod 2
- 2*M_q^{-1} is integer and has a unique odd entry at (0,0)

Output:
- artifacts/export/xi_exceptional_integer_model_Mq_audit.json
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

from common_paths import export_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    details: str = ""


def _pascal(q: int) -> sp.Matrix:
    return sp.Matrix([[sp.binomial(k, ell) for ell in range(q + 1)] for k in range(q + 1)])


def _reversal(q: int) -> sp.Matrix:
    return sp.Matrix([[1 if k + ell == q else 0 for ell in range(q + 1)] for k in range(q + 1)])


def _diag_sign(q: int) -> sp.Matrix:
    return sp.diag(*[(-1) ** k for k in range(q + 1)])


def _Mq(q: int) -> sp.Matrix:
    return sp.Matrix([[sp.binomial(q, ell) + sp.binomial(q - k, ell) for ell in range(q + 1)] for k in range(q + 1)])


def _Mq_inv_closed_form(q: int) -> sp.Matrix:
    N = sp.zeros(q + 1, q + 1)
    for k in range(q + 1):
        for ell in range(q + 1):
            if k == 0 and ell == 0:
                N[k, ell] = sp.Rational(-1, 2)
            elif k + ell < q:
                N[k, ell] = sp.Integer(0)
            else:
                r = k + ell - q
                N[k, ell] = (-1) ** (k + ell - q) * sp.binomial(k, r)
    return N


def main() -> None:
    t0 = time.time()

    q_min = 2
    q_max = 25
    q_snf_max = 16  # SNF is heavier; keep deterministic runtime bounded.

    checks: List[Check] = []
    per_q: Dict[str, Dict[str, object]] = {}

    for q in range(q_min, q_max + 1):
        M = _Mq(q)
        N = _Mq_inv_closed_form(q)

        # 1) Inverse closed form.
        I = sp.eye(q + 1)
        ok_left = (M * N) == I
        ok_right = (N * M) == I

        # 2) Decomposition checks.
        P = _pascal(q)
        R = _reversal(q)
        D = _diag_sign(q)
        E00 = sp.zeros(q + 1, q + 1)
        E00[0, 0] = 1
        b = sp.Matrix([sp.binomial(q, ell) for ell in range(q + 1)])
        ones = sp.Matrix([1 for _ in range(q + 1)])

        A = (-1) ** q * D * P * R * D
        B = (-1) ** q * D * R * P.inv() * D  # integer
        ok_decomp_inv = (N == (A - sp.Rational(1, 2) * E00))
        ok_decomp_fwd = (M == (B + ones * b.T))

        # 3) Determinant formula.
        det_M = sp.factor(M.det())
        det_expected = sp.Integer(2) * (-1) ** (q * (q + 1) // 2)
        ok_det = sp.simplify(det_M - det_expected) == 0

        # 4) 2*N integrality and unique odd entry.
        twoN = sp.Matrix([[sp.simplify(2 * N[i, j]) for j in range(q + 1)] for i in range(q + 1)])
        ok_twoN_int = all(v.is_Integer for v in list(twoN))
        odd_positions = [(i, j) for i in range(q + 1) for j in range(q + 1) if int(twoN[i, j]) % 2 != 0]
        ok_unique_odd = (odd_positions == [(0, 0)]) and (twoN[0, 0] in {sp.Integer(-1), sp.Integer(1)})

        # 5) Diophantine parity obstruction (spot check on random b).
        # Use a deterministic set of test vectors (no RNG).
        test_bs: List[sp.Matrix] = []
        for t in range(6):
            v = sp.Matrix([(q + 7) * (t + 1) + 3 * i for i in range(q + 1)])
            test_bs.append(v)
            v2 = v.copy()
            v2[0] += 1
            test_bs.append(v2)

        ok_parity = True
        for bvec in test_bs:
            x = sp.simplify(N * bvec)
            is_int = all(sp.simplify(xx).is_Integer for xx in list(x))
            should_int = int(bvec[0]) % 2 == 0
            if is_int != should_int:
                ok_parity = False
                break

        # 6) Smith normal form (subset of q).
        ok_snf = True
        snf_diag: List[int] | None = None
        if q <= q_snf_max:
            S = smith_normal_form(M, domain=sp.ZZ)
            diag = [int(S[i, i]) for i in range(q + 1)]
            snf_diag = diag
            expected_diag = [1] * q + [2]
            ok_snf = diag == expected_diag

        per_q[str(q)] = {
            "inverse_left_ok": bool(ok_left),
            "inverse_right_ok": bool(ok_right),
            "decomp_inv_ok": bool(ok_decomp_inv),
            "decomp_fwd_ok": bool(ok_decomp_fwd),
            "det": str(det_M),
            "det_expected": str(det_expected),
            "det_ok": bool(ok_det),
            "twoN_int_ok": bool(ok_twoN_int),
            "twoN_unique_odd_ok": bool(ok_unique_odd),
            "odd_positions": odd_positions,
            "parity_obstruction_ok": bool(ok_parity),
            "snf_checked": q <= q_snf_max,
            "snf_diag": snf_diag,
        }

        if not (ok_left and ok_right and ok_decomp_inv and ok_decomp_fwd and ok_det and ok_twoN_int and ok_unique_odd and ok_parity and ok_snf):
            # Keep going to report all q.
            pass

    # Aggregate checks.
    def _all(name: str, key: str) -> Check:
        bad = [q for q, d in per_q.items() if not bool(d[key])]
        ok = len(bad) == 0
        return Check(name=name, ok=ok, details="" if ok else f"failed_q={bad}")

    checks.extend(
        [
            _all("inverse_left", "inverse_left_ok"),
            _all("inverse_right", "inverse_right_ok"),
            _all("decomposition_inverse", "decomp_inv_ok"),
            _all("decomposition_forward", "decomp_fwd_ok"),
            _all("determinant", "det_ok"),
            _all("twoN_integral", "twoN_int_ok"),
            _all("twoN_unique_odd_entry", "twoN_unique_odd_ok"),
            _all("parity_obstruction", "parity_obstruction_ok"),
        ]
    )
    # SNF only checked up to q_snf_max.
    bad_snf = [q for q, d in per_q.items() if d["snf_checked"] and d["snf_diag"] != ([1] * int(q) + [2])]
    checks.append(Check(name="smith_normal_form", ok=len(bad_snf) == 0, details="" if len(bad_snf) == 0 else f"failed_q={bad_snf}"))

    out = {
        "q_min": q_min,
        "q_max": q_max,
        "q_snf_max": q_snf_max,
        "checks": [{"name": c.name, "ok": c.ok, "details": c.details} for c in checks],
        "per_q": per_q,
        "elapsed_s": time.time() - t0,
    }

    export_path = export_dir() / "xi_exceptional_integer_model_Mq_audit.json"
    _write_text(export_path, json.dumps(out, indent=2, sort_keys=True) + "\n")

    worst = [c for c in checks if not c.ok]
    if worst:
        print(f"[xi_exceptional_integer_model_Mq_audit] FAIL: {len(worst)} checks failed")
        for c in worst:
            print(f"  - {c.name}: {c.details}")
    else:
        print("[xi_exceptional_integer_model_Mq_audit] OK")


if __name__ == "__main__":
    main()

