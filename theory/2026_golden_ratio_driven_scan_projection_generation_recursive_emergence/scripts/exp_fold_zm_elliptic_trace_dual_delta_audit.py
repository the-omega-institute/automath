#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the trace-dual / inversion identities controlled by the different generator
delta_diff = dF/dX for the quartic plane model of the elliptic y-cover.

We verify in K = Q(y)[X]/(F) with
  F(X,y) = X^4 - X^3 - (2y+1)X^2 + X + y(y+1),
that
  Tr_{K/Q(y)}(X^m / delta_diff) = 0  for m=0,1,2,
  Tr_{K/Q(y)}(X^3 / delta_diff) = 1,
where delta_diff = dF/dX.

Equivalently, for delta := -delta_diff (the Jacobian factor appearing in dy),
  Tr(X^3 / delta) = -1.

We also verify the explicit trace-dual basis in the inverse different:
writing F(X,y)=X^4+a3 X^3+a2 X^2+a1 X + a0, define the Horner truncations
  q0=1,
  q1=X+a3,
  q2=X^2+a3 X + a2,
  q3=X^3+a3 X^2+a2 X + a1.
Then {1,X,X^2,X^3} is trace-dual to {q3/delta_diff, q2/delta_diff, q1/delta_diff, q0/delta_diff}.

Outputs:
  - artifacts/export/fold_zm_elliptic_trace_dual_delta_audit.json
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _together_sstr(expr: sp.Expr) -> str:
    return sp.sstr(sp.together(sp.simplify(expr)))


def _is_zero(expr: sp.Expr) -> bool:
    return bool(sp.factor(sp.together(expr)) == 0)


def _companion_matrix_quartic(a3: sp.Expr, a2: sp.Expr, a1: sp.Expr, a0: sp.Expr) -> sp.Matrix:
    """
    Companion matrix for monic quartic:
      X^4 + a3 X^3 + a2 X^2 + a1 X + a0.
    In basis [1, X, X^2, X^3], multiplication-by-X is this matrix.
    """
    return sp.Matrix(
        [
            [0, 0, 0, -a0],
            [1, 0, 0, -a1],
            [0, 1, 0, -a2],
            [0, 0, 1, -a3],
        ]
    )


@dataclass(frozen=True)
class Payload:
    trace_delta_diff_m0_to_m3: Dict[str, str]
    trace_delta_m0_to_m3: Dict[str, str]
    traces_ok_delta_diff: bool
    traces_ok_delta: bool
    pairing_matrix: List[List[str]]
    pairing_ok: bool
    reconstruction_ok: bool


def main() -> None:
    t0 = time.time()
    print("[fold-zm-elliptic-trace-dual-delta] start", flush=True)

    X, y = sp.symbols("X y")

    # Quartic plane model: K = Q(y)[X]/(F).
    F = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)
    delta_diff = sp.diff(F, X)  # dF/dX

    # Companion matrix for multiplication by X.
    # F = X^4 + a3 X^3 + a2 X^2 + a1 X + a0.
    a3 = sp.Integer(-1)
    a2 = -(2 * y + 1)
    a1 = sp.Integer(1)
    a0 = y * (y + 1)
    C = _companion_matrix_quartic(a3=a3, a2=a2, a1=a1, a0=a0)

    # Multiplication by delta_diff corresponds to the polynomial delta_diff(C).
    I = sp.eye(4)
    deltaM = 4 * (C**3) - 3 * (C**2) - (4 * y + 2) * C + I
    inv_deltaM = deltaM.inv()

    # Trace checks for X^m / delta_diff.
    trace_delta_diff: Dict[str, sp.Expr] = {}
    for m in range(0, 4):
        trace_delta_diff[str(m)] = sp.simplify((C**m * inv_deltaM).trace())

    traces_ok_delta_diff = (
        _is_zero(trace_delta_diff["0"])
        and _is_zero(trace_delta_diff["1"])
        and _is_zero(trace_delta_diff["2"])
        and _is_zero(trace_delta_diff["3"] - 1)
    )

    # Sign convention bridge: delta := -delta_diff.
    # Multiplication by 1/delta equals -1/delta_diff, hence inv matrix is -inv_deltaM.
    trace_delta: Dict[str, sp.Expr] = {}
    for m in range(0, 4):
        trace_delta[str(m)] = sp.simplify((C**m * (-inv_deltaM)).trace())
    traces_ok_delta = (
        _is_zero(trace_delta["0"])
        and _is_zero(trace_delta["1"])
        and _is_zero(trace_delta["2"])
        and _is_zero(trace_delta["3"] + 1)
    )

    # Trace-dual basis via Horner truncations.
    # F = X^4 + a3 X^3 + a2 X^2 + a1 X + a0 (monic quartic).
    # q0=1, q1=X+a3, q2=X^2+a3 X+a2, q3=X^3+a3 X^2+a2 X + a1.
    q0M = I
    q1M = C + a3 * I
    q2M = (C**2) + a3 * C + a2 * I
    q3M = (C**3) + a3 * (C**2) + a2 * C + a1 * I

    dual = [
        q3M * inv_deltaM,  # pairs with 1
        q2M * inv_deltaM,  # pairs with X
        q1M * inv_deltaM,  # pairs with X^2
        q0M * inv_deltaM,  # pairs with X^3
    ]

    pairing: List[List[sp.Expr]] = []
    pairing_ok = True
    for i in range(0, 4):
        row: List[sp.Expr] = []
        for j in range(0, 4):
            entry = sp.simplify(((C**i) * dual[j]).trace())
            row.append(entry)
            if not _is_zero(entry - (1 if i == j else 0)):
                pairing_ok = False
        pairing.append(row)

    # Reconstruction identity on the basis elements a = X^k.
    reconstruction_ok = True
    for k in range(0, 4):
        M_a = C**k
        coeffs: List[sp.Expr] = [sp.simplify((M_a * dual[j]).trace()) for j in range(0, 4)]
        M_recon = sp.zeros(4)
        for j in range(0, 4):
            M_recon += coeffs[j] * (C**j)
        # Compare matrices entrywise.
        diff = sp.simplify(M_recon - M_a)
        for entry in list(diff):
            if not _is_zero(entry):
                reconstruction_ok = False
                break
        if not reconstruction_ok:
            break

    payload = Payload(
        trace_delta_diff_m0_to_m3={m: _together_sstr(v) for m, v in trace_delta_diff.items()},
        trace_delta_m0_to_m3={m: _together_sstr(v) for m, v in trace_delta.items()},
        traces_ok_delta_diff=bool(traces_ok_delta_diff),
        traces_ok_delta=bool(traces_ok_delta),
        pairing_matrix=[[ _together_sstr(e) for e in row ] for row in pairing],
        pairing_ok=bool(pairing_ok),
        reconstruction_ok=bool(reconstruction_ok),
    )

    out = export_dir() / "fold_zm_elliptic_trace_dual_delta_audit.json"
    _write_json(out, asdict(payload))

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-trace-dual-delta] checks:"
        f" traces_delta_diff={traces_ok_delta_diff} traces_delta={traces_ok_delta}"
        f" pairing={pairing_ok} recon={reconstruction_ok} seconds={dt:.3f}",
        flush=True,
    )
    print(f"[fold-zm-elliptic-trace-dual-delta] wrote {out}", flush=True)
    print("[fold-zm-elliptic-trace-dual-delta] done", flush=True)


if __name__ == "__main__":
    main()

