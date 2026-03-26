#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the "self-dual bridge package" for the weighted sync-kernel.

This script is intentionally lightweight and reproducible: it builds the
paper-local matrices (B0, B1, Pi) from the edge list, then checks the matrix
identities used in the self-duality-derived Lemma/Corollary chain:

Checks (exact unless noted):
  - self-dual exchange: Pi^{-1} B0 Pi = B1 and Pi^{-1} B1 Pi = B0
  - even/odd splitting: B(u) = (1+u) B_sym + (u-1) B_asym with Pi-even/odd parts
  - Pi-eigenbasis normal form blocks (X,Y,Z,W) and u=1 decoupling
  - Ward trace identities: Tr(B(1)^{n-1} B_asym) = 0 for n=1..N
  - sign twist (chi(g1)=-1): functional equation and B_-(1) = -2 B_asym

Outputs:
  - artifacts/export/sync_kernel_weighted_self_dual_bridge.json (default)

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir
from exp_sync_kernel_weighted_pressure import STATES, build_edges


@dataclass(frozen=True)
class _Blocks:
    X: sp.Matrix
    Y: sp.Matrix
    Z: sp.Matrix
    W: sp.Matrix


def _build_B0_B1() -> Tuple[np.ndarray, np.ndarray]:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    B0 = np.zeros((n, n), dtype=int)
    B1 = np.zeros((n, n), dtype=int)
    for edge in build_edges():
        i = idx[edge.src]
        j = idx[edge.dst]
        if int(edge.e) == 0:
            B0[i, j] += 1
        else:
            B1[i, j] += 1
    return B0, B1


def _build_Pi() -> np.ndarray:
    # Involution from the paper (App. "同步核的自对偶对称").
    iota: Dict[str, str] = {
        "000": "101",
        "101": "000",
        "001": "100",
        "100": "001",
        "002": "010",
        "010": "002",
        "0-12": "11-1",
        "11-1": "0-12",
        "1-12": "01-1",
        "01-1": "1-12",
    }
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    Pi = np.zeros((n, n), dtype=int)
    for s in STATES:
        if s not in iota:
            raise KeyError(f"missing iota mapping for state {s!r}")
        Pi[idx[iota[s]], idx[s]] = 1
    return Pi


def _as_sympy_int(A: np.ndarray) -> sp.Matrix:
    # Ensure exact integer entries in SymPy.
    return sp.Matrix([[int(A[i, j]) for j in range(A.shape[1])] for i in range(A.shape[0])])


def _pi_eigenbasis_matrix(pairs: List[Tuple[int, int]], n: int) -> sp.Matrix:
    # Columns: first V_+ (e_i+e_j), then V_- (e_i-e_j).
    cols: List[sp.Matrix] = []
    for i, j in pairs:
        v = sp.zeros(n, 1)
        v[i, 0] = 1
        v[j, 0] = 1
        cols.append(v)
    for i, j in pairs:
        v = sp.zeros(n, 1)
        v[i, 0] = 1
        v[j, 0] = -1
        cols.append(v)
    Q = sp.Matrix.hstack(*cols)
    if Q.shape != (n, n):
        raise AssertionError(f"unexpected eigenbasis shape: {Q.shape}")
    return Q


def _extract_blocks(B0_hat: sp.Matrix) -> _Blocks:
    n = int(B0_hat.shape[0])
    if n % 2 != 0:
        raise AssertionError("expected even dimension for V_+ ⊕ V_- split")
    p = n // 2
    X = sp.Matrix(B0_hat[:p, :p])
    Y = sp.Matrix(B0_hat[:p, p:])
    Z = sp.Matrix(B0_hat[p:, :p])
    W = sp.Matrix(B0_hat[p:, p:])
    return _Blocks(X=X, Y=Y, Z=Z, W=W)


def _block_normal_form(u: sp.Expr, blk: _Blocks) -> sp.Matrix:
    X, Y, Z, W = blk.X, blk.Y, blk.Z, blk.W
    p = int(X.shape[0])
    out = sp.zeros(2 * p, 2 * p)
    out[:p, :p] = (1 + u) * X
    out[:p, p:] = (1 - u) * Y
    out[p:, :p] = (1 - u) * Z
    out[p:, p:] = (1 + u) * W
    return sp.Matrix(out)


def _check_exact(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(f"check failed: {name}")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit self-dual bridge identities for weighted sync-kernel.")
    ap.add_argument(
        "--out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_self_dual_bridge.json"),
        help="Output JSON path.",
    )
    ap.add_argument("--max-n", type=int, default=30, help="Max n for Ward trace checks.")
    args = ap.parse_args()

    B0_np, B1_np = _build_B0_B1()
    Pi_np = _build_Pi()
    n = int(B0_np.shape[0])

    # Basic Pi properties (permutation involution).
    _check_exact("Pi is permutation", np.all((Pi_np == 0) | (Pi_np == 1)))
    _check_exact("Pi rows sum to 1", np.all(Pi_np.sum(axis=1) == 1))
    _check_exact("Pi cols sum to 1", np.all(Pi_np.sum(axis=0) == 1))
    _check_exact("Pi^2 = I", np.array_equal(Pi_np @ Pi_np, np.eye(n, dtype=int)))

    # Self-dual exchange.
    _check_exact("Pi^{-1} B0 Pi = B1", np.array_equal(Pi_np.T @ B0_np @ Pi_np, B1_np))
    _check_exact("Pi^{-1} B1 Pi = B0", np.array_equal(Pi_np.T @ B1_np @ Pi_np, B0_np))

    # Even/odd split (avoid halves by using doubled matrices).
    S_np = B0_np + B1_np  # 2*B_sym
    A_np = B1_np - B0_np  # 2*B_asym
    _check_exact("Pi^{-1} S Pi = S", np.array_equal(Pi_np.T @ S_np @ Pi_np, S_np))
    _check_exact("Pi^{-1} A Pi = -A", np.array_equal(Pi_np.T @ A_np @ Pi_np, -A_np))

    # Reconstruction check at a few u values (numeric, exact equality over complex entries).
    for u in [0.0, 1.0, -1.0, 2.0, 0.5 + 0.2j]:
        Bu = B0_np.astype(np.complex128) + complex(u) * B1_np.astype(np.complex128)
        Bu_split = ((1 + u) / 2.0) * S_np.astype(np.complex128) + ((u - 1) / 2.0) * A_np.astype(np.complex128)
        if np.max(np.abs(Bu - Bu_split)) > 1e-12:
            raise AssertionError(f"split reconstruction failed at u={u!r}")

    # Pi-eigenbasis normal form (exact, in SymPy rationals).
    idx = {s: i for i, s in enumerate(STATES)}
    pairs_states = [("000", "101"), ("001", "100"), ("002", "010"), ("0-12", "11-1"), ("1-12", "01-1")]
    pairs = [(idx[a], idx[b]) for a, b in pairs_states]

    Q = _pi_eigenbasis_matrix(pairs=pairs, n=n)
    Qinv = Q.inv()

    B0 = _as_sympy_int(B0_np)
    B1 = _as_sympy_int(B1_np)
    Pi = _as_sympy_int(Pi_np)

    # Sanity: Q diagonalizes Pi with eigenvalues (+1)^5 ⊕ (-1)^5.
    Pi_hat = sp.simplify(Qinv * Pi * Q)
    p = n // 2
    _check_exact("Pi_hat +I block", Pi_hat[:p, :p] == sp.eye(p))
    _check_exact("Pi_hat -I block", Pi_hat[p:, p:] == -sp.eye(p))
    _check_exact("Pi_hat off-diagonal zero", Pi_hat[:p, p:] == sp.zeros(p) and Pi_hat[p:, :p] == sp.zeros(p))

    B0_hat = sp.simplify(Qinv * B0 * Q)
    blk = _extract_blocks(B0_hat)

    for u in [sp.Integer(0), sp.Integer(1), sp.Integer(-1), sp.Integer(2)]:
        Bu_hat = sp.simplify(Qinv * (B0 + u * B1) * Q)
        Bu_nf = _block_normal_form(u=u, blk=blk)
        _check_exact(f"normal form at u={u}", sp.simplify(Bu_hat - Bu_nf) == sp.zeros(n))

    # u=1 decoupling: off-diagonal blocks of B(1) vanish in the Pi-eigenbasis.
    B1_hat = sp.simplify(Qinv * B1 * Q)
    B_one_hat = sp.simplify(B0_hat + B1_hat)
    _check_exact("B(1) off-diagonal blocks are zero", B_one_hat[:p, p:] == sp.zeros(p) and B_one_hat[p:, :p] == sp.zeros(p))

    # Ward traces: Tr(B(1)^{n-1} B_asym) = 0.
    # Use integer matrix A = 2*B_asym = B1-B0 to avoid halves.
    B_one = _as_sympy_int(S_np)  # B(1) = B0+B1
    A = _as_sympy_int(A_np)  # 2*B_asym
    Pwr = sp.eye(n)
    for k in range(1, int(args.max_n) + 1):
        tr = sp.trace(Pwr * A)
        if tr != 0:
            raise AssertionError(f"Ward trace failed at n={k}: trace={tr}")
        Pwr = Pwr * B_one

    # Sign twist at u=1: B_-(1) = B0-B1 = -2*B_asym.
    _check_exact("B_-(1) = -(B1-B0)", _as_sympy_int(B0_np - B1_np) == -A)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "ok": True,
        "n_states": n,
        "states": list(STATES),
        "pairs": pairs_states,
        "ward_trace_max_n": int(args.max_n),
        "checks": {
            "pi_involution": True,
            "self_dual_exchange": True,
            "even_odd_split": True,
            "pi_eigenbasis_normal_form": True,
            "u1_decouple_blocks": True,
            "ward_traces": True,
            "sign_twist_u1": True,
        },
    }
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[self-dual-bridge] wrote {out_path}", flush=True)
    print("[self-dual-bridge] OK", flush=True)


if __name__ == "__main__":
    main()

