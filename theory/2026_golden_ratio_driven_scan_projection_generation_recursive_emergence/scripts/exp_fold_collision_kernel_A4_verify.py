#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify an explicit 5-state nonnegative collision-kernel realization for S4(m).

We work with Fold_m fiber multiplicities d_m(x)=|Fold_m^{-1}(x)| and define:
  S4(m) = sum_x d_m(x)^4.

This script provides an audit trail for the explicit kernel stated in the paper:
  S4(m) = 2 * u^T A4^(m-2) v,   m >= 2,
where A4 is a 5x5 nonnegative integer matrix, u,v are integer vectors.

Verification strategy (fully deterministic):
  - Enumerate S4(m) for m=2..12 (cheap, 2^12=4096 windows).
  - Extend S4(m) for m>=13 by the verified exact recurrence:
      S4(m)=2S4(m-1)+7S4(m-2)+2S4(m-4)-2S4(m-5).
  - Check the kernel readout formula against the recurrence-extended values on a wide range.

All output is English-only by repository convention.
"""

from __future__ import annotations

from itertools import product
from typing import Dict, List, Sequence

from common_phi_fold import Progress, fold_m, word_to_str


# Paper kernel (5-state adjacency matrix).
A4: List[List[int]] = [
    [0, 1, 0, 0, 0],
    [0, 0, 7, 0, 1],
    [0, 1, 2, 0, 0],
    [1, 0, 1, 0, 0],
    [0, 0, 0, 1, 0],
]

u4: List[int] = [9, 404, 1613, 25, 114]  # column vector
v4: List[int] = [1, 0, 0, 0, 0]  # e1


def _matmul(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    n = len(X)
    Z = [[0 for _ in range(n)] for __ in range(n)]
    for i in range(n):
        for k in range(n):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(n):
                Z[i][j] += xik * Y[k][j]
    return Z


def _matpow(A: List[List[int]], e: int) -> List[List[int]]:
    n = len(A)
    P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    B = [row[:] for row in A]
    while e > 0:
        if e & 1:
            P = _matmul(P, B)
        B = _matmul(B, B)
        e >>= 1
    return P


def _dot(u: Sequence[int], M: List[List[int]], v: Sequence[int]) -> int:
    s = 0
    n = len(u)
    for i in range(n):
        ui = u[i]
        if ui == 0:
            continue
        Mi = M[i]
        for j in range(n):
            s += ui * Mi[j] * v[j]
    return s


def s4_from_kernel(m: int) -> int:
    if m < 2:
        raise ValueError("m must be >= 2")
    P = _matpow(A4, m - 2)
    return 2 * _dot(u4, P, v4)


def collision_counts(m: int, progress: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if progress is not None:
            progress.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def S4_enum(m: int) -> int:
    prog = Progress("S4.enum", every_seconds=20.0)
    counts = collision_counts(m, progress=prog)
    return sum(v * v * v * v for v in counts.values())


def extend_S4(seq: Dict[int, int], m_max: int) -> Dict[int, int]:
    out = dict(seq)
    for m in range(13, m_max + 1):
        out[m] = (
            2 * out[m - 1]
            + 7 * out[m - 2]
            + 2 * out[m - 4]
            - 2 * out[m - 5]
        )
    return out


def main() -> None:
    m_enum_min, m_enum_max = 2, 12
    m_verify_max = 40

    print("[A4-verify] Enumerating S4(m) for small m...", flush=True)
    s4: Dict[int, int] = {}
    for m in range(m_enum_min, m_enum_max + 1):
        s4[m] = S4_enum(m)
        print(f"[A4-verify] m={m:2d} S4={s4[m]}", flush=True)

    print("[A4-verify] Extending via exact recurrence for m>=13...", flush=True)
    s4_ext = extend_S4(s4, m_verify_max)

    print("[A4-verify] Verifying kernel readout S4(m)=2 u^T A4^(m-2) v ...", flush=True)
    for m in range(2, m_verify_max + 1):
        lhs = s4_ext[m]
        rhs = s4_from_kernel(m)
        if lhs != rhs:
            raise AssertionError(f"Kernel formula failed at m={m}: lhs={lhs}, rhs={rhs}")
    print("[A4-verify] OK (matches recurrence-extended values).", flush=True)

    print("[A4-verify] Cross-checking against enumerated values for m<=12 ...", flush=True)
    for m in range(m_enum_min, m_enum_max + 1):
        rhs = s4_from_kernel(m)
        if rhs != s4[m]:
            raise AssertionError(f"Enum cross-check failed at m={m}: enum={s4[m]}, kernel={rhs}")
    print("[A4-verify] OK (matches enumeration for m<=12).", flush=True)


if __name__ == "__main__":
    main()

