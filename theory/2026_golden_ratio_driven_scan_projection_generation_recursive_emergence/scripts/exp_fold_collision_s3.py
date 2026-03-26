#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute the Fold_m triple-collision moment S3(m) by enumeration.

This script is for auditability:
  S3(m) = sum_{x in X_m} d_m(x)^3,
  where d_m(x) = |Fold_m^{-1}(x)|.

It verifies an explicit 3-state realization and recurrence (as stated in the paper draft):
  S3(m) = 2 u^T A3^(m-2) v,  m >= 2,
  S3(m) = 2 S3(m-1) + 4 S3(m-2) - 2 S3(m-3),  m >= 5.

All output is English-only by repository convention.
"""

from __future__ import annotations

import math
from itertools import product
from typing import Dict, List, Sequence, Tuple

from common_phi_fold import Progress, fold_m, word_to_str


def _matmul3(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    Z = [[0, 0, 0] for _ in range(3)]
    for i in range(3):
        for k in range(3):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(3):
                Z[i][j] += xik * Y[k][j]
    return Z


def _matpow3(A: List[List[int]], e: int) -> List[List[int]]:
    P = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    B = [row[:] for row in A]
    while e > 0:
        if e & 1:
            P = _matmul3(P, B)
        B = _matmul3(B, B)
        e >>= 1
    return P


def _dot(u: Sequence[int], M: List[List[int]], v: Sequence[int]) -> int:
    s = 0
    for i in range(3):
        ui = u[i]
        if ui == 0:
            continue
        for j in range(3):
            s += ui * M[i][j] * v[j]
    return s


def s3_from_A3(m: int) -> int:
    """Compute S3(m) from the explicit 3-state kernel A3 and readout vectors."""
    if m < 2:
        raise ValueError("m must be >= 2")
    A3 = [[0, 2, 2], [1, 0, 2], [0, 1, 2]]
    u = [5, 13, 34]
    v = [1, 0, 0]
    P = _matpow3(A3, m - 2)
    return 2 * _dot(u, P, v)


def collision_counts(m: int, progress: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if progress is not None:
            progress.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def s3_from_counts(counts: Dict[str, int]) -> int:
    return sum(v * v * v for v in counts.values())


def compute_s3_table(m_min: int, m_max: int) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    for m in range(m_min, m_max + 1):
        prog = Progress("S3", every_seconds=20.0)
        counts = collision_counts(m, progress=prog)
        s3 = s3_from_counts(counts)
        out.append((m, s3))
    return out


def verify_recurrence(s3_by_m: Dict[int, int]) -> None:
    for m in sorted(s3_by_m.keys()):
        if m < 5:
            continue
        lhs = s3_by_m[m]
        rhs = 2 * s3_by_m[m - 1] + 4 * s3_by_m[m - 2] - 2 * s3_by_m[m - 3]
        if lhs != rhs:
            raise AssertionError(f"Recurrence failed at m={m}: lhs={lhs}, rhs={rhs}")


def perron_root_r3() -> float:
    # Largest real root of x^3 - 2x^2 - 4x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**3 - 2.0 * x**2 - 4.0 * x + 2.0

    def df(x: float) -> float:
        return 3.0 * x**2 - 4.0 * x - 4.0

    x = 3.1
    for _ in range(40):
        x = x - f(x) / df(x)
    return x


def main() -> None:
    m_min, m_max = 2, 18
    table = compute_s3_table(m_min, m_max)
    s3_by_m = {m: s3 for (m, s3) in table}

    print("Computed S3(m) from enumeration.")
    print("Columns: m  S3(m)")
    for m, s3 in table:
        print(f"{m:2d}  {s3:14d}")

    print("\nVerifying the explicit 3-state collision kernel formula ...")
    for m, s3 in table:
        s3_A3 = s3_from_A3(m)
        if s3_A3 != s3:
            raise AssertionError(f"A3 formula failed at m={m}: enum={s3}, A3={s3_A3}")
    print("OK.")

    print("\nVerifying recurrence S3(m)=2S3(m-1)+4S3(m-2)-2S3(m-3) for m>=5 ...")
    verify_recurrence(s3_by_m)
    print("OK.")

    r3 = perron_root_r3()
    h3 = math.log(8.0 / r3)
    print(f"\nPerron root r3 (largest real root of x^3-2x^2-4x+2): {r3:.14f}")
    print(f"Renyi-3 projection entropy rate h3 = log(8/r3): {h3:.14f}")


if __name__ == "__main__":
    main()

