#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute the Fold_m collision moment S2(m) by enumeration.

This script is for auditability:
  S2(m) = sum_{x in X_m} d_m(x)^2,
  where d_m(x) = |Fold_m^{-1}(x)|.

It verifies the exact recurrence:
  S2(m) = 2 S2(m-1) + 2 S2(m-2) - 2 S2(m-3),  m >= 5,
with initial values S2(2)=6, S2(3)=14, S2(4)=36.

All output is English-only by repository convention.
"""

from __future__ import annotations

import math
from itertools import product
from typing import Dict, List, Tuple

from common_phi_fold import Progress, fold_m, word_to_str


def s2_from_A2(m: int) -> int:
    """Compute S2(m) from the explicit 3-state collision kernel A2."""
    if m < 2:
        raise ValueError("m must be >= 2")
    A2 = [[0, 0, 1], [0, 1, 1], [2, 1, 1]]
    # Integer matrix power (tiny 3x3, so plain multiplication is fine).
    def matmul(X, Y):
        Z = [[0, 0, 0] for _ in range(3)]
        for i in range(3):
            for k in range(3):
                if X[i][k] == 0:
                    continue
                for j in range(3):
                    Z[i][j] += X[i][k] * Y[k][j]
        return Z

    P = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    B = [row[:] for row in A2]
    e = m - 2
    while e > 0:
        if e & 1:
            P = matmul(P, B)
        B = matmul(B, B)
        e >>= 1
    one = [1, 1, 1]
    # one^T P one
    s = 0
    for i in range(3):
        for j in range(3):
            s += one[i] * P[i][j] * one[j]
    return 2 * s


def collision_counts(m: int, progress: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if progress is not None:
            progress.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def s2_from_counts(counts: Dict[str, int]) -> int:
    return sum(v * v for v in counts.values())


def compute_s2_table(m_min: int, m_max: int) -> List[Tuple[int, int, int]]:
    out: List[Tuple[int, int, int]] = []
    for m in range(m_min, m_max + 1):
        prog = Progress("S2", every_seconds=20.0)
        counts = collision_counts(m, progress=prog)
        s2 = s2_from_counts(counts)
        D = max(counts.values()) if counts else 0
        out.append((m, s2, D))
    return out


def verify_recurrence(s2_by_m: Dict[int, int]) -> None:
    # Check the recurrence for all m where it applies.
    for m in sorted(s2_by_m.keys()):
        if m < 5:
            continue
        lhs = s2_by_m[m]
        rhs = 2 * s2_by_m[m - 1] + 2 * s2_by_m[m - 2] - 2 * s2_by_m[m - 3]
        if lhs != rhs:
            raise AssertionError(f"Recurrence failed at m={m}: lhs={lhs}, rhs={rhs}")


def perron_root_r2() -> float:
    # Largest real root of x^3 - 2x^2 - 2x + 2 = 0.
    # Use a simple Newton iteration on the positive root.
    def f(x: float) -> float:
        return x**3 - 2 * x**2 - 2 * x + 2

    def df(x: float) -> float:
        return 3 * x**2 - 4 * x - 2

    x = 2.5
    for _ in range(30):
        x = x - f(x) / df(x)
    return x


def main() -> None:
    m_min, m_max = 2, 16
    table = compute_s2_table(m_min, m_max)
    s2_by_m = {m: s2 for (m, s2, _) in table}

    print("Computed S2(m) and D_m from enumeration.")
    print("Columns: m  S2(m)  D_m")
    for m, s2, D in table:
        print(f"{m:2d}  {s2:10d}  {D:6d}")

    print("\nVerifying the explicit 3-state collision kernel formula ...")
    for m, s2, _ in table:
        s2_A2 = s2_from_A2(m)
        if s2_A2 != s2:
            raise AssertionError(f"A2 formula failed at m={m}: enum={s2}, A2={s2_A2}")
    print("OK.")

    print("\nVerifying recurrence S2(m)=2S2(m-1)+2S2(m-2)-2S2(m-3) for m>=5 ...")
    verify_recurrence(s2_by_m)
    print("OK.")

    r2 = perron_root_r2()
    h2 = math.log(4.0 / r2)
    print(f"\nPerron root r2 (largest real root of x^3-2x^2-2x+2): {r2:.12f}")
    print(f"Renyi-2 projection entropy rate h2 = log(4/r2): {h2:.12f}")


if __name__ == "__main__":
    main()

