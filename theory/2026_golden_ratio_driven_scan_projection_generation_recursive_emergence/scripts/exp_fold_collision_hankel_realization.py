#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Construct a minimal Hankel realization for S2(m) and relate it to A2.

This script provides an "automata/minimization" viewpoint:
  - Build the Hankel matrices from the sequence a_n := S2(n+2)/2.
  - Compute the canonical (possibly signed) 3x3 shift realization A.
  - Find a unimodular similarity transform P with P^{-1} A P = A2,
    where A2 is the nonnegative integer collision kernel used in the paper.

All output is English-only by repository convention.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import List, Tuple

from common_phi_fold import Progress, fold_m


def s2(m: int) -> int:
    # Enumerate counts for Fold_m.
    from itertools import product as prod
    from common_phi_fold import word_to_str

    counts = {}
    total = 1 << m
    prog = Progress("Hankel", every_seconds=20.0)
    for i, bits in enumerate(prod([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        prog.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return sum(v * v for v in counts.values())


def mat_inv_3(M: List[List[Fraction]]) -> List[List[Fraction]]:
    n = 3
    A = [[M[i][j] for j in range(n)] + [Fraction(int(i == j), 1) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise RuntimeError("Singular matrix in inversion.")
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        for j in range(2 * n):
            A[col][j] /= pv
        for r in range(n):
            if r == col:
                continue
            f = A[r][col]
            if f == 0:
                continue
            for j in range(2 * n):
                A[r][j] -= f * A[col][j]
    return [row[n:] for row in A]


def mat_mul_3(X: List[List[Fraction]], Y: List[List[Fraction]]) -> List[List[Fraction]]:
    Z = [[Fraction(0, 1) for _ in range(3)] for __ in range(3)]
    for i in range(3):
        for k in range(3):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(3):
                Z[i][j] += xik * Y[k][j]
    return Z


def det_int_3(M: List[List[int]]) -> int:
    a, b, c = M[0]
    d, e, f = M[1]
    g, h, i = M[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def inv_unimodular_3(P: List[List[int]]) -> List[List[int]]:
    # Assumes det(P) is +/-1.
    a, b, c = P[0]
    d, e, f = P[1]
    g, h, i = P[2]
    det = det_int_3(P)
    if det not in (1, -1):
        raise ValueError("Matrix is not unimodular.")
    adj = [
        [e * i - f * h, c * h - b * i, b * f - c * e],
        [f * g - d * i, a * i - c * g, c * d - a * f],
        [d * h - e * g, b * g - a * h, a * e - b * d],
    ]
    if det == 1:
        return adj
    return [[-x for x in row] for row in adj]


def mat_mul_int_3(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    Z = [[0, 0, 0] for _ in range(3)]
    for i in range(3):
        for k in range(3):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(3):
                Z[i][j] += xik * Y[k][j]
    return Z


@dataclass(frozen=True)
class Realization:
    A: List[List[int]]
    A2: List[List[int]]
    P: List[List[int]]


def build_hankel_realization(s2_values: List[int]) -> List[List[int]]:
    # a_n = S2(n+2)/2, n>=0. Need S2(2..9) to fill 3x3 Hankel.
    def a(n: int) -> Fraction:
        return Fraction(s2_values[n + 2], 2)

    H0 = [[a(i + j) for j in range(3)] for i in range(3)]
    H1 = [[a(i + j + 1) for j in range(3)] for i in range(3)]
    H0inv = mat_inv_3(H0)
    A = mat_mul_3(H0inv, H1)
    # Convert to integers (it should already be integer-valued here).
    A_int: List[List[int]] = []
    for row in A:
        r: List[int] = []
        for x in row:
            if x.denominator != 1:
                raise RuntimeError(f"Non-integer A entry: {x}")
            r.append(int(x))
        A_int.append(r)
    return A_int


def find_similarity_to_A2(A: List[List[int]], A2: List[List[int]], bound: int = 1) -> List[List[int]]:
    vals = range(-bound, bound + 1)
    for entries in product(vals, repeat=9):
        P = [list(entries[0:3]), list(entries[3:6]), list(entries[6:9])]
        det = det_int_3(P)
        if det not in (1, -1):
            continue
        Pinv = inv_unimodular_3(P)
        B = mat_mul_int_3(mat_mul_int_3(Pinv, A), P)
        if B == A2:
            return P
    raise RuntimeError(f"No similarity P found within bound={bound}.")


def main() -> None:
    print("Enumerating S2(m) for m=2..9 to build Hankel realization...")
    s2_vals = [0] * 10
    for m in range(2, 10):
        s2_vals[m] = s2(m)
        print(f"S2({m}) = {s2_vals[m]}")

    A = build_hankel_realization(s2_vals)
    # Also show det(H0) to certify invertibility in the construction.
    from fractions import Fraction as F

    def a(n: int) -> F:
        return F(s2_vals[n + 2], 2)

    H0 = [[a(i + j) for j in range(3)] for i in range(3)]
    detH0 = (
        H0[0][0] * (H0[1][1] * H0[2][2] - H0[1][2] * H0[2][1])
        - H0[0][1] * (H0[1][0] * H0[2][2] - H0[1][2] * H0[2][0])
        + H0[0][2] * (H0[1][0] * H0[2][1] - H0[1][1] * H0[2][0])
    )
    print(f"\nHankel H0 det = {detH0} (nonzero => rank 3 in this window)")
    print("H0 entries (a_n = S2(n+2)/2, n>=0):")
    for row in H0:
        print("  ", [str(x) for x in row])

    print("\nCanonical Hankel shift realization A (may have signed entries):")
    for row in A:
        print("  ", row)

    A2 = [[0, 0, 1], [0, 1, 1], [2, 1, 1]]
    P = find_similarity_to_A2(A, A2, bound=1)
    print("\nFound unimodular similarity transform P with P^{-1} A P = A2:")
    for row in P:
        print("  ", row)

    Pinv = inv_unimodular_3(P)
    B = mat_mul_int_3(mat_mul_int_3(Pinv, A), P)
    if B != A2:
        raise AssertionError("Similarity verification failed.")
    print("Similarity verification OK.")


if __name__ == "__main__":
    main()

