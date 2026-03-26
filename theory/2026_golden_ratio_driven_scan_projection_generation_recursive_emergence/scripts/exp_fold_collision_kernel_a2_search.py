#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Derive the 3-state collision kernel A2 for S2(m).

Goal:
  - Enumerate S2(m) for small m using Fold_m.
  - Recover the minimal order-3 linear recurrence for S2(m).
  - Search a small nonnegative 3x3 integer matrix A2 such that
        S2(m) = 2 * 1^T * A2^(m-2) * 1   for m in a verification range.

This provides an auditable construction of the "collision kernel" realization
used in the paper (Section 8, S2-subsection).

All output is English-only by repository convention.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Dict, List, Optional, Tuple

from common_phi_fold import Progress, fold_m, word_to_str


def collision_counts(m: int, progress: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if progress is not None:
            progress.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def s2(m: int) -> int:
    counts = collision_counts(m, progress=Progress("A2.search", every_seconds=20.0))
    return sum(v * v for v in counts.values())


def solve_recurrence_order3(seq: List[int]) -> Tuple[int, int, int]:
    """Solve for (a,b,c) s.t. S_m = a S_{m-1} + b S_{m-2} + c S_{m-3}."""
    # Use exact integer solving on 3 equations.
    # Build from m=5..7 using 2..7 data.
    # seq is 1-indexed list where seq[m]=S_m
    import fractions

    def frac(x: int) -> fractions.Fraction:
        return fractions.Fraction(x, 1)

    # equations for m=5,6,7
    A = [
        [frac(seq[4]), frac(seq[3]), frac(seq[2])],
        [frac(seq[5]), frac(seq[4]), frac(seq[3])],
        [frac(seq[6]), frac(seq[5]), frac(seq[4])],
    ]
    b = [frac(seq[5]), frac(seq[6]), frac(seq[7])]

    # Gaussian elimination 3x3
    M = [A[i] + [b[i]] for i in range(3)]
    for col in range(3):
        piv = None
        for r in range(col, 3):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise RuntimeError("Singular system while solving recurrence.")
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        for j in range(col, 4):
            M[col][j] /= pv
        for r in range(3):
            if r == col:
                continue
            f = M[r][col]
            if f == 0:
                continue
            for j in range(col, 4):
                M[r][j] -= f * M[col][j]

    a, bcoef, c = (M[0][3], M[1][3], M[2][3])
    if a.denominator != 1 or bcoef.denominator != 1 or c.denominator != 1:
        raise RuntimeError(f"Non-integer recurrence: {(a, bcoef, c)}")
    return int(a), int(bcoef), int(c)


def matmul3(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    Z = [[0, 0, 0] for _ in range(3)]
    for i in range(3):
        for k in range(3):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(3):
                Z[i][j] += xik * Y[k][j]
    return Z


def matpow3(A: List[List[int]], e: int) -> List[List[int]]:
    P = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    B = [row[:] for row in A]
    while e > 0:
        if e & 1:
            P = matmul3(P, B)
        B = matmul3(B, B)
        e >>= 1
    return P


def quad_form_one(A: List[List[int]], e: int) -> int:
    """Return 2 * 1^T A^e 1."""
    P = matpow3(A, e)
    one = [1, 1, 1]
    s = 0
    for i in range(3):
        for j in range(3):
            s += one[i] * P[i][j] * one[j]
    return 2 * s


@dataclass(frozen=True)
class A2Candidate:
    A: List[List[int]]
    max_entry: int


def search_A2(
    seq: List[int],
    m_min: int,
    m_max: int,
    entry_max: int = 2,
) -> Optional[A2Candidate]:
    """Bruteforce nonnegative 3x3 integer matrices to fit the sequence."""
    target = {m: seq[m] for m in range(m_min, m_max + 1)}
    # Search in row-major order for a stable, auditable canonical choice.
    rng = range(0, entry_max + 1)
    for a00 in rng:
        for a01 in rng:
            for a02 in rng:
                for a10 in rng:
                    for a11 in rng:
                        for a12 in rng:
                            for a20 in rng:
                                for a21 in rng:
                                    for a22 in rng:
                                        A = [
                                            [a00, a01, a02],
                                            [a10, a11, a12],
                                            [a20, a21, a22],
                                        ]
                                        ok = True
                                        for m in range(m_min, m_max + 1):
                                            val = quad_form_one(A, m - 2)
                                            if val != target[m]:
                                                ok = False
                                                break
                                        if ok:
                                            return A2Candidate(A=A, max_entry=entry_max)
    return None


def main() -> None:
    m_eval_min, m_eval_max = 2, 16
    seq = [0] * (m_eval_max + 1)
    print("Enumerating S2(m) ...")
    for m in range(m_eval_min, m_eval_max + 1):
        seq[m] = s2(m)
        print(f"S2({m}) = {seq[m]}")

    print("\nRecovering order-3 recurrence S_m = a S_{m-1} + b S_{m-2} + c S_{m-3} ...")
    a, bcoef, c = solve_recurrence_order3(seq)
    print(f"(a,b,c) = ({a},{bcoef},{c})")
    # Verify recurrence on the computed range.
    for m in range(5, m_eval_max + 1):
        lhs = seq[m]
        rhs = a * seq[m - 1] + bcoef * seq[m - 2] + c * seq[m - 3]
        if lhs != rhs:
            raise AssertionError(f"Recurrence check failed at m={m}: lhs={lhs}, rhs={rhs}")
    print("Recurrence check OK.")

    print("\nSanity check: order-2 recurrence must fail.")
    # Solve order-2 recurrence from m=4,5 and show it fails at m=6.
    # S4 = alpha S3 + beta S2, S5 = alpha S4 + beta S3.
    import fractions

    S2, S3, S4, S5, S6 = seq[2], seq[3], seq[4], seq[5], seq[6]
    det = S3 * S3 - S2 * S4
    alpha = fractions.Fraction(S4 * S3 - S2 * S5, det)
    beta = fractions.Fraction(S3 * S5 - S4 * S4, det)
    pred6 = alpha * S5 + beta * S4
    print(f"alpha={alpha}, beta={beta}, predicted S6={pred6}, actual S6={S6}")
    if pred6 == S6:
        raise AssertionError("Unexpected: order-2 recurrence matched at m=6.")

    print("\nSearching a nonnegative 3x3 realization A2 with S2(m)=2*1^T A2^(m-2) 1 ...")
    cand = search_A2(seq, m_min=2, m_max=16, entry_max=2)
    if cand is None:
        print("No A2 found with entry_max=2. Try increasing the bound.")
        raise SystemExit(2)

    print("Found A2:")
    for row in cand.A:
        print("  ", row)
    # Final verification
    for m in range(2, 17):
        val = quad_form_one(cand.A, m - 2)
        if val != seq[m]:
            raise AssertionError(f"A2 mismatch at m={m}: seq={seq[m]}, A2={val}")
    print("A2 verification OK on m=2..16.")


if __name__ == "__main__":
    main()

