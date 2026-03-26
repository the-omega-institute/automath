#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Construct a Hankel minimal realization for S4(m) and search a nonnegative integer kernel A4.

We define collision moments:
  S_k(m) = sum_{x in X_m} d_m(x)^k,  d_m(x)=|Fold_m^{-1}(x)|.

For k=4 the paper verifies an exact order-5 integer recurrence starting at m>=13:
  S4(m) = 2 S4(m-1) + 7 S4(m-2) + 0 S4(m-3) + 2 S4(m-4) - 2 S4(m-5).

This script:
  - enumerates S4(m) for m=2..12 (cheap) to get initial data,
  - extends the sequence via the exact recurrence,
  - builds the canonical Hankel shift realization A = H0^{-1} H1 for a_n := S4(n+2),
  - searches a unimodular similarity P (via random elementary transforms) such that
      A4 := P^{-1} A P
    has nonnegative integer entries (interpretable as an adjacency kernel),
  - exports A4 and the transformed readout vectors.

Outputs:
  - artifacts/export/collision_kernel_A4_search.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir
from common_phi_fold import Progress, fold_m, word_to_str


def collision_counts(m: int, prog: Progress) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        prog.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def S4_enum(m: int) -> int:
    prog = Progress("S4.enum", every_seconds=20.0)
    counts = collision_counts(m, prog)
    return sum(v * v * v * v for v in counts.values())


REC4 = [2, 7, 0, 2, -2]  # order 5, m>=13


def extend_S4(seq: Dict[int, int], m_max: int) -> Dict[int, int]:
    out = dict(seq)
    for m in range(13, m_max + 1):
        out[m] = (
            REC4[0] * out[m - 1]
            + REC4[1] * out[m - 2]
            + REC4[2] * out[m - 3]
            + REC4[3] * out[m - 4]
            + REC4[4] * out[m - 5]
        )
    return out


def mat_inv(M: List[List[Fraction]]) -> List[List[Fraction]]:
    n = len(M)
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


def mat_mul(X: List[List[Fraction]], Y: List[List[Fraction]]) -> List[List[Fraction]]:
    n = len(X)
    Z = [[Fraction(0, 1) for _ in range(n)] for __ in range(n)]
    for i in range(n):
        for k in range(n):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(n):
                Z[i][j] += xik * Y[k][j]
    return Z


def mat_mul_int(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
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


def det_int(M: List[List[int]]) -> int:
    # Bareiss determinant for small n.
    n = len(M)
    A = [row[:] for row in M]
    det_sign = 1
    pivot_prev = 1
    for k in range(n - 1):
        pivot = A[k][k]
        if pivot == 0:
            swap = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    swap = i
                    break
            if swap is None:
                return 0
            A[k], A[swap] = A[swap], A[k]
            det_sign = -det_sign
            pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = A[i][j] * pivot - A[i][k] * A[k][j]
                if pivot_prev != 1:
                    A[i][j] //= pivot_prev
        pivot_prev = pivot
    return det_sign * A[n - 1][n - 1]


def inv_unimodular(P: List[List[int]]) -> List[List[int]]:
    # Compute inverse via adjugate / det; assumes det = ±1.
    import itertools

    n = len(P)
    d = det_int(P)
    if d not in (1, -1):
        raise ValueError("Matrix is not unimodular.")

    def minor_det(i0: int, j0: int) -> int:
        M = []
        for i in range(n):
            if i == i0:
                continue
            row = []
            for j in range(n):
                if j == j0:
                    continue
                row.append(P[i][j])
            M.append(row)
        # recurse for n<=4 ok, but here n=5; still ok with Bareiss.
        return det_int(M)

    adj = [[0 for _ in range(n)] for __ in range(n)]
    for i, j in itertools.product(range(n), range(n)):
        co = minor_det(i, j)
        if (i + j) % 2 == 1:
            co = -co
        adj[j][i] = co  # transpose
    if d == 1:
        return adj
    return [[-x for x in row] for row in adj]


def build_hankel_shift_realization(a: List[int], d: int) -> Tuple[List[List[int]], List[int], List[int]]:
    # a_n is 0-indexed.
    def af(n: int) -> Fraction:
        return Fraction(a[n], 1)

    H0 = [[af(i + j) for j in range(d)] for i in range(d)]
    H1 = [[af(i + j + 1) for j in range(d)] for i in range(d)]
    H0inv = mat_inv(H0)
    A = mat_mul(H0inv, H1)
    A_int: List[List[int]] = []
    for row in A:
        r: List[int] = []
        for x in row:
            if x.denominator != 1:
                raise RuntimeError(f"Non-integer A entry: {x}")
            r.append(int(x))
        A_int.append(r)

    # a_n = alpha^T A^n beta with alpha^T = e0^T H0 and beta = e0.
    alpha = [int(H0[0][j]) for j in range(d)]
    beta = [1] + [0] * (d - 1)
    return A_int, alpha, beta


def apply_similarity(A: List[List[int]], P: List[List[int]]) -> List[List[int]]:
    Pinv = inv_unimodular(P)
    return mat_mul_int(mat_mul_int(Pinv, A), P)


def vec_mul_row(v: List[int], M: List[List[int]]) -> List[int]:
    n = len(v)
    out = [0] * n
    for j in range(n):
        s = 0
        for i in range(n):
            s += v[i] * M[i][j]
        out[j] = s
    return out


def mat_vec(M: List[List[int]], v: List[int]) -> List[int]:
    n = len(v)
    out = [0] * n
    for i in range(n):
        s = 0
        Mi = M[i]
        for j in range(n):
            s += Mi[j] * v[j]
        out[i] = s
    return out


def dot(u: List[int], v: List[int]) -> int:
    return sum(ui * vi for ui, vi in zip(u, v))


def cost_nonneg(A: List[List[int]]) -> int:
    neg = 0
    big = 0
    for row in A:
        for x in row:
            if x < 0:
                neg += -x
            if x > 50:
                big += x - 50
    return 1000 * neg + big


def random_elementary_unimodular(n: int, rng: random.Random) -> List[List[int]]:
    # Return an elementary unimodular matrix E (det=±1).
    # Types: swap, sign flip, shear.
    E = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    t = rng.choice(["swap", "flip", "shear"])
    if t == "swap":
        i, j = rng.sample(range(n), 2)
        E[i], E[j] = E[j], E[i]
        return E
    if t == "flip":
        i = rng.randrange(n)
        E[i][i] = -1
        return E
    # shear: add k * row j to row i in basis change matrix, i!=j, k in {-2,-1,1,2}
    i, j = rng.sample(range(n), 2)
    k = rng.choice([-5, -4, -3, -2, -1, 1, 2, 3, 4, 5])
    E[i][j] = k
    return E


def mat_mul_unimodular(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    return mat_mul_int(A, B)


def search_nonnegative_similarity(
    A: List[List[int]],
    *,
    steps: int,
    seed: int,
    prog: Progress,
) -> Tuple[List[List[int]], List[List[int]], int]:
    n = len(A)
    rng = random.Random(seed)

    # Fast path: try single elementary shears (often enough in practice).
    I = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    k_vals = [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for k in k_vals:
                P1 = [row[:] for row in I]
                P1[i][j] = k
                try:
                    A1 = apply_similarity(A, P1)
                except Exception:
                    continue
                if cost_nonneg(A1) == 0:
                    prog.tick(f"found 1-step nonnegative similarity: i={i} j={j} k={k}")
                    return A1, P1, 0

    P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    Acur = [row[:] for row in A]
    cur_cost = cost_nonneg(Acur)
    best_cost = cost_nonneg(Acur)
    best_A = [row[:] for row in Acur]
    best_P = [row[:] for row in P]

    for it in range(1, steps + 1):
        E = random_elementary_unimodular(n, rng)
        P2 = mat_mul_unimodular(P, E)
        try:
            A2 = apply_similarity(A, P2)
        except Exception:
            continue
        c = cost_nonneg(A2)
        # Metropolis-like acceptance: compare to current, not global best.
        # We allow occasional uphill moves for exploration.
        accept = c <= cur_cost or rng.random() < 0.05
        if accept:
            P = P2
            Acur = A2
            cur_cost = c
            if c < best_cost:
                best_cost = c
                best_A = [row[:] for row in A2]
                best_P = [row[:] for row in P2]
                prog.tick(f"best cost={best_cost} at it={it}")
                if best_cost == 0:
                    break
        if it % 2000 == 0:
            prog.tick(f"it={it}/{steps} best_cost={best_cost}")

    return best_A, best_P, best_cost


@dataclass(frozen=True)
class Result:
    d: int
    recurrence: List[int]
    S4_initial: Dict[str, int]
    A_hankel: List[List[int]]
    alpha_hankel: List[int]
    beta_hankel: List[int]
    A4: List[List[int]]
    P: List[List[int]]
    cost: int


def main() -> None:
    parser = argparse.ArgumentParser(description="Hankel realization and nonnegative-kernel search for S4(m).")
    parser.add_argument("--m-enum-max", type=int, default=12, help="Max m to enumerate exactly for initial values.")
    parser.add_argument("--m-max", type=int, default=40, help="Max m to extend (by recurrence) for verification.")
    parser.add_argument("--steps", type=int, default=80000, help="Random search steps for unimodular similarity.")
    parser.add_argument("--seed", type=int, default=20260203, help="RNG seed.")
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    prog = Progress("A4.search", every_seconds=20.0)
    S4: Dict[int, int] = {}
    for m in range(2, args.m_enum_max + 1):
        S4[m] = S4_enum(m)
        print(f"[A4.search] S4({m}) = {S4[m]}", flush=True)

    S4 = extend_S4(S4, args.m_max)
    # Verify recurrence on the extended range.
    for m in range(13, args.m_max + 1):
        lhs = S4[m]
        rhs = (
            REC4[0] * S4[m - 1]
            + REC4[1] * S4[m - 2]
            + REC4[2] * S4[m - 3]
            + REC4[3] * S4[m - 4]
            + REC4[4] * S4[m - 5]
        )
        if lhs != rhs:
            raise AssertionError(f"[A4.search] recurrence failed at m={m}")

    # Build a_n := S4(n+2), n=0.. need at least 2d terms (d=5 => a_0..a_9).
    d = 5
    a = [S4[n + 2] for n in range(0, 12)]
    A, alpha, beta = build_hankel_shift_realization(a, d=d)

    prog.tick("start unimodular similarity search")
    A4, P, cost = search_nonnegative_similarity(A, steps=int(args.steps), seed=int(args.seed), prog=prog)

    payload: Dict[str, object] = {
        "d": d,
        "recurrence_coeffs": REC4,
        "S4_initial_enum": {str(m): int(S4[m]) for m in range(2, args.m_enum_max + 1)},
        "A_hankel": A,
        "alpha_hankel": alpha,
        "beta_hankel": beta,
        "A4_candidate": A4,
        "P_unimodular": P,
        "cost": cost,
        "steps": int(args.steps),
        "seed": int(args.seed),
    }

    if not args.no_output:
        out = export_dir() / "collision_kernel_A4_search.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"[A4.search] wrote {out}", flush=True)

    print(f"[A4.search] best_cost={cost}", flush=True)
    print("[A4.search] Hankel A:", flush=True)
    for row in A:
        print(" ", row, flush=True)
    print("[A4.search] A4 candidate:", flush=True)
    for row in A4:
        print(" ", row, flush=True)


if __name__ == "__main__":
    main()

