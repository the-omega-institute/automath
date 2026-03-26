#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: binary-necklace trace expansion for replica-softcore T^(q).

This script is English-only by repository convention.

It certifies, for a small grid of (m,q), the exact identities recorded in
Conclusions:
  - Tr((T^(q))^m) = 2^{-m} * sum_{omega in {0,1}^m} tau(omega)^q
    with the necklace reduction sum_{necklaces} |orb| * tau^q, and
  - 2^m S_m(q) = Omega_m(q) + sum_{necklaces != 0^m} |orb| * tau^q
    where Omega_m(q) = Tr(B_q^m) and B_q(i,j)=binom(q-j,i).

The audit uses only integer arithmetic by working with the scaled matrices:
  - B^(q) = 2 T^(q)  (entries in {1,2}), so Tr((B^(q))^m) = 2^m Tr((T^(q))^m).
  - A2^(q) = 2 A^(q) (integer), so Tr((A2^(q))^m) = 2^m S_m(q).
"""

from __future__ import annotations

import json
from collections import Counter
from math import comb
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent
OUT = (
    ROOT
    / "artifacts"
    / "export"
    / "replica_softcore_binary_necklace_trace_audit.json"
)


def fib_list(max_n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_max_n with F_0=0, F_1=1."""
    if max_n < 0:
        raise ValueError("max_n must be >= 0")
    F = [0] * (max_n + 1)
    if max_n >= 0:
        F[0] = 0
    if max_n >= 1:
        F[1] = 1
    for i in range(2, max_n + 1):
        F[i] = F[i - 1] + F[i - 2]
    return F


def lucas_from_fib(F: Sequence[int], n: int) -> int:
    """Lucas L_n from Fibonacci table with F_0=0, F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return 2
    if n == 1:
        return 1
    # L_n = F_{n-1} + F_{n+1}
    return F[n - 1] + F[n + 1]


def rot_left_bits(w: int, m: int, shift: int) -> int:
    """Rotate the m-bit word w left by shift positions."""
    if m <= 0:
        raise ValueError("m must be >= 1")
    mask = (1 << m) - 1
    shift %= m
    if shift == 0:
        return w & mask
    return ((w << shift) & mask) | ((w & mask) >> (m - shift))


def rotations(w: int, m: int) -> List[int]:
    """All cyclic rotations of w (as m-bit word)."""
    return [rot_left_bits(w, m, s) for s in range(m)]


def necklace_representatives(m: int) -> Dict[int, int]:
    """Return {rep: orbit_size} for binary necklaces of length m."""
    reps: Dict[int, int] = {}
    for w in range(1 << m):
        rep = min(rotations(w, m))
        if rep in reps:
            continue
        reps[rep] = len(set(rotations(rep, m)))
    return reps


Mat2 = Tuple[Tuple[int, int], Tuple[int, int]]


def mat2_mul(A: Mat2, B: Mat2) -> Mat2:
    return (
        (
            A[0][0] * B[0][0] + A[0][1] * B[1][0],
            A[0][0] * B[0][1] + A[0][1] * B[1][1],
        ),
        (
            A[1][0] * B[0][0] + A[1][1] * B[1][0],
            A[1][0] * B[0][1] + A[1][1] * B[1][1],
        ),
    )


def mat2_trace(A: Mat2) -> int:
    return A[0][0] + A[1][1]


J2: Mat2 = ((1, 1), (1, 1))
K2: Mat2 = ((1, 1), (1, 0))
I2: Mat2 = ((1, 0), (0, 1))


def tau_by_matrix(word: int, m: int) -> int:
    """tau(word) = Tr(prod_t A_{bit_t}) with A_0=K, A_1=J."""
    M = I2
    for t in range(m):
        bit = (word >> t) & 1
        M = mat2_mul(M, J2 if bit else K2)
    return mat2_trace(M)


def tau_by_blocks(word: int, m: int, F: Sequence[int]) -> int:
    """Compute tau from the zero-block decomposition between 1s."""
    bits = [((word >> t) & 1) for t in range(m)]
    ones = [i for i, b in enumerate(bits) if b == 1]
    if not ones:
        return lucas_from_fib(F, m)

    s = len(ones)
    prod = 1
    for idx in range(s):
        a = ones[idx]
        b = ones[(idx + 1) % s]
        if idx == s - 1:
            b += m
        r = b - a - 1
        prod *= F[r + 3]
    return prod


def identity(n: int) -> List[List[int]]:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def matmul(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    if n == 0 or len(B) != n or any(len(row) != n for row in A) or any(len(row) != n for row in B):
        raise ValueError("matmul expects two square matrices of same size")

    B_cols = list(zip(*B))
    C = [[0] * n for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for j in range(n):
            s = 0
            Bj = B_cols[j]
            for k in range(n):
                s += Ai[k] * Bj[k]
            C[i][j] = s
    return C


def trace(A: List[List[int]]) -> int:
    return sum(A[i][i] for i in range(len(A)))


def build_B_scaled(q: int) -> List[List[int]]:
    """B^(q) = 2 T^(q) on U_q, indexed by bitmasks u,v in {0,1}^q."""
    n = 1 << q
    M = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            M[u][v] = 2 if (u & v) == 0 else 1
    return M


def build_A2(q: int) -> List[List[int]]:
    """A2^(q) = 2 A^(q) on the S_q-symmetric subspace (size q+1)."""
    M = [[0] * (q + 1) for _ in range(q + 1)]
    for k in range(q + 1):
        for l in range(q + 1):
            M[k][l] = comb(q, l) + (comb(q - k, l) if 0 <= l <= q - k else 0)
    return M


def build_Bq(q: int) -> List[List[int]]:
    """Binomial matrix B_q(i,j)=binom(q-j,i) (size q+1)."""
    M = [[0] * (q + 1) for _ in range(q + 1)]
    for i in range(q + 1):
        for j in range(q + 1):
            n = q - j
            M[i][j] = comb(n, i) if 0 <= i <= n else 0
    return M


def precompute_necklace_data(m_values: Iterable[int]) -> Dict[int, List[Dict[str, int]]]:
    data: Dict[int, List[Dict[str, int]]] = {}
    for m in m_values:
        F = fib_list(m + 3 + 2)
        reps = necklace_representatives(m)
        rows: List[Dict[str, int]] = []
        for rep, orb in sorted(reps.items()):
            tau_mx = tau_by_matrix(rep, m)
            tau_blk = tau_by_blocks(rep, m, F)
            if tau_mx != tau_blk:
                raise RuntimeError(
                    f"tau mismatch: m={m} rep={rep} tau_matrix={tau_mx} tau_blocks={tau_blk}"
                )
            rows.append({"rep": rep, "orb": orb, "tau": tau_mx})
        data[m] = rows
    return data


def word_tau_counts_excluding_all_zero(m: int) -> Dict[int, int]:
    """Return {tau: count} over all m-bit words excluding the all-zero word."""
    counts: Counter[int] = Counter()
    for w in range(1 << m):
        counts[tau_by_matrix(w, m)] += 1

    lucas = tau_by_matrix(0, m)
    counts[lucas] -= 1
    if counts[lucas] == 0:
        del counts[lucas]
    if any(v < 0 for v in counts.values()):
        raise RuntimeError("negative tau count encountered")
    return dict(counts)


def main() -> None:
    q_values = list(range(2, 7))
    m_values = list(range(1, 9))

    necklace_data = precompute_necklace_data(m_values)

    expected_coeffs: Dict[int, Dict[int, int]] = {
        # 2^m S_m(q) = Omega_m(q) + sum_{t} coeff[t] * t^q
        6: {
            64: 1,
            48: 6,
            40: 6,
            36: 9,
            32: 6,
            30: 12,
            27: 2,
            26: 6,
            25: 3,
            24: 6,
            21: 6,
        },
        7: {
            128: 1,
            96: 7,
            80: 7,
            72: 14,
            64: 7,
            60: 21,
            54: 7,
            52: 7,
            50: 7,
            48: 14,
            45: 7,
            42: 7,
            40: 7,
            39: 7,
            34: 7,
        },
        8: {
            256: 1,
            192: 8,
            160: 8,
            144: 20,
            128: 8,
            120: 32,
            108: 16,
            104: 8,
            100: 12,
            96: 24,
            90: 24,
            84: 8,
            81: 2,
            80: 16,
            78: 16,
            75: 8,
            72: 8,
            68: 8,
            65: 8,
            64: 4,
            63: 8,
            55: 8,
        },
    }

    tau_value_counts: Dict[int, Dict[int, int]] = {}
    for m, coeffs in expected_coeffs.items():
        observed = word_tau_counts_excluding_all_zero(m)
        if observed != coeffs:
            raise RuntimeError(
                f"Unexpected (tau -> count) distribution for m={m}. "
                f"observed={sorted(observed.items(), reverse=True)} "
                f"expected={sorted(coeffs.items(), reverse=True)}"
            )
        if sum(observed.values()) != (1 << m) - 1:
            raise RuntimeError(f"Count sum mismatch for m={m}")
        tau_value_counts[m] = dict(sorted(observed.items(), reverse=True))

    checks: List[Dict[str, int]] = []
    for q in q_values:
        B_scaled = build_B_scaled(q)
        A2 = build_A2(q)
        Bq = build_Bq(q)

        pow_B = identity(len(B_scaled))
        pow_A2 = identity(len(A2))
        pow_Bq = identity(len(Bq))

        for m in m_values:
            pow_B = matmul(pow_B, B_scaled)
            pow_A2 = matmul(pow_A2, A2)
            pow_Bq = matmul(pow_Bq, Bq)

            lhs_full = trace(pow_B)  # = 2^m Tr((T^(q))^m)
            lhs_exc = trace(pow_A2)  # = 2^m S_m(q)
            omega = trace(pow_Bq)  # = Omega_m(q) = Tr(B_q^m)

            neck_total = 0
            neck_nonzero = 0
            for row in necklace_data[m]:
                term = row["orb"] * pow(row["tau"], q)
                neck_total += term
                if row["rep"] != 0:
                    neck_nonzero += term

            rhs_full = neck_total
            rhs_exc = omega + neck_nonzero

            if lhs_full != rhs_full:
                raise RuntimeError(
                    f"Full trace mismatch at (q,m)=({q},{m}): lhs={lhs_full} rhs={rhs_full}"
                )
            if lhs_exc != rhs_exc:
                raise RuntimeError(
                    f"Exceptional sum mismatch at (q,m)=({q},{m}): lhs={lhs_exc} rhs={rhs_exc}"
                )

            if m in expected_coeffs:
                rhs_exc_closed = omega + sum(c * pow(t, q) for t, c in expected_coeffs[m].items())
                if lhs_exc != rhs_exc_closed:
                    raise RuntimeError(
                        f"Closed form mismatch at (q,m)=({q},{m}): lhs={lhs_exc} rhs={rhs_exc_closed}"
                    )

            checks.append(
                {
                    "q": q,
                    "m": m,
                    "lhs_full": lhs_full,
                    "rhs_full": rhs_full,
                    "lhs_exc": lhs_exc,
                    "rhs_exc": rhs_exc,
                    "omega": omega,
                }
            )

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(
            {
                "q_values": q_values,
                "m_values": m_values,
                "checks": checks,
                "tau_value_counts_excluding_all_zero": tau_value_counts,
                "notes": {
                    "lhs_full": "Tr((2T^(q))^m) = 2^m Tr((T^(q))^m)",
                    "lhs_exc": "Tr((2A^(q))^m) = 2^m S_m(q)",
                    "omega": "Tr((B_q)^m) with B_q(i,j)=binom(q-j,i)",
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"File: {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

