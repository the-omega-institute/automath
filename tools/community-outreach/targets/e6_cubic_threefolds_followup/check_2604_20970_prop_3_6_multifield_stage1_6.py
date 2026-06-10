#!/usr/bin/env python3
"""Stage-1.6 multifield verifier for arXiv:2604.20970, Proposition 3.6.

This rebuilds the Stage-1.5 matrix

    nu: Sym^2(R_3) -> Hom(Lambda^2(R_1), Lambda^2(R_4))
    nu(f*g)(phi wedge psi) = f*phi wedge g*psi + g*phi wedge f*psi

for the Fermat Jacobian ring R = Q[x_0,...,x_4]/(x_0^2,...,x_4^2), then checks
its rank over several finite fields.  Only Python's standard library is used.
"""

from __future__ import annotations

from fractions import Fraction
import datetime as _datetime
import hashlib
import itertools
import json
import os
import time
from typing import Dict, List, Optional, Sequence, Tuple


PAPER = "arXiv:2604.20970"
PROPOSITION = "3.6 multifield extension"
VARIABLE_COUNT = 5
PROGRESS_INTERVAL_SECONDS = 20.0
PRIMES_TESTED = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
EXPECTED_MATRIX_SHA256_Q = "309e752d6a25641e0d5f0b1655cbc029af59154547d76b9fedef1085131b343e"
OUTPUT_NAME = "check_2604_20970_prop_3_6_multifield_stage1_6_output.json"

Monomial = frozenset[int]
BasisPair = Tuple[int, int]
MatrixQ = List[List[Fraction]]
MatrixFp = List[List[int]]

_LAST_PROGRESS = 0.0


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    """Emit progress at least every 20 seconds during longer runs."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        _LAST_PROGRESS = now


def subsets_of_degree(degree: int) -> List[Monomial]:
    return [
        frozenset(combo)
        for combo in itertools.combinations(range(VARIABLE_COUNT), degree)
    ]


def multiply(left: Monomial, right: Monomial) -> Optional[Monomial]:
    """Squarefree multiplication: overlapping variables produce zero."""
    if left.intersection(right):
        return None
    return left.union(right)


def wedge_basis_pairs(size: int) -> List[BasisPair]:
    return [(i, j) for i in range(size) for j in range(i + 1, size)]


def sym2_basis_indices(size: int) -> List[BasisPair]:
    return [(i, j) for i in range(size) for j in range(i, size)]


def wedge_coordinate(
    left: Optional[Monomial],
    right: Optional[Monomial],
    r4_index: Dict[Monomial, int],
    lam2_r4_index: Dict[BasisPair, int],
) -> List[Fraction]:
    """Return coordinates of left wedge right in Lambda^2(R_4)."""
    coords = [Fraction(0) for _ in range(len(lam2_r4_index))]
    if left is None or right is None or left == right:
        return coords

    a = r4_index[left]
    b = r4_index[right]
    if a < b:
        coords[lam2_r4_index[(a, b)]] = Fraction(1)
    else:
        coords[lam2_r4_index[(b, a)]] = Fraction(-1)
    return coords


def add_vectors(left: Sequence[Fraction], right: Sequence[Fraction]) -> List[Fraction]:
    return [a + b for a, b in zip(left, right)]


def build_nu_matrix() -> MatrixQ:
    r1_basis = [frozenset({i}) for i in range(VARIABLE_COUNT)]
    r3_basis = subsets_of_degree(3)
    r4_basis = subsets_of_degree(4)

    sym2_r3 = sym2_basis_indices(len(r3_basis))
    lam2_r1 = wedge_basis_pairs(len(r1_basis))
    lam2_r4 = wedge_basis_pairs(len(r4_basis))

    r4_index = {monomial: index for index, monomial in enumerate(r4_basis)}
    lam2_r4_index = {pair: index for index, pair in enumerate(lam2_r4)}

    matrix: MatrixQ = []
    total_rows = len(sym2_r3)
    for row_index, (f_index, g_index) in enumerate(sym2_r3):
        progress(f"Building nu matrix row {row_index + 1}/{total_rows}")
        f = r3_basis[f_index]
        g = r3_basis[g_index]
        row = [Fraction(0) for _ in range(len(lam2_r4) * len(lam2_r1))]

        for j_in, (phi_index, psi_index) in enumerate(lam2_r1):
            phi = r1_basis[phi_index]
            psi = r1_basis[psi_index]

            f_phi = multiply(f, phi)
            g_psi = multiply(g, psi)
            g_phi = multiply(g, phi)
            f_psi = multiply(f, psi)

            first = wedge_coordinate(f_phi, g_psi, r4_index, lam2_r4_index)
            second = wedge_coordinate(g_phi, f_psi, r4_index, lam2_r4_index)
            image_coords = add_vectors(first, second)

            for i_out, coefficient in enumerate(image_coords):
                if coefficient:
                    column = i_out * len(lam2_r1) + j_in
                    row[column] = coefficient

        matrix.append(row)

    return matrix


def matrix_sha256_q(matrix: Sequence[Sequence[Fraction]]) -> str:
    canonical = [[str(entry) for entry in row] for row in matrix]
    return hashlib.sha256(repr(canonical).encode()).hexdigest()


def reduce_matrix_mod_p(matrix: Sequence[Sequence[Fraction]], p: int) -> MatrixFp:
    reduced: MatrixFp = []
    for row in matrix:
        reduced_row = []
        for entry in row:
            numerator = entry.numerator % p
            denominator = entry.denominator % p
            if denominator == 0:
                raise ZeroDivisionError(f"Cannot reduce denominator {entry.denominator} modulo {p}")
            reduced_row.append((numerator * pow(denominator, p - 2, p)) % p)
        reduced.append(reduced_row)
    return reduced


def matrix_sha256_mod_p(matrix_mod_p: Sequence[Sequence[int]]) -> str:
    canonical_json = json.dumps(matrix_mod_p, separators=(",", ":"))
    return hashlib.sha256(canonical_json.encode()).hexdigest()


def rank_over_fp(matrix_mod_p: Sequence[Sequence[int]], p: int) -> int:
    """Compute row rank over F_p by Gaussian elimination."""
    if not matrix_mod_p:
        return 0

    row_count = len(matrix_mod_p)
    col_count = len(matrix_mod_p[0])
    work = [list(row) for row in matrix_mod_p]
    pivot_row = 0

    for col in range(col_count):
        progress(f"F_{p} elimination: column {col + 1}/{col_count}, pivots={pivot_row}")
        pivot = None
        for row in range(pivot_row, row_count):
            if work[row][col] % p:
                pivot = row
                break
        if pivot is None:
            continue

        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = pow(work[pivot_row][col] % p, p - 2, p)
        work[pivot_row] = [(entry * inverse) % p for entry in work[pivot_row]]

        for row in range(row_count):
            if row == pivot_row:
                continue
            factor = work[row][col] % p
            if factor == 0:
                continue
            work[row] = [
                (entry - factor * pivot_entry) % p
                for entry, pivot_entry in zip(work[row], work[pivot_row])
            ]

        pivot_row += 1
        if pivot_row == row_count:
            break

    return pivot_row


def decide_verdict(
    matrix_sha256_q_recomputed: str,
    rank_per_prime: Dict[str, int],
) -> str:
    if matrix_sha256_q_recomputed != EXPECTED_MATRIX_SHA256_Q:
        return "FAIL"
    if all(rank == 50 for rank in rank_per_prime.values()):
        return "PASS_ALL_PRIMES_50"
    if all(rank_per_prime[str(p)] == 50 for p in PRIMES_TESTED if p >= 5):
        return "PASS_LARGE_PRIMES_50"
    return "FAIL"


def write_output(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def main() -> int:
    progress("Starting Stage-1.6 multifield verifier", force=True)
    matrix = build_nu_matrix()

    progress("Recomputing Stage-1.5 Q matrix sha256", force=True)
    matrix_sha256_q_recomputed = matrix_sha256_q(matrix)

    rank_per_prime: Dict[str, int] = {}
    matrix_sha256_per_prime: Dict[str, str] = {}

    for p in PRIMES_TESTED:
        progress(f"Reducing matrix modulo {p}", force=True)
        matrix_mod_p = reduce_matrix_mod_p(matrix, p)
        matrix_sha256_per_prime[str(p)] = matrix_sha256_mod_p(matrix_mod_p)

        progress(f"Computing rank over F_{p}", force=True)
        rank = rank_over_fp(matrix_mod_p, p)
        rank_per_prime[str(p)] = rank
        print(f"rank_F_{p}(M_nu) = {rank}", flush=True)

    primes_with_smaller_rank = [
        p for p in PRIMES_TESTED
        if rank_per_prime[str(p)] < 50
    ]
    primes_with_rank_50 = [
        p for p in PRIMES_TESTED
        if rank_per_prime[str(p)] == 50
    ]
    all_primes_rank_50 = len(primes_with_rank_50) == len(PRIMES_TESTED)
    verdict = decide_verdict(matrix_sha256_q_recomputed, rank_per_prime)

    output: Dict[str, object] = {
        "paper": PAPER,
        "proposition": PROPOSITION,
        "primes_tested": PRIMES_TESTED,
        "rank_per_prime": rank_per_prime,
        "all_primes_rank_50": all_primes_rank_50,
        "primes_with_smaller_rank": primes_with_smaller_rank,
        "primes_with_rank_50": primes_with_rank_50,
        "matrix_sha256_Q": EXPECTED_MATRIX_SHA256_Q,
        "matrix_sha256_Q_recomputed": matrix_sha256_q_recomputed,
        "matrix_sha256_per_prime": matrix_sha256_per_prime,
        "verdict": verdict,
    }

    output_path = write_output(output)
    print(f"Q hash expected:   {EXPECTED_MATRIX_SHA256_Q}", flush=True)
    print(f"Q hash recomputed: {matrix_sha256_q_recomputed}", flush=True)
    print(f"VERDICT: {verdict}", flush=True)
    print(f"JSON: {output_path}", flush=True)
    return 0 if verdict != "FAIL" else 1


if __name__ == "__main__":
    raise SystemExit(main())
