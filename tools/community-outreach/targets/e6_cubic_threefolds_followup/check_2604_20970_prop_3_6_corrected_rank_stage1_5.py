#!/usr/bin/env python3
"""Stage-1.5 exact verifier for arXiv:2604.20970, Proposition 3.6.

This checks the corrected map from Section 3.3:

    nu: Sym^2(R_3) -> Hom(Lambda^2(R_1), Lambda^2(R_4))
    nu(f*g)(phi wedge psi) = f*phi wedge g*psi + g*phi wedge f*psi

for the Fermat Jacobian ring R = Q[x_0,...,x_4]/(x_0^2,...,x_4^2).
Only Python's standard library is used, and all rank computation is exact over Q.
"""

from __future__ import annotations

from fractions import Fraction
import datetime as _datetime
import hashlib
import itertools
import json
import os
import time
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


PAPER = "arXiv:2604.20970"
PROPOSITION = "3.6"
CLAIM = "rank(nu) = 50"
VARIABLE_COUNT = 5
PROGRESS_INTERVAL_SECONDS = 20.0
OUTPUT_NAME = "check_2604_20970_prop_3_6_corrected_rank_stage1_5_output.json"

Monomial = frozenset[int]
Matrix = List[List[Fraction]]
BasisPair = Tuple[int, int]

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


def build_nu_matrix() -> Tuple[
    Matrix,
    List[Monomial],
    List[Monomial],
    List[Monomial],
    List[BasisPair],
    List[BasisPair],
    List[BasisPair],
]:
    r1_basis = [frozenset({i}) for i in range(VARIABLE_COUNT)]
    r3_basis = subsets_of_degree(3)
    r4_basis = subsets_of_degree(4)

    sym2_r3 = sym2_basis_indices(len(r3_basis))
    lam2_r1 = wedge_basis_pairs(len(r1_basis))
    lam2_r4 = wedge_basis_pairs(len(r4_basis))

    r4_index = {monomial: index for index, monomial in enumerate(r4_basis)}
    lam2_r4_index = {pair: index for index, pair in enumerate(lam2_r4)}

    matrix: Matrix = []
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

    return matrix, r1_basis, r3_basis, r4_basis, sym2_r3, lam2_r1, lam2_r4


def rank_over_q(matrix: Sequence[Sequence[Fraction]]) -> int:
    """Compute exact row rank over Q by Gaussian elimination."""
    if not matrix:
        return 0
    row_count = len(matrix)
    col_count = len(matrix[0])
    work = [list(row) for row in matrix]
    pivot_row = 0

    for col in range(col_count):
        progress(f"Gaussian elimination: column {col + 1}/{col_count}, pivots={pivot_row}")
        pivot = None
        for row in range(pivot_row, row_count):
            if work[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue

        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        pivot_value = work[pivot_row][col]
        work[pivot_row] = [entry / pivot_value for entry in work[pivot_row]]

        for row in range(row_count):
            if row == pivot_row or work[row][col] == 0:
                continue
            factor = work[row][col]
            work[row] = [
                entry - factor * pivot_entry
                for entry, pivot_entry in zip(work[row], work[pivot_row])
            ]

        pivot_row += 1
        if pivot_row == row_count:
            break

    return pivot_row


def matrix_sha256(matrix: Sequence[Sequence[Fraction]]) -> str:
    canonical = [[str(entry) for entry in row] for row in matrix]
    return hashlib.sha256(repr(canonical).encode()).hexdigest()


def write_output(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def main() -> int:
    progress("Starting Stage-1.5 corrected rank verifier", force=True)
    (
        matrix,
        r1_basis,
        r3_basis,
        r4_basis,
        sym2_r3,
        lam2_r1,
        lam2_r4,
    ) = build_nu_matrix()

    progress("Computing exact rank over Q", force=True)
    computed_rank = rank_over_q(matrix)
    digest = matrix_sha256(matrix)
    matches_claim = computed_rank == 50
    verdict = "PASS_RANK_50" if matches_claim else f"FAIL_RANK_{computed_rank}"

    output: Dict[str, object] = {
        "paper": PAPER,
        "proposition": PROPOSITION,
        "claim": CLAIM,
        "field_of_computation": "Q",
        "source_dim_Sym2_R3": len(sym2_r3),
        "target_dim_Hom_Lam2R1_Lam2R4": len(lam2_r4) * len(lam2_r1),
        "matrix_rows": len(matrix),
        "matrix_cols": len(matrix[0]) if matrix else 0,
        "computed_rank": computed_rank,
        "matches_paper_claim": matches_claim,
        "matrix_sha256": digest,
        "verdict": verdict,
        "notes": [
            "Monomials are frozenset[int] and multiply to zero on overlapping variables.",
            "R_3 and R_4 bases use lexicographic itertools.combinations order.",
            "Sym^2(R_3) basis uses unordered index pairs f_index <= g_index.",
            "Lambda^2 bases use ordered index pairs i < j with standard antisymmetric sign.",
            "Hom coordinates are flattened by k = i_out * dim(Lambda^2 R_1) + j_in.",
        ],
        "basis_dimensions": {
            "R1": len(r1_basis),
            "R3": len(r3_basis),
            "R4": len(r4_basis),
            "Lambda2_R1": len(lam2_r1),
            "Lambda2_R4": len(lam2_r4),
        },
    }

    output_path = write_output(output)
    print(f"VERDICT: {verdict}", flush=True)
    print(f"JSON: {output_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
