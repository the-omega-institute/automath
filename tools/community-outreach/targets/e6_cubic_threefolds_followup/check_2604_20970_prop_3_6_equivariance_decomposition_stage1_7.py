#!/usr/bin/env python3
"""Stage-1.7 S_5-equivariant isotypic verifier for arXiv:2604.20970, Prop. 3.6.

This rebuilds the Stage-1.5 matrix

    nu: Sym^2(R_3) -> Hom(Lambda^2(R_1), Lambda^2(R_4))
    nu(f*g)(phi wedge psi) = f*phi wedge g*psi + g*phi wedge f*psi

for the Fermat Jacobian ring R = Q[x_0,...,x_4]/(x_0^2,...,x_4^2), checks the
historical Stage-1.6 Q-matrix anchor, verifies S_5 equivariance, and decomposes
the source Sym^2(R_3) into S_5 isotypic summands.  Only Python's standard
library is used, and all linear algebra is exact over Q.
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
PROPOSITION = "3.6 equivariance decomposition"
VARIABLE_COUNT = 5
GROUP_ORDER = 120
PROGRESS_INTERVAL_SECONDS = 20.0
EXPECTED_MATRIX_SHA256_Q = "309e752d6a25641e0d5f0b1655cbc029af59154547d76b9fedef1085131b343e"
OUTPUT_NAME = "check_2604_20970_prop_3_6_equivariance_decomposition_stage1_7_output.json"

Monomial = frozenset[int]
BasisPair = Tuple[int, int]
Permutation = Tuple[int, ...]
SignedMap = List[Tuple[int, int]]
Matrix = List[List[Fraction]]

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
    """Build the exact Stage-1.5 55 x 100 row matrix with the same basis order."""
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


def matrix_sha256_q_anchor(matrix: Sequence[Sequence[Fraction]]) -> str:
    """Historical Stage-1.5/1.6 Q anchor serialization."""
    canonical = [[str(entry) for entry in row] for row in matrix]
    return hashlib.sha256(repr(canonical).encode()).hexdigest()


def matrix_sha256_q_numden_json(matrix: Sequence[Sequence[Fraction]]) -> str:
    """Canonical JSON serialization with entries as [numerator, denominator]."""
    canonical = [
        [[entry.numerator, entry.denominator] for entry in row]
        for row in matrix
    ]
    return hashlib.sha256(json.dumps(canonical, separators=(",", ":")).encode()).hexdigest()


def write_output(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[Fraction(0) for _ in range(cols)] for _ in range(rows)]


def identity_matrix(size: int) -> Matrix:
    matrix = zero_matrix(size, size)
    for i in range(size):
        matrix[i][i] = Fraction(1)
    return matrix


def transpose(matrix: Sequence[Sequence[Fraction]]) -> Matrix:
    if not matrix:
        return []
    return [[matrix[row][col] for row in range(len(matrix))] for col in range(len(matrix[0]))]


def matmul(left: Sequence[Sequence[Fraction]], right: Sequence[Sequence[Fraction]]) -> Matrix:
    if not left or not right:
        return []
    rows = len(left)
    inner = len(right)
    cols = len(right[0])
    product = zero_matrix(rows, cols)
    for i in range(rows):
        for k in range(inner):
            factor = left[i][k]
            if factor == 0:
                continue
            right_row = right[k]
            for j in range(cols):
                if right_row[j]:
                    product[i][j] += factor * right_row[j]
    return product


def signed_map_to_matrix(signed_map: SignedMap) -> Matrix:
    size = len(signed_map)
    matrix = zero_matrix(size, size)
    for col, (row, sign) in enumerate(signed_map):
        matrix[row][col] = Fraction(sign)
    return matrix


def rank_over_q(matrix: Sequence[Sequence[Fraction]], label: str = "Q elimination") -> int:
    """Compute exact row rank over Q by Gaussian elimination."""
    if not matrix:
        return 0
    row_count = len(matrix)
    col_count = len(matrix[0])
    work = [list(row) for row in matrix]
    pivot_row = 0

    for col in range(col_count):
        progress(f"{label}: column {col + 1}/{col_count}, pivots={pivot_row}")
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


def pivot_columns_for_column_space(matrix: Sequence[Sequence[Fraction]], label: str) -> List[int]:
    """Return pivot columns from RREF, hence independent original columns."""
    if not matrix:
        return []
    row_count = len(matrix)
    col_count = len(matrix[0])
    work = [list(row) for row in matrix]
    pivot_row = 0
    pivots: List[int] = []

    for col in range(col_count):
        progress(f"{label}: RREF column {col + 1}/{col_count}, pivots={pivot_row}")
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

        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break

    return pivots


def columns_matrix(matrix: Sequence[Sequence[Fraction]], columns: Sequence[int]) -> Matrix:
    return [[row[col] for col in columns] for row in matrix]


def all_permutations() -> List[Permutation]:
    return list(itertools.permutations(range(VARIABLE_COUNT)))


def inverse_permutation(perm: Permutation) -> Permutation:
    inverse = [0] * len(perm)
    for i, image in enumerate(perm):
        inverse[image] = i
    return tuple(inverse)


def cycle_type(perm: Permutation) -> str:
    seen = [False] * len(perm)
    lengths: List[int] = []
    for start in range(len(perm)):
        if seen[start]:
            continue
        length = 0
        current = start
        while not seen[current]:
            seen[current] = True
            length += 1
            current = perm[current]
        lengths.append(length)
    lengths.sort(reverse=True)
    if lengths == [1, 1, 1, 1, 1]:
        return "1^5"
    if lengths == [2, 1, 1, 1]:
        return "2.1^3"
    if lengths == [2, 2, 1]:
        return "2^2.1"
    if lengths == [3, 1, 1]:
        return "3.1^2"
    if lengths == [3, 2]:
        return "3.2"
    if lengths == [4, 1]:
        return "4.1"
    if lengths == [5]:
        return "5"
    raise ValueError(f"Unexpected cycle lengths: {lengths}")


def apply_permutation_to_monomial(perm: Permutation, monomial: Monomial) -> Monomial:
    return frozenset(perm[i] for i in monomial)


def permutation_signed_map_on_basis(perm: Permutation, basis: Sequence[Monomial]) -> SignedMap:
    index = {monomial: i for i, monomial in enumerate(basis)}
    return [
        (index[apply_permutation_to_monomial(perm, monomial)], 1)
        for monomial in basis
    ]


def wedge_signed_map(base_map: SignedMap, wedge_basis: Sequence[BasisPair]) -> SignedMap:
    wedge_index = {pair: i for i, pair in enumerate(wedge_basis)}
    result: SignedMap = []
    for i, j in wedge_basis:
        image_i, sign_i = base_map[i]
        image_j, sign_j = base_map[j]
        sign = sign_i * sign_j
        if image_i < image_j:
            result.append((wedge_index[(image_i, image_j)], sign))
        else:
            result.append((wedge_index[(image_j, image_i)], -sign))
    return result


def sym2_signed_map(base_map: SignedMap, sym2_basis: Sequence[BasisPair]) -> SignedMap:
    sym2_index = {pair: i for i, pair in enumerate(sym2_basis)}
    result: SignedMap = []
    for i, j in sym2_basis:
        image_i, sign_i = base_map[i]
        image_j, sign_j = base_map[j]
        if image_i <= image_j:
            pair = (image_i, image_j)
        else:
            pair = (image_j, image_i)
        result.append((sym2_index[pair], sign_i * sign_j))
    return result


def hom_signed_map(output_map: SignedMap, input_map: SignedMap, input_dim: int) -> SignedMap:
    """Signed map for Hom(input, output): T -> rho_out T rho_in^{-1}.

    Hom basis is flattened as (output_index, input_index) -> output_index * input_dim + input_index,
    matching the Stage-1.5 matrix target-coordinate convention.
    """
    result: SignedMap = []
    for out_index, (out_image, out_sign) in enumerate(output_map):
        for in_index, (in_image, in_sign) in enumerate(input_map):
            old_flat = out_index * input_dim + in_index
            assert old_flat == len(result)
            new_flat = out_image * input_dim + in_image
            result.append((new_flat, out_sign * in_sign))
    return result


def trace_from_signed_map(signed_map: SignedMap) -> int:
    trace = 0
    for col, (row, sign) in enumerate(signed_map):
        if row == col:
            trace += sign
    return trace


def representative_permutations() -> Dict[str, Permutation]:
    return {
        "(12)": (1, 0, 2, 3, 4),
        "(12345)": (1, 2, 3, 4, 0),
    }


def class_representatives() -> Dict[str, Permutation]:
    return {
        "1^5": (0, 1, 2, 3, 4),
        "2.1^3": (1, 0, 2, 3, 4),
        "2^2.1": (1, 0, 3, 2, 4),
        "3.1^2": (1, 2, 0, 3, 4),
        "3.2": (1, 2, 0, 4, 3),
        "4.1": (1, 2, 3, 0, 4),
        "5": (1, 2, 3, 4, 0),
    }


PARTITION_LABELS = [
    "[5]",
    "[4,1]",
    "[3,2]",
    "[3,1,1]",
    "[2,2,1]",
    "[2,1,1,1]",
    "[1,1,1,1,1]",
]

CLASS_LABELS = ["1^5", "2.1^3", "2^2.1", "3.1^2", "3.2", "4.1", "5"]

CLASS_SIZES = {
    "1^5": 1,
    "2.1^3": 10,
    "2^2.1": 15,
    "3.1^2": 20,
    "3.2": 20,
    "4.1": 30,
    "5": 24,
}

CHARACTER_TABLE = {
    "[5]": {
        "1^5": 1,
        "2.1^3": 1,
        "2^2.1": 1,
        "3.1^2": 1,
        "3.2": 1,
        "4.1": 1,
        "5": 1,
    },
    "[4,1]": {
        "1^5": 4,
        "2.1^3": 2,
        "2^2.1": 0,
        "3.1^2": 1,
        "3.2": -1,
        "4.1": 0,
        "5": -1,
    },
    "[3,2]": {
        "1^5": 5,
        "2.1^3": 1,
        "2^2.1": 1,
        "3.1^2": -1,
        "3.2": 1,
        "4.1": -1,
        "5": 0,
    },
    "[3,1,1]": {
        "1^5": 6,
        "2.1^3": 0,
        "2^2.1": -2,
        "3.1^2": 0,
        "3.2": 0,
        "4.1": 0,
        "5": 1,
    },
    "[2,2,1]": {
        "1^5": 5,
        "2.1^3": -1,
        "2^2.1": 1,
        "3.1^2": -1,
        "3.2": -1,
        "4.1": 1,
        "5": 0,
    },
    "[2,1,1,1]": {
        "1^5": 4,
        "2.1^3": -2,
        "2^2.1": 0,
        "3.1^2": 1,
        "3.2": 1,
        "4.1": 0,
        "5": -1,
    },
    "[1,1,1,1,1]": {
        "1^5": 1,
        "2.1^3": -1,
        "2^2.1": 1,
        "3.1^2": 1,
        "3.2": -1,
        "4.1": -1,
        "5": 1,
    },
}


def compute_sym2_character(
    reps: Dict[str, Permutation],
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> Dict[str, int]:
    character: Dict[str, int] = {}
    for class_label, perm in reps.items():
        r3_map = permutation_signed_map_on_basis(perm, r3_basis)
        sym2_map = sym2_signed_map(r3_map, sym2_r3)
        character[class_label] = trace_from_signed_map(sym2_map)
    return character


def decompose_character(source_character: Dict[str, int]) -> Dict[str, int]:
    multiplicities: Dict[str, int] = {}
    for partition in PARTITION_LABELS:
        numerator = sum(
            CLASS_SIZES[class_label]
            * source_character[class_label]
            * CHARACTER_TABLE[partition][class_label]
            for class_label in CLASS_LABELS
        )
        if numerator % GROUP_ORDER != 0:
            raise ArithmeticError(f"Nonintegral multiplicity for {partition}: {numerator}/{GROUP_ORDER}")
        multiplicities[partition] = numerator // GROUP_ORDER
    return multiplicities


def build_source_projector(
    partition: str,
    group: Sequence[Permutation],
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> Matrix:
    dim_irrep = CHARACTER_TABLE[partition]["1^5"]
    factor = Fraction(dim_irrep, GROUP_ORDER)
    size = len(sym2_r3)
    projector = zero_matrix(size, size)

    for index, perm in enumerate(group):
        progress(f"Building projector {partition}: group element {index + 1}/{len(group)}")
        inv = inverse_permutation(perm)
        class_label = cycle_type(perm)
        coefficient = factor * CHARACTER_TABLE[partition][class_label]
        if coefficient == 0:
            continue
        r3_map = permutation_signed_map_on_basis(inv, r3_basis)
        sym2_map = sym2_signed_map(r3_map, sym2_r3)
        for col, (row, sign) in enumerate(sym2_map):
            projector[row][col] += coefficient * sign

    return projector


def is_idempotent(projector: Matrix) -> bool:
    return matmul(projector, projector) == projector


def verify_equivariance_for_perm(
    perm: Permutation,
    nu_column_matrix: Matrix,
    r1_basis: Sequence[Monomial],
    r3_basis: Sequence[Monomial],
    r4_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
    lam2_r1: Sequence[BasisPair],
    lam2_r4: Sequence[BasisPair],
) -> bool:
    r1_map = permutation_signed_map_on_basis(perm, r1_basis)
    r3_map = permutation_signed_map_on_basis(perm, r3_basis)
    r4_map = permutation_signed_map_on_basis(perm, r4_basis)
    source_map = sym2_signed_map(r3_map, sym2_r3)
    input_map = wedge_signed_map(r1_map, lam2_r1)
    output_map = wedge_signed_map(r4_map, lam2_r4)
    target_map = hom_signed_map(output_map, input_map, len(lam2_r1))

    source_matrix = signed_map_to_matrix(source_map)
    target_matrix = signed_map_to_matrix(target_map)

    left = matmul(nu_column_matrix, source_matrix)
    right = matmul(target_matrix, nu_column_matrix)
    return left == right


def zero_result(anchor_matches: bool, recomputed_sha: str, verdict: str) -> Dict[str, object]:
    empty_by_partition = {label: 0 for label in PARTITION_LABELS}
    return {
        "paper": PAPER,
        "proposition": PROPOSITION,
        "matrix_sha256_Q_anchor": EXPECTED_MATRIX_SHA256_Q,
        "matrix_sha256_Q_recomputed": recomputed_sha,
        "anchor_matches": anchor_matches,
        "S5_action_on_M_nu_equivariant": False,
        "S5_equivariance_per_generator": {"(12)": False, "(12345)": False},
        "Sym2_R3_decomposition": dict(empty_by_partition),
        "Sym2_R3_total_dim_check": 0,
        "per_isotypic_dim": dict(empty_by_partition),
        "per_isotypic_rank": dict(empty_by_partition),
        "per_isotypic_kernel_dim": dict(empty_by_partition),
        "total_rank_from_isotypics": 0,
        "total_kernel_dim_from_isotypics": 0,
        "matches_50": False,
        "kernel_carriers": [],
        "verdict": verdict,
    }


def main() -> int:
    progress("Starting Stage-1.7 S_5 equivariance/isotypic verifier", force=True)
    (
        matrix_rows_source,
        r1_basis,
        r3_basis,
        r4_basis,
        sym2_r3,
        lam2_r1,
        lam2_r4,
    ) = build_nu_matrix()

    progress("Checking Stage-1.6 Q matrix anchor", force=True)
    matrix_sha256_q_recomputed = matrix_sha256_q_anchor(matrix_rows_source)
    anchor_matches = matrix_sha256_q_recomputed == EXPECTED_MATRIX_SHA256_Q
    if not anchor_matches:
        verdict = "FAIL_ANCHOR_MISMATCH"
        output = zero_result(anchor_matches, matrix_sha256_q_recomputed, verdict)
        output_path = write_output(output)
        print(f"VERDICT: {verdict}", flush=True)
        print(f"JSON: {output_path}", flush=True)
        print("commit: no commit; anchor mismatch", flush=True)
        print(
            "key numbers: "
            f"anchor_matches={anchor_matches}, equivariant=False, "
            "per_isotypic_rank={}, total_rank=0, kernel_carriers=[]",
            flush=True,
        )
        return 1

    requested_numden_json_sha = matrix_sha256_q_numden_json(matrix_rows_source)
    print(f"matrix_sha256_Q_anchor_compatible = {matrix_sha256_q_recomputed}", flush=True)
    print(f"matrix_sha256_Q_numden_json = {requested_numden_json_sha}", flush=True)

    progress("Verifying S_5 equivariance on generators", force=True)
    nu_column_matrix = transpose(matrix_rows_source)
    equivariance_per_generator: Dict[str, bool] = {}
    for name, perm in representative_permutations().items():
        passed = verify_equivariance_for_perm(
            perm,
            nu_column_matrix,
            r1_basis,
            r3_basis,
            r4_basis,
            sym2_r3,
            lam2_r1,
            lam2_r4,
        )
        equivariance_per_generator[name] = passed
        print(f"equivariance {name}: {passed}", flush=True)

    progress("Verifying S_5 equivariance on all 120 elements", force=True)
    all_equivariant = True
    failed_elements: List[str] = []
    for index, perm in enumerate(all_permutations()):
        progress(f"Checking equivariance for S_5 element {index + 1}/120")
        passed = verify_equivariance_for_perm(
            perm,
            nu_column_matrix,
            r1_basis,
            r3_basis,
            r4_basis,
            sym2_r3,
            lam2_r1,
            lam2_r4,
        )
        if not passed:
            all_equivariant = False
            failed_elements.append(str(perm))

    progress("Computing character of Sym^2(R_3)", force=True)
    sym2_character = compute_sym2_character(class_representatives(), r3_basis, sym2_r3)
    multiplicities = decompose_character(sym2_character)
    total_dim_check = sum(
        multiplicities[label] * CHARACTER_TABLE[label]["1^5"]
        for label in PARTITION_LABELS
    )
    print(f"Sym2_R3_character = {sym2_character}", flush=True)
    print(f"Sym2_R3_decomposition = {multiplicities}", flush=True)

    per_isotypic_dim = {label: 0 for label in PARTITION_LABELS}
    per_isotypic_rank = {label: 0 for label in PARTITION_LABELS}
    per_isotypic_kernel_dim = {label: 0 for label in PARTITION_LABELS}
    projector_idempotency_failures: List[str] = []
    group = all_permutations()

    for label in PARTITION_LABELS:
        multiplicity = multiplicities[label]
        if multiplicity <= 0:
            continue
        progress(f"Processing isotypic component {label}", force=True)
        projector = build_source_projector(label, group, r3_basis, sym2_r3)
        if not is_idempotent(projector):
            projector_idempotency_failures.append(label)
            print(f"projector idempotency {label}: False", flush=True)
        else:
            print(f"projector idempotency {label}: True", flush=True)

        pivot_columns = pivot_columns_for_column_space(projector, f"Projector {label}")
        basis_matrix = columns_matrix(projector, pivot_columns)
        dim_isotypic = len(pivot_columns)
        restricted = matmul(nu_column_matrix, basis_matrix)
        rank = rank_over_q(restricted, label=f"Restricted rank {label}")
        kernel_dim = dim_isotypic - rank

        per_isotypic_dim[label] = dim_isotypic
        per_isotypic_rank[label] = rank
        per_isotypic_kernel_dim[label] = kernel_dim
        print(
            f"isotypic {label}: dim={dim_isotypic}, rank={rank}, kernel_dim={kernel_dim}",
            flush=True,
        )

    total_rank = sum(per_isotypic_rank.values())
    total_kernel_dim = sum(per_isotypic_kernel_dim.values())
    kernel_carriers = [
        label for label in PARTITION_LABELS
        if per_isotypic_kernel_dim[label] > 0
    ]
    matches_50 = total_rank == 50

    if not all_equivariant:
        verdict = "FAIL_EQUIVARIANCE"
        if failed_elements:
            print(f"Failed equivariance elements: {failed_elements}", flush=True)
    elif projector_idempotency_failures:
        verdict = "PARTIAL_PROJECTOR_IDEMPOTENCY"
        print(f"Projector idempotency failures: {projector_idempotency_failures}", flush=True)
    elif not matches_50:
        verdict = "PARTIAL_RANK_SUM_NOT_50"
    elif total_kernel_dim != 5:
        verdict = "PARTIAL_KERNEL_DIM_NOT_5"
    else:
        verdict = "PASS_EQUIVARIANCE_RANK_50"

    output: Dict[str, object] = {
        "paper": PAPER,
        "proposition": PROPOSITION,
        "matrix_sha256_Q_anchor": EXPECTED_MATRIX_SHA256_Q,
        "matrix_sha256_Q_recomputed": matrix_sha256_q_recomputed,
        "anchor_matches": anchor_matches,
        "S5_action_on_M_nu_equivariant": all_equivariant,
        "S5_equivariance_per_generator": equivariance_per_generator,
        "Sym2_R3_decomposition": multiplicities,
        "Sym2_R3_total_dim_check": total_dim_check,
        "per_isotypic_dim": per_isotypic_dim,
        "per_isotypic_rank": per_isotypic_rank,
        "per_isotypic_kernel_dim": per_isotypic_kernel_dim,
        "total_rank_from_isotypics": total_rank,
        "total_kernel_dim_from_isotypics": total_kernel_dim,
        "matches_50": matches_50,
        "kernel_carriers": kernel_carriers,
        "verdict": verdict,
    }
    output_path = write_output(output)

    print(f"VERDICT: {verdict}", flush=True)
    print(f"JSON: {output_path}", flush=True)
    print("commit: pending workflow decision", flush=True)
    print(
        "key numbers: "
        f"anchor_matches={anchor_matches}, equivariant={all_equivariant}, "
        f"per_isotypic_rank={per_isotypic_rank}, total_rank={total_rank}, "
        f"kernel_carriers={kernel_carriers}",
        flush=True,
    )
    return 0 if verdict.startswith("PASS") else 1


if __name__ == "__main__":
    raise SystemExit(main())
