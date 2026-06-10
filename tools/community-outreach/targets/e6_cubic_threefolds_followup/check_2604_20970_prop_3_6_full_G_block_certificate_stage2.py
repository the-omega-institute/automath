#!/usr/bin/env python3
"""Stage-2 full G block certificate for arXiv:2604.20970, Proposition 3.6.

This refines the Stage-1.5 exact matrix

    nu: Sym^2(R_3) -> Hom(Lambda^2(R_1), Lambda^2(R_4))
    nu(f*g)(phi wedge psi) = f*phi wedge g*psi + g*phi wedge f*psi

for the Fermat Jacobian ring R = Q[x_0,...,x_4]/(x_0^2,...,x_4^2) by the full
diagonal-by-permutation symmetry G = S_5 semidirect (mu_3)^5.  Only Python's
standard library is used, and all Q-linear algebra is exact with Fraction.
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
PROPOSITION = "3.6 full G block certificate Stage-2"
G_STRUCTURE = "S_5 \u22c9 (\u03bc_3)^5"
VARIABLE_COUNT = 5
PROGRESS_INTERVAL_SECONDS = 20.0
EXPECTED_MATRIX_SHA256_Q = "309e752d6a25641e0d5f0b1655cbc029af59154547d76b9fedef1085131b343e"
OUTPUT_NAME = "check_2604_20970_prop_3_6_full_G_block_certificate_stage2_output.json"

Monomial = frozenset[int]
BasisPair = Tuple[int, int]
Character = Tuple[int, int, int, int, int]
Permutation = Tuple[int, ...]
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


def build_nu_matrix() -> Tuple[
    MatrixQ,
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

    return matrix, r1_basis, r3_basis, r4_basis, sym2_r3, lam2_r1, lam2_r4


def transpose(matrix: Sequence[Sequence[Fraction]]) -> MatrixQ:
    if not matrix:
        return []
    return [[matrix[row][col] for row in range(len(matrix))] for col in range(len(matrix[0]))]


def matrix_sha256_q(matrix: Sequence[Sequence[Fraction]]) -> str:
    canonical = [[str(entry) for entry in row] for row in matrix]
    return hashlib.sha256(repr(canonical).encode()).hexdigest()


def monomial_character(monomial: Monomial) -> Character:
    return tuple(1 if i in monomial else 0 for i in range(VARIABLE_COUNT))  # type: ignore[return-value]


def add_characters(*characters: Character) -> Character:
    return tuple(
        sum(character[i] for character in characters) % 3
        for i in range(VARIABLE_COUNT)
    )  # type: ignore[return-value]


def sub_characters(left: Character, right: Character) -> Character:
    return tuple((left[i] - right[i]) % 3 for i in range(VARIABLE_COUNT))  # type: ignore[return-value]


def source_character(
    source_index: int,
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> Character:
    f_index, g_index = sym2_r3[source_index]
    return add_characters(
        monomial_character(r3_basis[f_index]),
        monomial_character(r3_basis[g_index]),
    )


def target_character(
    target_index: int,
    r1_basis: Sequence[Monomial],
    r4_basis: Sequence[Monomial],
    lam2_r1: Sequence[BasisPair],
    lam2_r4: Sequence[BasisPair],
) -> Character:
    """Return the diagonal character of a Hom(Lambda^2 R_1, Lambda^2 R_4) basis vector."""
    input_dim = len(lam2_r1)
    out_index, in_index = divmod(target_index, input_dim)
    out_left_index, out_right_index = lam2_r4[out_index]
    in_left_index, in_right_index = lam2_r1[in_index]

    output_char = add_characters(
        monomial_character(r4_basis[out_left_index]),
        monomial_character(r4_basis[out_right_index]),
    )
    input_char = add_characters(
        monomial_character(r1_basis[in_left_index]),
        monomial_character(r1_basis[in_right_index]),
    )
    return sub_characters(output_char, input_char)


def intersection_size_for_source(
    source_index: int,
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> int:
    f_index, g_index = sym2_r3[source_index]
    return len(r3_basis[f_index].intersection(r3_basis[g_index]))


def character_key(character: Character) -> str:
    return "".join(str(entry) for entry in character)


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


def rank_over_fp(matrix_mod_p: Sequence[Sequence[int]], p: int, label: str = "Fp elimination") -> int:
    """Compute exact row rank over F_p by Gaussian elimination."""
    if not matrix_mod_p:
        return 0
    row_count = len(matrix_mod_p)
    col_count = len(matrix_mod_p[0])
    work = [list(row) for row in matrix_mod_p]
    pivot_row = 0

    for col in range(col_count):
        progress(f"{label}: column {col + 1}/{col_count}, pivots={pivot_row}")
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


def submatrix_q(
    matrix: Sequence[Sequence[Fraction]],
    rows: Sequence[int],
    columns: Sequence[int],
) -> MatrixQ:
    return [[matrix[row][col] for col in columns] for row in rows]


def submatrix_fp(
    matrix: Sequence[Sequence[int]],
    rows: Sequence[int],
    columns: Sequence[int],
) -> MatrixFp:
    return [[matrix[row][col] for col in columns] for row in rows]


def matvec_source_to_target(
    matrix_rows_source: Sequence[Sequence[Fraction]],
    vector: Sequence[Fraction],
) -> List[Fraction]:
    if not matrix_rows_source:
        return []
    target_dim = len(matrix_rows_source[0])
    result = [Fraction(0) for _ in range(target_dim)]
    for source_index, coefficient in enumerate(vector):
        if coefficient == 0:
            continue
        row = matrix_rows_source[source_index]
        for target_index, entry in enumerate(row):
            if entry:
                result[target_index] += coefficient * entry
    return result


def build_kernel_generators(
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> List[List[Fraction]]:
    r3_index = {monomial: index for index, monomial in enumerate(r3_basis)}
    sym2_index = {pair: index for index, pair in enumerate(sym2_r3)}
    generators: List[List[Fraction]] = []

    for a in range(VARIABLE_COUNT):
        vector = [Fraction(0) for _ in range(len(sym2_r3))]
        complement = [i for i in range(VARIABLE_COUNT) if i != a]
        seen_partitions = set()
        for p_tuple in itertools.combinations(complement, 2):
            p_set = frozenset(p_tuple)
            q_set = frozenset(i for i in complement if i not in p_set)
            partition_key = tuple(sorted([tuple(sorted(p_set)), tuple(sorted(q_set))]))
            if partition_key in seen_partitions:
                continue
            seen_partitions.add(partition_key)

            left = frozenset({a}).union(p_set)
            right = frozenset({a}).union(q_set)
            left_index = r3_index[left]
            right_index = r3_index[right]
            pair = (left_index, right_index) if left_index <= right_index else (right_index, left_index)
            vector[sym2_index[pair]] += Fraction(1)
        generators.append(vector)

    return generators


def fraction_vector_to_ints(vector: Sequence[Fraction]) -> List[int]:
    ints: List[int] = []
    for entry in vector:
        if entry.denominator != 1:
            raise ArithmeticError(f"Nonintegral kernel-generator entry: {entry}")
        ints.append(entry.numerator)
    return ints


def apply_permutation_to_monomial(perm: Permutation, monomial: Monomial) -> Monomial:
    return frozenset(perm[i] for i in monomial)


def source_permutation_map(
    perm: Permutation,
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> List[int]:
    r3_index = {monomial: index for index, monomial in enumerate(r3_basis)}
    sym2_index = {pair: index for index, pair in enumerate(sym2_r3)}
    result: List[int] = []
    for f_index, g_index in sym2_r3:
        f_image = r3_index[apply_permutation_to_monomial(perm, r3_basis[f_index])]
        g_image = r3_index[apply_permutation_to_monomial(perm, r3_basis[g_index])]
        pair = (f_image, g_image) if f_image <= g_image else (g_image, f_image)
        result.append(sym2_index[pair])
    return result


def apply_source_permutation_to_vector(
    source_map: Sequence[int],
    vector: Sequence[Fraction],
) -> List[Fraction]:
    image = [Fraction(0) for _ in range(len(vector))]
    for old_index, new_index in enumerate(source_map):
        image[new_index] += vector[old_index]
    return image


def partition_sources_by_character(
    r3_basis: Sequence[Monomial],
    sym2_r3: Sequence[BasisPair],
) -> Dict[Character, List[int]]:
    by_character: Dict[Character, List[int]] = {}
    for source_index in range(len(sym2_r3)):
        character = source_character(source_index, r3_basis, sym2_r3)
        by_character.setdefault(character, []).append(source_index)
    return by_character


def partition_targets_by_character(
    r1_basis: Sequence[Monomial],
    r4_basis: Sequence[Monomial],
    lam2_r1: Sequence[BasisPair],
    lam2_r4: Sequence[BasisPair],
) -> Dict[Character, List[int]]:
    target_dim = len(lam2_r1) * len(lam2_r4)
    by_character: Dict[Character, List[int]] = {}
    for target_index in range(target_dim):
        character = target_character(target_index, r1_basis, r4_basis, lam2_r1, lam2_r4)
        by_character.setdefault(character, []).append(target_index)
    return by_character


def verify_character_preservation(
    matrix_rows_source: Sequence[Sequence[Fraction]],
    source_characters: Sequence[Character],
    target_characters: Sequence[Character],
) -> Tuple[bool, List[Dict[str, object]]]:
    violations: List[Dict[str, object]] = []
    for source_index, row in enumerate(matrix_rows_source):
        for target_index, entry in enumerate(row):
            if entry and source_characters[source_index] != target_characters[target_index]:
                violations.append(
                    {
                        "source_index": source_index,
                        "target_index": target_index,
                        "entry": str(entry),
                        "source_character": source_characters[source_index],
                        "target_character": target_characters[target_index],
                    }
                )
    return len(violations) == 0, violations


def expected_block_table() -> Dict[str, Dict[str, int]]:
    return {
        "|I\u2229J|=3": {
            "chars": 10,
            "dim_D": 1,
            "dim_T": 1,
            "rank": 1,
            "total_contribution_to_rank": 10,
        },
        "|I\u2229J|=2": {
            "chars": 30,
            "dim_D": 1,
            "dim_T": 2,
            "rank": 1,
            "total_contribution_to_rank": 30,
        },
        "|I\u2229J|=1": {
            "chars": 5,
            "dim_D": 3,
            "dim_T": 6,
            "rank": 2,
            "total_contribution_to_rank": 10,
        },
    }


def write_output(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def main() -> int:
    progress("Starting Stage-2 full G block certificate", force=True)
    (
        matrix_rows_source,
        r1_basis,
        r3_basis,
        r4_basis,
        sym2_r3,
        lam2_r1,
        lam2_r4,
    ) = build_nu_matrix()
    matrix_target_by_source = transpose(matrix_rows_source)

    progress("Checking Stage-1.5 matrix anchor and diagonal character preservation", force=True)
    matrix_sha256_q_recomputed = matrix_sha256_q(matrix_rows_source)
    anchor_matches = matrix_sha256_q_recomputed == EXPECTED_MATRIX_SHA256_Q

    source_characters = [
        source_character(source_index, r3_basis, sym2_r3)
        for source_index in range(len(sym2_r3))
    ]
    target_characters = [
        target_character(target_index, r1_basis, r4_basis, lam2_r1, lam2_r4)
        for target_index in range(len(lam2_r1) * len(lam2_r4))
    ]
    character_preserved, character_violations = verify_character_preservation(
        matrix_rows_source,
        source_characters,
        target_characters,
    )

    progress("Partitioning source and target by diagonal characters", force=True)
    source_by_character = partition_sources_by_character(r3_basis, sym2_r3)
    target_by_character = partition_targets_by_character(r1_basis, r4_basis, lam2_r1, lam2_r4)

    character_partition_counts = {
        1: 0,
        2: 0,
        3: 0,
    }
    source_character_intersections: Dict[Character, int] = {}
    partition_shape_ok = True
    for character, source_indices in source_by_character.items():
        intersection_sizes = {
            intersection_size_for_source(source_index, r3_basis, sym2_r3)
            for source_index in source_indices
        }
        if len(intersection_sizes) != 1:
            partition_shape_ok = False
            continue
        intersection_size = next(iter(intersection_sizes))
        source_character_intersections[character] = intersection_size
        character_partition_counts[intersection_size] += 1
        expected_dim = 3 if intersection_size == 1 else 1
        if len(source_indices) != expected_dim:
            partition_shape_ok = False

    character_partition_verified = (
        partition_shape_ok
        and character_partition_counts == {3: 10, 2: 30, 1: 5}
        and sum(len(indices) for indices in source_by_character.values()) == 55
    )

    progress("Computing exact Q block ranks", force=True)
    block_details: Dict[str, Dict[str, object]] = {}
    grouped_block_summaries: Dict[int, Dict[str, object]] = {
        3: {"chars": 0, "dim_D_values": set(), "dim_T_values": set(), "rank_values": set(), "rank_sum": 0},
        2: {"chars": 0, "dim_D_values": set(), "dim_T_values": set(), "rank_values": set(), "rank_sum": 0},
        1: {"chars": 0, "dim_D_values": set(), "dim_T_values": set(), "rank_values": set(), "rank_sum": 0},
    }

    total_block_rank_q = 0
    for character in sorted(source_by_character, key=character_key):
        source_indices = source_by_character[character]
        target_indices = target_by_character.get(character, [])
        block = submatrix_q(matrix_target_by_source, target_indices, source_indices)
        rank = rank_over_q(block, label=f"Q block {character_key(character)}")
        total_block_rank_q += rank

        intersection_size = source_character_intersections.get(character, -1)
        summary = grouped_block_summaries[intersection_size]
        summary["chars"] = int(summary["chars"]) + 1
        summary["dim_D_values"].add(len(source_indices))  # type: ignore[union-attr]
        summary["dim_T_values"].add(len(target_indices))  # type: ignore[union-attr]
        summary["rank_values"].add(rank)  # type: ignore[union-attr]
        summary["rank_sum"] = int(summary["rank_sum"]) + rank
        block_details[character_key(character)] = {
            "character": list(character),
            "intersection_size": intersection_size,
            "dim_D": len(source_indices),
            "dim_T": len(target_indices),
            "rank_Q": rank,
            "source_indices": source_indices,
            "target_indices": target_indices,
        }

    computed_block_table: Dict[str, Dict[str, int]] = {}
    for intersection_size in (3, 2, 1):
        label = f"|I\u2229J|={intersection_size}"
        summary = grouped_block_summaries[intersection_size]
        dim_d_values = summary["dim_D_values"]
        dim_t_values = summary["dim_T_values"]
        rank_values = summary["rank_values"]
        computed_block_table[label] = {
            "chars": int(summary["chars"]),
            "dim_D": next(iter(dim_d_values)) if len(dim_d_values) == 1 else -1,  # type: ignore[arg-type]
            "dim_T": next(iter(dim_t_values)) if len(dim_t_values) == 1 else -1,  # type: ignore[arg-type]
            "rank": next(iter(rank_values)) if len(rank_values) == 1 else -1,  # type: ignore[arg-type]
            "total_contribution_to_rank": int(summary["rank_sum"]),
        }

    expected_table = expected_block_table()
    block_table_matches_prediction = computed_block_table == expected_table

    progress("Checking explicit kernel generators k_a", force=True)
    kernel_generators = build_kernel_generators(r3_basis, sym2_r3)
    all_k_a_in_kernel = all(
        all(entry == 0 for entry in matvec_source_to_target(matrix_rows_source, generator))
        for generator in kernel_generators
    )
    kernel_generator_rank = rank_over_q(kernel_generators, label="k_a independence")
    full_matrix_rank_q = rank_over_q(matrix_rows_source, label="Full Q rank")
    kernel_dimension_q = len(sym2_r3) - full_matrix_rank_q
    k_a_span_full_kernel = (
        kernel_generator_rank == VARIABLE_COUNT
        and kernel_dimension_q == VARIABLE_COUNT
        and all_k_a_in_kernel
    )

    progress("Checking S_5 transposition action on k_a", force=True)
    transposition_01: Permutation = (1, 0, 2, 3, 4)
    source_map_01 = source_permutation_map(transposition_01, r3_basis, sym2_r3)
    s5_action_on_kernel = True
    s5_kernel_action: Dict[str, int] = {}
    for a, generator in enumerate(kernel_generators):
        image = apply_source_permutation_to_vector(source_map_01, generator)
        expected_index = transposition_01[a]
        s5_kernel_action[str(a)] = expected_index
        if image != kernel_generators[expected_index]:
            s5_action_on_kernel = False

    progress("Checking characteristic-2 rank drop anchor", force=True)
    matrix_mod_2_rows_source = reduce_matrix_mod_p(matrix_rows_source, 2)
    matrix_mod_2_target_by_source = [
        [matrix_mod_2_rows_source[source][target] for source in range(len(sym2_r3))]
        for target in range(len(lam2_r1) * len(lam2_r4))
    ]
    mod_2_full_rank = rank_over_fp(matrix_mod_2_rows_source, 2, label="F_2 full rank")
    mod_2_cap3_rows_zero = True
    mod_2_cap3_block_ranks: Dict[str, int] = {}
    for character, source_indices in source_by_character.items():
        if source_character_intersections[character] != 3:
            continue
        source_index = source_indices[0]
        if any(entry % 2 for entry in matrix_mod_2_rows_source[source_index]):
            mod_2_cap3_rows_zero = False
        target_indices = target_by_character.get(character, [])
        block_mod_2 = submatrix_fp(matrix_mod_2_target_by_source, target_indices, source_indices)
        mod_2_cap3_block_ranks[character_key(character)] = rank_over_fp(
            block_mod_2,
            2,
            label=f"F_2 cap3 block {character_key(character)}",
        )

    mod_2_cap3_blocks_rank_zero = all(rank == 0 for rank in mod_2_cap3_block_ranks.values())
    mod_2_block_rank_drop_explained = (
        mod_2_full_rank == 40
        and mod_2_cap3_rows_zero
        and mod_2_cap3_blocks_rank_zero
        and len(mod_2_cap3_block_ranks) == 10
    )

    all_items_pass = (
        anchor_matches
        and character_preserved
        and character_partition_verified
        and block_table_matches_prediction
        and total_block_rank_q == 50
        and full_matrix_rank_q == 50
        and all_k_a_in_kernel
        and k_a_span_full_kernel
        and s5_action_on_kernel
        and mod_2_block_rank_drop_explained
    )
    if all_items_pass:
        verdict = "PASS_FULL_G_BLOCK_CERTIFICATE"
    elif not anchor_matches:
        verdict = "FAIL"
    elif not character_preserved:
        verdict = "PARTIAL_CHARACTER_PRESERVATION"
    elif not block_table_matches_prediction:
        verdict = "PARTIAL_BLOCK_TABLE_MISMATCH"
    elif total_block_rank_q != 50 or full_matrix_rank_q != 50:
        verdict = "PARTIAL_RANK_NOT_50"
    elif not k_a_span_full_kernel:
        verdict = "PARTIAL_KERNEL_SPAN"
    elif not s5_action_on_kernel:
        verdict = "PARTIAL_S5_KERNEL_ACTION"
    elif not mod_2_block_rank_drop_explained:
        verdict = "PARTIAL_MOD2_ANCHOR"
    else:
        verdict = "FAIL"

    output: Dict[str, object] = {
        "paper": PAPER,
        "proposition": PROPOSITION,
        "G_structure": G_STRUCTURE,
        "character_partition_verified": character_partition_verified,
        "block_table": computed_block_table,
        "total_block_rank_Q": total_block_rank_q,
        "kernel_generators_k_a": [
            fraction_vector_to_ints(generator)
            for generator in kernel_generators
        ],
        "all_k_a_in_kernel": all_k_a_in_kernel,
        "k_a_span_full_kernel": k_a_span_full_kernel,
        "S_5_acts_on_k_a_by_permutation": s5_action_on_kernel,
        "mod_2_block_rank_drop_explained": mod_2_block_rank_drop_explained,
        "verdict": verdict,
        "diagnostics": {
            "matrix_sha256_Q_anchor": EXPECTED_MATRIX_SHA256_Q,
            "matrix_sha256_Q_recomputed": matrix_sha256_q_recomputed,
            "anchor_matches": anchor_matches,
            "source_dim_Sym2_R3": len(sym2_r3),
            "target_dim_Hom_Lam2R1_Lam2R4": len(lam2_r1) * len(lam2_r4),
            "character_preservation_verified": character_preserved,
            "character_preservation_violation_count": len(character_violations),
            "first_character_preservation_violations": character_violations[:5],
            "source_character_count": len(source_by_character),
            "target_character_count": len(target_by_character),
            "source_character_partition_counts": {
                str(key): value for key, value in sorted(character_partition_counts.items())
            },
            "block_table_matches_prediction": block_table_matches_prediction,
            "block_details": block_details,
            "full_matrix_rank_Q": full_matrix_rank_q,
            "kernel_dimension_Q": kernel_dimension_q,
            "kernel_generator_rank_Q": kernel_generator_rank,
            "S5_generator": "(12)",
            "S5_kernel_action": s5_kernel_action,
            "mod_2_full_rank": mod_2_full_rank,
            "mod_2_cap3_rows_zero": mod_2_cap3_rows_zero,
            "mod_2_cap3_block_ranks": mod_2_cap3_block_ranks,
        },
    }

    output_path = write_output(output)
    print(f"VERDICT: {verdict}", flush=True)
    print(f"JSON: {output_path}", flush=True)
    print(
        "key numbers: "
        f"anchor_matches={anchor_matches}, character_preserved={character_preserved}, "
        f"block_table={computed_block_table}, total_block_rank_Q={total_block_rank_q}, "
        f"rank_Q={full_matrix_rank_q}, kernel_rank={kernel_generator_rank}, "
        f"rank_F_2={mod_2_full_rank}",
        flush=True,
    )
    return 0 if verdict == "PASS_FULL_G_BLOCK_CERTIFICATE" else 1


if __name__ == "__main__":
    raise SystemExit(main())
