#!/usr/bin/env python3
"""Finite consistency checks for the A5 same-W certificate.

This verifies only the finite group and linear algebra assertions used in the
certificate. It does not certify the geometric existence of a concrete cover,
the de Rham H^1 vanishing, spreadout, or the E-G theorem match.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import permutations


Perm = tuple[int, int, int, int, int]
Matrix = list[list[Fraction]]


def inversion_parity(p: Perm) -> int:
    return sum(1 for i in range(5) for j in range(i + 1, 5) if p[i] > p[j]) % 2


def a5() -> list[Perm]:
    return [tuple(p) for p in permutations(range(5)) if inversion_parity(tuple(p)) == 0]


def permutation_matrix(p: Perm) -> Matrix:
    matrix = [[Fraction(0) for _ in range(5)] for _ in range(5)]
    for j, image in enumerate(p):
        matrix[image][j] = Fraction(1)
    return matrix


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def mat_sub(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_rank(a: Matrix) -> int:
    rows = [row[:] for row in a]
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [x / scale for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                factor = rows[r][col]
                rows[r] = [rows[r][c] - factor * rows[rank][c] for c in range(len(rows[0]))]
        rank += 1
    return rank


def determinant(a: Matrix) -> Fraction:
    rows = [row[:] for row in a]
    det = Fraction(1)
    for col in range(len(rows)):
        pivot = next((r for r in range(col, len(rows)) if rows[r][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            rows[col], rows[pivot] = rows[pivot], rows[col]
            det *= -1
        pivot_value = rows[col][col]
        det *= pivot_value
        for r in range(col + 1, len(rows)):
            if rows[r][col]:
                factor = rows[r][col] / pivot_value
                rows[r] = [rows[r][c] - factor * rows[col][c] for c in range(len(rows))]
    return det


def standard_idempotent() -> Matrix:
    identity = [[Fraction(int(i == j)) for j in range(5)] for i in range(5)]
    all_ones_over_5 = [[Fraction(1, 5) for _ in range(5)] for _ in range(5)]
    return mat_sub(identity, all_ones_over_5)


def restrict_to_sum_zero(p: Perm) -> Matrix:
    # Coordinates in the basis e_i - e_4, i=0..3, of the sum-zero representation.
    images: list[list[Fraction]] = []
    for i in range(4):
        vector = [Fraction(0) for _ in range(5)]
        vector[p[i]] += 1
        vector[p[4]] -= 1
        images.append(vector[:4])
    return [[images[col][row] for col in range(4)] for row in range(4)]


def standard_character(p: Perm) -> int:
    return sum(1 for i, image in enumerate(p) if i == image) - 1


def main() -> int:
    group = a5()
    assert len(group) == 60, len(group)

    e = standard_idempotent()
    assert mat_mul(e, e) == e
    assert mat_rank(e) == 4
    assert all(mat_mul(permutation_matrix(g), e) == mat_mul(e, permutation_matrix(g)) for g in group)
    assert all(sum(e[i][j] for j in range(5)) == 0 for i in range(5))

    character_inner_product = sum(standard_character(g) ** 2 for g in group) / len(group)
    assert character_inner_product == 1
    assert {determinant(restrict_to_sum_zero(g)) for g in group} == {Fraction(1)}

    print("PASS_A5_SAME_W_CERTIFICATE_CONSISTENCY")
    print("A5_order=60")
    print("idempotent=e=I-J/5")
    print("idempotent_rank=4")
    print("idempotent_commutes_with_A5=True")
    print("standard_character_inner_product=1")
    print("standard_representation_determinant_values=[1]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
