#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the multiplicity bulk/defect matrix package for window-6.

All output is English-only by repository convention.

This script certifies the exact algebraic package behind the window-6
multiplicity/Coxeter conclusions:
  - the Weyl stabilizer size of the decorated B3 root data,
  - the long-layer generated algebra and commutant dimensions,
  - the cubic central relation on the long block,
  - the short-block nilpotent defect ranks,
  - the characteristic/minimal polynomial package for the cyclic commutator.

Outputs:
  - artifacts/export/window6_multiplicity_bulk_defect_audit.json
  - sections/generated/eq_window6_multiplicity_bulk_defect_audit.tex
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from common_paths import export_dir, generated_dir


Matrix = List[List[int]]


def eye(n: int) -> Matrix:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def zeros(m: int, n: int) -> Matrix:
    return [[0 for _ in range(n)] for _ in range(m)]


def mat_add(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_sub(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_scale(c: int, a: Matrix) -> Matrix:
    return [[c * a[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    m = len(a)
    n = len(b[0])
    kdim = len(b)
    out = zeros(m, n)
    for i in range(m):
        for k in range(kdim):
            aik = a[i][k]
            if aik == 0:
                continue
            for j in range(n):
                out[i][j] += aik * b[k][j]
    return out


def mat_pow(a: Matrix, k: int) -> Matrix:
    n = len(a)
    out = eye(n)
    base = [row[:] for row in a]
    exp = k
    while exp > 0:
        if exp & 1:
            out = mat_mul(out, base)
        base = mat_mul(base, base)
        exp >>= 1
    return out


def kron(a: Matrix, b: Matrix) -> Matrix:
    ma, na = len(a), len(a[0])
    mb, nb = len(b), len(b[0])
    out = zeros(ma * mb, na * nb)
    for i in range(ma):
        for j in range(na):
            aij = a[i][j]
            if aij == 0:
                continue
            for r in range(mb):
                for s in range(nb):
                    out[i * mb + r][j * nb + s] = aij * b[r][s]
    return out


def block_diag(*blocks: Matrix) -> Matrix:
    rows = sum(len(b) for b in blocks)
    cols = sum(len(b[0]) for b in blocks)
    out = zeros(rows, cols)
    r0 = 0
    c0 = 0
    for b in blocks:
        for i in range(len(b)):
            for j in range(len(b[0])):
                out[r0 + i][c0 + j] = b[i][j]
        r0 += len(b)
        c0 += len(b[0])
    return out


def trace(a: Matrix) -> int:
    return sum(a[i][i] for i in range(len(a)))


def is_zero(a: Matrix) -> bool:
    return all(x == 0 for row in a for x in row)


def flatten(a: Matrix) -> List[int]:
    return [x for row in a for x in row]


def rank_of_rows(rows: Sequence[Sequence[int | Fraction]]) -> int:
    if not rows:
        return 0
    mat = [[Fraction(x) for x in row] for row in rows]
    m = len(mat)
    n = len(mat[0])
    r = 0
    c = 0
    while r < m and c < n:
        pivot = None
        for i in range(r, m):
            if mat[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            c += 1
            continue
        mat[r], mat[pivot] = mat[pivot], mat[r]
        piv = mat[r][c]
        for j in range(c, n):
            mat[r][j] /= piv
        for i in range(m):
            if i == r or mat[i][c] == 0:
                continue
            fac = mat[i][c]
            for j in range(c, n):
                mat[i][j] -= fac * mat[r][j]
        r += 1
        c += 1
    return r


def matrix_rank(a: Matrix) -> int:
    return rank_of_rows(a)


def span_dimension(mats: Iterable[Matrix]) -> int:
    return rank_of_rows([flatten(m) for m in mats])


def generated_algebra_dimension(generators: Sequence[Matrix]) -> int:
    n = len(generators[0])
    basis: List[Matrix] = [eye(n)]
    queue: List[Matrix] = [eye(n)]
    gens = list(generators)
    while queue:
        x = queue.pop(0)
        for g in gens:
            y = mat_mul(x, g)
            if span_dimension(basis + [y]) > len(basis):
                basis.append(y)
                queue.append(y)
    return len(basis)


def commutant_dimension(generators: Sequence[Matrix]) -> int:
    n = len(generators[0])
    num_vars = n * n
    equations: List[List[int]] = []
    for g in generators:
        for i in range(n):
            for j in range(n):
                row = [0] * num_vars
                for a in range(n):
                    row[a * n + i] += g[a][j]
                for b in range(n):
                    row[j * n + b] -= g[i][b]
                equations.append(row)
    rank = rank_of_rows(equations)
    return num_vars - rank


def charpoly_coeffs(a: Matrix) -> List[Fraction]:
    n = len(a)
    coeffs: List[Fraction] = [Fraction(1)]
    power = [row[:] for row in a]
    traces: List[Fraction] = [Fraction(0)]
    for _ in range(1, n + 1):
        traces.append(Fraction(trace(power)))
        power = mat_mul(power, a)
    for k in range(1, n + 1):
        total = Fraction(0)
        for i in range(1, k + 1):
            total += coeffs[k - i] * traces[i]
        coeffs.append(-total / k)
    return coeffs


def coeffs_to_ints(coeffs: Sequence[Fraction]) -> List[int]:
    out: List[int] = []
    for c in coeffs:
        if c.denominator != 1:
            raise ValueError(f"Non-integral characteristic coefficient: {c}")
        out.append(c.numerator)
    return out


def apply_signed_permutation(mat: Matrix, v: Tuple[int, int, int]) -> Tuple[int, int, int]:
    out = [0, 0, 0]
    for i in range(3):
        s = 0
        for j in range(3):
            s += mat[i][j] * v[j]
        out[i] = s
    return (out[0], out[1], out[2])


def signed_permutation_group() -> List[Matrix]:
    mats: List[Matrix] = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product([-1, 1], repeat=3):
            m = zeros(3, 3)
            for i in range(3):
                m[i][perm[i]] = signs[i]
            mats.append(m)
    return mats


def build_root_decorations() -> Dict[Tuple[int, int, int], int]:
    data: Dict[Tuple[int, int, int], int] = {}
    for y in (-1, 1):
        for z in (-1, 1):
            data[(0, y, z)] = 2
    for x in (-1, 1):
        for z in (-1, 1):
            data[(x, 0, z)] = 3
    for x in (-1, 1):
        for y in (-1, 1):
            data[(x, y, 0)] = 4
    data[(-1, 0, 0)] = 2
    data[(1, 0, 0)] = 4
    data[(0, 1, 0)] = 4
    data[(0, -1, 0)] = 4
    data[(0, 0, 1)] = 4
    data[(0, 0, -1)] = 4
    return data


def stabilizer_elements() -> List[Matrix]:
    deco = build_root_decorations()
    roots = list(deco.keys())
    good: List[Matrix] = []
    for w in signed_permutation_group():
        if all(deco[apply_signed_permutation(w, r)] == deco[r] for r in roots):
            good.append(w)
    return good


def identity_check(a: Matrix, b: Matrix) -> bool:
    return a == b


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the window-6 multiplicity bulk/defect package.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_multiplicity_bulk_defect_audit.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_window6_multiplicity_bulk_defect_audit.tex"),
        help="Output TeX path.",
    )
    args = parser.parse_args()

    print("[window6-bulk-defect] building exact matrices", flush=True)

    I2 = eye(2)
    I3 = eye(3)
    I6 = eye(6)
    I12 = eye(12)
    I18 = eye(18)

    Q3 = [
        [0, 0, 1],
        [1, 0, 0],
        [0, 1, 0],
    ]
    S2 = [
        [0, 1],
        [1, 0],
    ]
    P6 = [
        [0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 1, 0],
    ]
    M = [
        [4, 0, 0],
        [0, 2, 0],
        [0, 0, 3],
    ]
    D_short = [
        [4, 0, 0, 0, 0, 0],
        [0, 4, 0, 0, 0, 0],
        [0, 0, 4, 0, 0, 0],
        [0, 0, 0, 2, 0, 0],
        [0, 0, 0, 0, 4, 0],
        [0, 0, 0, 0, 0, 4],
    ]

    D_long = kron(kron(M, I2), I2)
    U_long = kron(kron(Q3, S2), I2)
    C_long = mat_sub(mat_mul(D_long, U_long), mat_mul(U_long, D_long))

    MQ = mat_sub(mat_mul(M, Q3), mat_mul(Q3, M))
    N_short = mat_sub(mat_mul(D_short, P6), mat_mul(P6, D_short))

    K_cyc = block_diag(N_short, C_long)

    stabilizer = stabilizer_elements()
    algebra_dim = generated_algebra_dimension([D_long, U_long])
    commutant_dim = commutant_dimension([D_long, U_long])

    print("[window6-bulk-defect] checking long-block identities", flush=True)
    c3_plus_2u3 = mat_add(mat_pow(C_long, 3), mat_scale(2, mat_pow(U_long, 3)))
    c6_minus_4i = mat_sub(mat_pow(C_long, 6), mat_scale(4, I12))

    print("[window6-bulk-defect] checking short-block nilpotent defect", flush=True)
    n2 = mat_pow(N_short, 2)
    n3 = mat_pow(N_short, 3)
    rank_n = matrix_rank(N_short)
    rank_n2 = matrix_rank(n2)

    print("[window6-bulk-defect] checking characteristic and minimal polynomials", flush=True)
    k_char_coeffs = coeffs_to_ints(charpoly_coeffs(K_cyc))
    expected_k_char = [1] + [0] * 5 + [-8] + [0] * 5 + [16] + [0] * 6

    k3 = mat_pow(K_cyc, 3)
    k6 = mat_pow(K_cyc, 6)
    minpoly_eval = mat_mul(k3, mat_sub(k6, mat_scale(4, I18)))
    test_drop_lambda = mat_mul(mat_pow(K_cyc, 2), mat_sub(k6, mat_scale(4, I18)))
    test_drop_plus = mat_mul(k3, mat_sub(k3, mat_scale(2, I18)))
    test_drop_minus = mat_mul(k3, mat_add(k3, mat_scale(2, I18)))

    stabilizer_serialized = [m for m in stabilizer]
    payload = {
        "root_plane_layers": {
            "omitted_index_1": {"roots": [[0, 1, 1], [0, 1, -1], [0, -1, 1], [0, -1, -1]], "multiplicity": 2},
            "omitted_index_2": {"roots": [[1, 0, 1], [1, 0, -1], [-1, 0, 1], [-1, 0, -1]], "multiplicity": 3},
            "omitted_index_3": {"roots": [[1, 1, 0], [1, -1, 0], [-1, 1, 0], [-1, -1, 0]], "multiplicity": 4},
        },
        "weyl_stabilizer_order": len(stabilizer_serialized),
        "weyl_stabilizer_matrices": stabilizer_serialized,
        "long_generated_algebra_dimension": algebra_dim,
        "long_commutant_dimension": commutant_dim,
        "long_commutator_cubic_identity_holds": identity_check(c3_plus_2u3, zeros(12, 12)),
        "long_commutator_sixth_identity_holds": identity_check(c6_minus_4i, zeros(12, 12)),
        "short_nilpotent_rank": rank_n,
        "short_nilpotent_square_rank": rank_n2,
        "short_nilpotent_cube_is_zero": identity_check(n3, zeros(6, 6)),
        "cyclic_commutator_characteristic_coefficients": k_char_coeffs,
        "cyclic_commutator_expected_characteristic_coefficients": expected_k_char,
        "cyclic_commutator_minpoly_holds": identity_check(minpoly_eval, zeros(18, 18)),
        "cyclic_commutator_drop_lambda_factor_nonzero": not identity_check(test_drop_lambda, zeros(18, 18)),
        "cyclic_commutator_drop_plus_factor_nonzero": not identity_check(test_drop_plus, zeros(18, 18)),
        "cyclic_commutator_drop_minus_factor_nonzero": not identity_check(test_drop_minus, zeros(18, 18)),
    }

    if len(stabilizer_serialized) != 4:
        raise RuntimeError(f"Unexpected stabilizer size: {len(stabilizer_serialized)}")
    if algebra_dim != 18:
        raise RuntimeError(f"Unexpected generated algebra dimension: {algebra_dim}")
    if commutant_dim != 8:
        raise RuntimeError(f"Unexpected commutant dimension: {commutant_dim}")
    if not identity_check(c3_plus_2u3, zeros(12, 12)):
        raise RuntimeError("Long commutator cubic identity failed.")
    if not identity_check(c6_minus_4i, zeros(12, 12)):
        raise RuntimeError("Long commutator sixth identity failed.")
    if rank_n != 2 or rank_n2 != 1 or not identity_check(n3, zeros(6, 6)):
        raise RuntimeError("Short nilpotent defect audit failed.")
    if k_char_coeffs != expected_k_char:
        raise RuntimeError(f"Unexpected characteristic polynomial coefficients: {k_char_coeffs}")
    if not identity_check(minpoly_eval, zeros(18, 18)):
        raise RuntimeError("Claimed minimal polynomial does not annihilate K_6.")
    if identity_check(test_drop_lambda, zeros(18, 18)):
        raise RuntimeError("Dropped lambda-factor still annihilates K_6.")
    if identity_check(test_drop_plus, zeros(18, 18)):
        raise RuntimeError("Dropped (lambda^3-2)-factor still annihilates K_6.")
    if identity_check(test_drop_minus, zeros(18, 18)):
        raise RuntimeError("Dropped (lambda^3+2)-factor still annihilates K_6.")

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_lines = [
        "% AUTO-GENERATED by scripts/exp_window6_multiplicity_bulk_defect_audit.py",
        r"\begin{equation}\label{eq:window6_multiplicity_bulk_defect_audit}",
        r"\begin{aligned}",
        r"|\operatorname{Stab}_{W(B_3)}(m_6)|&=4,\qquad \dim_{\CC}\CC\langle D_{\ell},U_{\ell}\rangle=18,\qquad \dim_{\CC}\operatorname{Cent}(D_{\ell},U_{\ell})=8,\\",
        r"C_{\ell}^3+2U_{\ell}^3&=0,\qquad C_{\ell}^6=4I_{12},\\",
        r"\operatorname{rank}N_{\mathrm{s}}&=2,\qquad \operatorname{rank}(N_{\mathrm{s}}^2)=1,\qquad N_{\mathrm{s}}^3=0,\\",
        r"\chi_{K_6}(\lambda)&=\lambda^6(\lambda^6-4)^2,\qquad \mu_{K_6}(\lambda)=\lambda^3(\lambda^6-4).",
        r"\end{aligned}",
        r"\end{equation}",
        "",
    ]
    tex_out = Path(str(args.tex_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)
    tex_out.write_text("\n".join(tex_lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}", flush=True)
    print(f"File: {tex_out.relative_to(generated_dir().parent.parent)}", flush=True)
    print("[window6-bulk-defect] done", flush=True)


if __name__ == "__main__":
    main()
