#!/usr/bin/env python3
"""Independent first-principles checks for the chi0_728 rank-108 label.

This verifier intentionally does not import or depend on the internal
``chi0_728_sector_rank108_system`` machinery.  It only checks the finite
linear facts that can be reconstructed directly from the standard symplectic
action of Mod_{3,1} on H_1(-; F_3), plus a small cited ATLAS ordinary-character
degree exclusion.

Pure Python stdlib only.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable


P = 3
DIM = 6
OUT = Path(__file__).with_name("independent_rank108_verifier_output.json")

Matrix = list[list[int]]
Vector = list[int]


def modp(x: int) -> int:
    return x % P


def identity_matrix(n: int = DIM) -> Matrix:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    return [
        [sum(a[i][k] * b[k][j] for k in range(DIM)) % P for j in range(DIM)]
        for i in range(DIM)
    ]


def mat_transpose(a: Matrix) -> Matrix:
    return [[a[j][i] for j in range(DIM)] for i in range(DIM)]


def mat_vec(a: Matrix, v: Vector) -> Vector:
    return [sum(a[i][j] * v[j] for j in range(DIM)) % P for i in range(DIM)]


def omega(v: Vector, x: Vector, j: Matrix) -> int:
    return sum(v[i] * j[i][k] * x[k] for i in range(DIM) for k in range(DIM)) % P


def transvection(v: Vector, j: Matrix) -> Matrix:
    """Matrix for T_v(x) = x + omega(v, x) v in the standard column convention."""
    ident = identity_matrix()
    omega_row = [sum(v[i] * j[i][col] for i in range(DIM)) % P for col in range(DIM)]
    return [
        [(ident[row][col] + v[row] * omega_row[col]) % P for col in range(DIM)]
        for row in range(DIM)
    ]


def standard_symplectic_form() -> Matrix:
    return [
        [0, 1, 0, 0, 0, 0],
        [-1, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0],
        [0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, -1, 0],
    ]


def reduce_matrix(a: Matrix) -> Matrix:
    return [[entry % P for entry in row] for row in a]


def is_symplectic(m: Matrix, j: Matrix) -> bool:
    return mat_mul(mat_mul(mat_transpose(m), j), m) == j


def nonzero_vectors() -> list[Vector]:
    vectors: list[Vector] = []
    for index in range(P**DIM):
        x = index
        coords = []
        for _ in range(DIM):
            coords.append(x % P)
            x //= P
        if any(coords):
            vectors.append(coords)
    return vectors


def all_vectors_are_permuted(generators: Iterable[Matrix], vectors: list[Vector]) -> bool:
    vector_set = {tuple(v) for v in vectors}
    for generator in generators:
        images = {tuple(mat_vec(generator, v)) for v in vectors}
        if images != vector_set:
            return False
    return True


def sp_order(n: int, q: int) -> int:
    order = q ** (n * n)
    for i in range(1, n + 1):
        order *= q ** (2 * i) - 1
    return order


def build_generators(j: Matrix) -> dict[str, Matrix]:
    basis = {
        "T_a1": [1, 0, 0, 0, 0, 0],
        "T_b1": [0, 1, 0, 0, 0, 0],
        "T_a2": [0, 0, 1, 0, 0, 0],
        "T_b2": [0, 0, 0, 1, 0, 0],
        "T_a3": [0, 0, 0, 0, 1, 0],
        "T_b3": [0, 0, 0, 0, 0, 1],
        "T_c_a1_plus_a2": [1, 0, 1, 0, 0, 0],
    }
    return {name: transvection(vector, j) for name, vector in basis.items()}


def main() -> None:
    j = reduce_matrix(standard_symplectic_form())
    generators = build_generators(j)
    symplectic_check = {name: is_symplectic(matrix, j) for name, matrix in generators.items()}

    vectors = nonzero_vectors()
    permutation_rep_dim = len(vectors)
    sp6_f3_full_order = sp_order(3, 3)
    sp6_f3_projective_order = sp6_f3_full_order // 2
    requested_order = 4_585_351_680
    stabilizer_order = requested_order // permutation_rep_dim
    full_sp_stabilizer_order = sp6_f3_full_order // permutation_rep_dim

    ordinary_char_degrees_known = [
        1,
        78,
        104,
        273,
        364,
        560,
        728,
        1456,
        2457,
    ]
    is_108_ordinary_degree = 108 in ordinary_char_degrees_known

    if is_108_ordinary_degree:
        hom_dim: int | str = "INDETERMINATE_NEEDS_CHARACTER_MULTIPLICITY"
        verdict = "NEEDS_BRAUER_DATA"
    else:
        hom_dim = "INDETERMINATE_NEEDS_BRAUER"
        verdict = "NEEDS_BRAUER_DATA"

    result = {
        "system_name_not_used_as_input": "chi0_728_sector_rank108_system",
        "method": (
            "Reconstruct seven mod-3 symplectic transvections from the standard "
            "basis a1,b1,a2,b2,a3,b3 and c=a1+a2; verify the 728 nonzero-vector "
            "permutation representation; compare 108 only against a hardcoded "
            "cited subset of ordinary ATLAS character degrees."
        ),
        "field": "F_3",
        "basis_order": ["a1", "b1", "a2", "b2", "a3", "b3"],
        "symplectic_form_J_mod_3": j,
        "generators": generators,
        "symplectic_check": symplectic_check,
        "all_generators_symplectic": all(symplectic_check.values()),
        "permutation_rep_dim": permutation_rep_dim,
        "sp6_action_on_nonzero_vectors_transitive": True,
        "sp6_action_on_nonzero_vectors_transitive_justification": (
            "Standard finite symplectic linear algebra: over F_3 every vector is "
            "isotropic for the alternating form, and Sp_6(F_3) acts transitively "
            "on nonzero vectors.  Thus the nonzero-vector permutation action has "
            "one orbit of size 3^6-1=728."
        ),
        "nonzero_vectors_are_permuted_by_generators": all_vectors_are_permuted(
            generators.values(), vectors
        ),
        "sp6_f3_order": requested_order,
        "sp6_f3_order_convention_note": (
            "The requested value 4585351680 is |PSp_6(3)|, not full |Sp_6(F_3)|. "
            "Full |Sp_6(F_3)| is 9170703360 because -I is a nontrivial central "
            "element in characteristic 3.  The JSON keeps the requested field "
            "sp6_f3_order equal to 4585351680 for compatibility with the prompt."
        ),
        "sp6_f3_full_order_formula": "3^9 * (3^2-1) * (3^4-1) * (3^6-1)",
        "sp6_f3_full_order_computed": sp6_f3_full_order,
        "psp6_f3_order_computed": sp6_f3_projective_order,
        "projective_order_matches_requested_order": sp6_f3_projective_order == requested_order,
        "stabilizer_order": stabilizer_order,
        "stabilizer_order_division_exact": requested_order % permutation_rep_dim == 0,
        "full_sp6_nonzero_vector_stabilizer_order": full_sp_stabilizer_order,
        "ordinary_char_degrees_known": ordinary_char_degrees_known,
        "ordinary_char_degrees_attribution": "ATLAS of Finite Groups, Conway et al. 1985",
        "ordinary_char_degrees_scope": (
            "Prompt-supplied/cited ordinary degree subset for Sp_6(3)/PSp_6(3); "
            "this verifier does not claim the subset is a complete printed "
            "character table."
        ),
        "is_108_ordinary_degree": is_108_ordinary_degree,
        "is_108_ordinary_degree_justification": (
            "No: 108 is absent from the hardcoded ATLAS-cited ordinary-degree subset "
            "[1, 78, 104, 273, 364, 560, 728, 1456, 2457].  Therefore the rank-108 "
            "label cannot be verified here as an ordinary irreducible degree.  A "
            "complete ordinary table would be stronger, but no degree in the cited "
            "subset supports 108."
        ),
        "brauer_degrees_3_status": "NEEDS_BRAUER_DATA",
        "brauer_degrees_3_status_justification": (
            "This stdlib-only verifier does not contain the 3-modular Brauer "
            "decomposition matrix or 3-Brauer irreducible degrees for Sp_6(3)/PSp_6(3). "
            "Since the defining characteristic is 3, an internal 108-dimensional "
            "sector could in principle be modular, reducible, a quotient/submodule, "
            "or a coefficient-system rank rather than an ordinary irreducible. "
            "Actual Brauer data or source matrices are required to decide that."
        ),
        "hom_dim_108_into_728": hom_dim,
        "hom_dim_108_into_728_justification": (
            "For ordinary semisimple character theory, Hom(V_108, Perm_728) is the "
            "multiplicity of an ordinary irreducible V_108 in the 728-dimensional "
            "permutation character.  Because no ordinary irreducible V_108 is "
            "identified from the cited ATLAS subset, Hom=0 would only be a "
            "tautological statement for ordinary irreducibles.  It does not verify "
            "the internal rank-108/F_3 Hom computation, whose meaningful version "
            "needs the actual 3-modular Brauer sector or the explicit source matrices."
        ),
        "verdict": verdict,
        "verdict_rationale": (
            "The first-principles linear part is verified: the seven displayed "
            "Dehn-twist transvection matrices over F_3 preserve the standard "
            "symplectic form, and the nonzero-vector permutation representation has "
            "dimension 3^6-1=728.  The order arithmetic also exposes a convention "
            "point: 4585351680 is the projective symplectic order |PSp_6(3)|; full "
            "|Sp_6(F_3)| is twice that.\n\n"
            "The rank-108/Hom-dim-0 team construct is not closure-grade verified by "
            "these data.  The cited ordinary ATLAS degree subset does not contain "
            "108, so a 108-dimensional ordinary irreducible is not supported here; "
            "however, this only gives a tautological ordinary-character exclusion.  "
            "The meaningful F_3-sector claim remains indeterminate until the "
            "3-modular Brauer degrees/decomposition data or the explicit internal "
            "rank-108 coefficient matrices are supplied."
        ),
    }

    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
