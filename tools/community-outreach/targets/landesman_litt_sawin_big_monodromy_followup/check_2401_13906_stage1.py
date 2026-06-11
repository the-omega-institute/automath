#!/usr/bin/env python3
"""Stage-1 anchor for arXiv:2401.13906.

This checker verifies the explicit finite-group representation-degree input
used immediately after Theorem 1.3 of Landesman-Litt-Sawin:

    "when H is abelian, rbar = 1, and so it suffices to take g >= 4"

It does not attempt to verify the paper's Zariski-closure monodromy theorem.
"""

from __future__ import annotations

import datetime as _datetime
import itertools
import json
import math
import os
import signal
import time
from typing import Any, Dict, Iterable, List, Sequence, Tuple

import sympy as sp


TIME_BUDGET_SECONDS = 25 * 60
PROGRESS_INTERVAL_SECONDS = 20
OUTPUT_NAME = "check_2401_13906_stage1_output.json"
PAPER = "arXiv:2401.13906"
VERSION = "v2"
CLAIM = (
    "For abelian covering group H, the maximal dimension rbar of an irreducible "
    "complex H-representation is 1; substituting rbar=1 into Theorem 1.3 gives "
    "the stated sufficient bound g >= 4. Small dihedral examples also recover "
    "the source remark rbar=2."
)

_START_MONOTONIC = time.monotonic()
_LAST_PROGRESS = 0.0

Element = Tuple[int, ...]


class VerificationAbort(RuntimeError):
    """Raised when the Stage-1 checker exceeds its runtime budget."""


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    """Print timestamped progress, throttled for long computations."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        _LAST_PROGRESS = now


def check_time_budget(context: str) -> None:
    elapsed = time.monotonic() - _START_MONOTONIC
    if elapsed > TIME_BUDGET_SECONDS:
        raise VerificationAbort(
            f"time budget exceeded during {context}; elapsed_seconds={elapsed:.3f}"
        )


def _alarm_handler(signum: int, frame: Any) -> None:
    raise VerificationAbort("global 25-minute alarm fired before Stage-1 completed")


def cyclic_product_group(moduli: Sequence[int]) -> Tuple[List[Element], Dict[Element, Element], Dict[Tuple[Element, Element], Element]]:
    elements = [tuple(coords) for coords in itertools.product(*(range(m) for m in moduli))]

    def mul(a: Element, b: Element) -> Element:
        return tuple((a[i] + b[i]) % moduli[i] for i in range(len(moduli)))

    inverses = {a: tuple((-a[i]) % moduli[i] for i in range(len(moduli))) for a in elements}
    multiplication = {(a, b): mul(a, b) for a in elements for b in elements}
    return elements, inverses, multiplication


def dihedral_group(n: int) -> Tuple[List[Element], Dict[Element, Element], Dict[Tuple[Element, Element], Element]]:
    """Return D_n = <r,s | r^n=s^2=1, srs=r^-1> as pairs (i,j)."""
    elements = [(i, j) for i in range(n) for j in range(2)]

    def mul(a: Element, b: Element) -> Element:
        i, j = a
        k, ell = b
        sign = -1 if j else 1
        return ((i + sign * k) % n, (j + ell) % 2)

    identity = (0, 0)
    multiplication = {(a, b): mul(a, b) for a in elements for b in elements}
    inverses: Dict[Element, Element] = {}
    for a in elements:
        for b in elements:
            if multiplication[(a, b)] == identity and multiplication[(b, a)] == identity:
                inverses[a] = b
                break
        else:
            raise AssertionError(f"no inverse found for {a}")
    return elements, inverses, multiplication


def conjugacy_classes(
    elements: Sequence[Element],
    inverses: Dict[Element, Element],
    multiplication: Dict[Tuple[Element, Element], Element],
) -> List[List[Element]]:
    unseen = set(elements)
    classes: List[List[Element]] = []
    while unseen:
        seed = next(iter(unseen))
        conj = {
            multiplication[(multiplication[(g, seed)], inverses[g])]
            for g in elements
        }
        classes.append(sorted(conj))
        unseen -= conj
    return sorted(classes, key=lambda cls: (len(cls), cls))


def left_regular_matrix(
    elements: Sequence[Element],
    multiplication: Dict[Tuple[Element, Element], Element],
    group_element: Element,
) -> sp.Matrix:
    index = {element: idx for idx, element in enumerate(elements)}
    rows = len(elements)
    matrix = sp.zeros(rows, rows)
    for col, basis_element in enumerate(elements):
        product = multiplication[(group_element, basis_element)]
        matrix[index[product], col] = 1
    return matrix


def class_sum_matrices(
    elements: Sequence[Element],
    classes: Sequence[Sequence[Element]],
    multiplication: Dict[Tuple[Element, Element], Element],
) -> List[sp.Matrix]:
    matrices = []
    for cls in classes:
        class_matrix = sp.zeros(len(elements), len(elements))
        for element in cls:
            class_matrix += left_regular_matrix(elements, multiplication, element)
        matrices.append(class_matrix)
    return matrices


def split_subspaces_by_operator(
    operator: sp.Matrix,
    basis_matrices: Sequence[sp.Matrix],
) -> List[sp.Matrix]:
    split: List[sp.Matrix] = []
    for basis in basis_matrices:
        if basis.cols == 0:
            continue
        restricted = basis.gauss_jordan_solve(operator * basis)[0]
        eigen_data = restricted.eigenvects()
        for _eigenvalue, _multiplicity, eigenvectors in eigen_data:
            eigenspace_columns = [basis * vector for vector in eigenvectors]
            if not eigenspace_columns:
                continue
            eigenspace = sp.Matrix.hstack(*eigenspace_columns)
            column_basis = eigenspace.columnspace()
            if column_basis:
                split.append(sp.Matrix.hstack(*column_basis))
    return split


def irreducible_degrees_from_regular_class_sums(
    elements: Sequence[Element],
    inverses: Dict[Element, Element],
    multiplication: Dict[Tuple[Element, Element], Element],
) -> Dict[str, Any]:
    classes = conjugacy_classes(elements, inverses, multiplication)
    operators = class_sum_matrices(elements, classes, multiplication)

    subspaces: List[sp.Matrix] = [sp.eye(len(elements))]
    progress(f"diagonalizing {len(operators)} class sums for group order {len(elements)}")
    for idx, operator in enumerate(operators):
        check_time_budget(f"class-sum diagonalization operator {idx}")
        subspaces = split_subspaces_by_operator(operator, subspaces)

    eigenspace_dims = sorted(space.cols for space in subspaces)
    degrees = []
    perfect_square_dims = True
    for dim in eigenspace_dims:
        root = math.isqrt(dim)
        if root * root != dim:
            perfect_square_dims = False
        degrees.append(root)

    return {
        "order": len(elements),
        "conjugacy_class_sizes": [len(cls) for cls in classes],
        "regular_joint_eigenspace_dimensions": eigenspace_dims,
        "irreducible_degrees": sorted(degrees),
        "rbar": max(degrees) if degrees else 0,
        "sum_degrees_squared": sum(degree * degree for degree in degrees),
        "perfect_square_eigenspaces": perfect_square_dims,
    }


def genus_bounds(rbar: int) -> Dict[str, int]:
    unbranched_min_g = 2 * rbar + 2
    strict_threshold = max(2 * rbar + 1, rbar * rbar)
    arbitrary_n_min_integer_g = strict_threshold + 1
    return {
        "unbranched_n_0_min_g_from_g_ge_2rbar_plus_2": unbranched_min_g,
        "arbitrary_n_strict_threshold_max_2rbar_plus_1_rbar_squared": strict_threshold,
        "arbitrary_n_min_integer_g_from_g_greater_than_threshold": arbitrary_n_min_integer_g,
        "combined_sufficient_integer_g": max(unbranched_min_g, arbitrary_n_min_integer_g),
    }


def verify_named_group(name: str, constructor: Iterable[Any]) -> Dict[str, Any]:
    progress(f"checking {name}", force=True)
    elements, inverses, multiplication = constructor  # type: ignore[misc]
    data = irreducible_degrees_from_regular_class_sums(elements, inverses, multiplication)
    data["name"] = name
    data["bounds_if_used_in_theorem_1_3"] = genus_bounds(int(data["rbar"]))
    data["degree_square_sum_matches_group_order"] = data["sum_degrees_squared"] == data["order"]
    data["match"] = bool(data["perfect_square_eigenspaces"] and data["degree_square_sum_matches_group_order"])
    return data


def build_output(verdict: str, computed: Dict[str, Any], reason: str) -> Dict[str, Any]:
    return {
        "paper": PAPER,
        "version": VERSION,
        "claim": CLAIM,
        "verdict": verdict,
        "computed": computed,
        "expected": {
            "abelian_rbar": 1,
            "abelian_theorem_1_3_combined_sufficient_integer_g": 4,
            "small_dihedral_rbar": 2,
        },
        "reason": reason,
    }


def main() -> int:
    signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(TIME_BUDGET_SECONDS)
    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))

    try:
        progress("Landesman-Litt-Sawin arXiv:2401.13906 Stage-1 checker starting", force=True)
        progress(f"using SymPy {sp.__version__}", force=True)

        abelian_specs = {
            "C2": (2,),
            "C3": (3,),
            "C2xC2": (2, 2),
            "C2xC3": (2, 3),
            "C4xC2": (4, 2),
        }
        dihedral_specs = {"D3": 3, "D4": 4, "D5": 5, "D6": 6}

        abelian_results = [
            verify_named_group(name, cyclic_product_group(moduli))
            for name, moduli in abelian_specs.items()
        ]
        dihedral_results = [
            verify_named_group(name, dihedral_group(n))
            for name, n in dihedral_specs.items()
        ]

        abelian_rbars = [item["rbar"] for item in abelian_results]
        dihedral_rbars = [item["rbar"] for item in dihedral_results]
        abelian_bounds = genus_bounds(1)
        all_local_checks_match = all(item["match"] for item in abelian_results + dihedral_results)
        abelian_claim_matches = (
            all(rbar == 1 for rbar in abelian_rbars)
            and abelian_bounds["combined_sufficient_integer_g"] == 4
        )
        dihedral_remark_matches = all(rbar == 2 for rbar in dihedral_rbars)

        computed = {
            "sympy_version": sp.__version__,
            "abelian_examples": abelian_results,
            "dihedral_examples": dihedral_results,
            "abelian_rbars": abelian_rbars,
            "dihedral_rbars": dihedral_rbars,
            "theorem_1_3_bounds_with_rbar_1": abelian_bounds,
        }

        if all_local_checks_match and abelian_claim_matches and dihedral_remark_matches:
            verdict = "PASS"
            reason = (
                "The checker independently recovers rbar=1 for sampled finite abelian groups, "
                "substitutes rbar=1 into both Theorem 1.3 genus hypotheses to obtain g>=4, "
                "and recovers rbar=2 for sampled dihedral groups. This anchors only the "
                "explicit representation-degree arithmetic, not the monodromy theorem."
            )
        else:
            verdict = "FAIL"
            reason = (
                "At least one finite-group representation-degree check or genus-bound "
                "substitution disagreed with the source-derived expected values."
            )
        output = build_output(verdict, computed, reason)
    except VerificationAbort as exc:
        output = build_output(
            "FAIL",
            {"runtime_error": str(exc)},
            "Stage-1 checker exceeded its 25-minute runtime budget.",
        )
    finally:
        signal.alarm(0)

    progress("writing JSON output", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print(f"JSON output: {output_path}", flush=True)
    print(f"VERDICT: {output['verdict']}", flush=True)
    return 0 if output["verdict"] in {"PASS", "INCONCLUSIVE_NEED_PDF"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
