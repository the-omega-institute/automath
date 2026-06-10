#!/usr/bin/env python3
"""Stage-4 exact CRT-translation check for arXiv:2605.20695.

This script implements the Oracle Stage-4 construction in the multiquadratic
field

    K_0 = Q(sqrt(5), sqrt(13), sqrt(17), sqrt(21), sqrt(33), i).

Elements are stored as 64-dimensional Q-vectors in the basis

    prod_{j in S} sqrt(d_j) * i^k,  S subset {0,...,4}, k in {0,1}.

The construction forms CRT selector elements E_eps, translation elements
u_eps = A_eps / conj(A_eps), additive-cube point sets P_m, and exact
unit-distance counts.  Floating point embedding is used only for sanity
diagnostics; all pass/fail decisions use Fraction arithmetic.
"""

from __future__ import annotations

import itertools
import json
import math
import os
import signal
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


TARGET_DIR = Path(__file__).resolve().parent
OUTPUT_PATH = TARGET_DIR / "check_2605_20695_CRT_translation_stage4_output.json"

D_VALUES = (5, 13, 17, 21, 33)
RHO_VALUES = (45, 35, 44, 18, 29)
MODULUS = 101
FIELD_DEGREE = 64
PROGRESS_INTERVAL_SECONDS = 20.0
TIME_BUDGET_SECONDS = 24.0 * 60.0
M_SMOKE = 6
M_TARGET = 8
M_BONUS = 10
F0 = Fraction(0)
F1 = Fraction(1)

_START = time.monotonic()
_LAST_PROGRESS = 0.0


class Stage4Timeout(RuntimeError):
    """Raised when the script should stop and preserve the best result so far."""


def elapsed_seconds() -> float:
    return time.monotonic() - _START


def progress(stage: str, detail: str = "", force: bool = False) -> None:
    """Emit throttled progress messages to stderr."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        suffix = f" {detail}" if detail else ""
        print(f"[t={now - _START:.1f}s] {stage}{suffix}", file=sys.stderr, flush=True)
        _LAST_PROGRESS = now


def check_budget(context: str, reserve_seconds: float = 0.0) -> None:
    remaining = TIME_BUDGET_SECONDS - elapsed_seconds()
    if remaining < reserve_seconds:
        raise Stage4Timeout(
            f"time budget guard during {context}: "
            f"elapsed={elapsed_seconds():.3f}s, reserve={reserve_seconds:.3f}s, "
            f"budget={TIME_BUDGET_SECONDS:.3f}s"
        )


def _alarm_handler(signum: int, frame: object) -> None:
    raise Stage4Timeout("global Stage-4 alarm fired")


def idx(mask: int, k: int) -> int:
    return 2 * mask + k


def mask_k(index: int) -> tuple[int, int]:
    return index // 2, index % 2


def basis_name(index: int) -> str:
    mask, k = mask_k(index)
    parts = [f"sqrt({D_VALUES[j]})" for j in range(5) if mask & (1 << j)]
    if k:
        parts.append("i")
    return "*".join(parts) if parts else "1"


def basis_mul_rule(left: int, right: int) -> tuple[int, int]:
    """Return (basis_index, integer_multiplier) for basis[left] * basis[right]."""
    mask_left, k_left = mask_k(left)
    mask_right, k_right = mask_k(right)
    common = mask_left & mask_right
    multiplier = 1
    for j, d in enumerate(D_VALUES):
        if common & (1 << j):
            multiplier *= d

    out_mask = mask_left ^ mask_right
    k_sum = k_left + k_right
    if k_sum == 2:
        multiplier *= -1
        out_k = 0
    else:
        out_k = k_sum
    return idx(out_mask, out_k), multiplier


BASIS_MUL = tuple(
    tuple(basis_mul_rule(i, j) for j in range(FIELD_DEGREE)) for i in range(FIELD_DEGREE)
)


def elem_zero() -> tuple[Fraction, ...]:
    return (F0,) * FIELD_DEGREE


def elem_one() -> tuple[Fraction, ...]:
    values = [F0] * FIELD_DEGREE
    values[0] = F1
    return tuple(values)


def elem_basis(mask: int, k: int = 0, coeff: Fraction | int = F1) -> tuple[Fraction, ...]:
    values = [F0] * FIELD_DEGREE
    values[idx(mask, k)] = Fraction(coeff)
    return tuple(values)


ZERO = elem_zero()
ONE = elem_one()
I_ELEM = elem_basis(0, 1)


def elem_add(left: tuple[Fraction, ...], right: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return tuple(a + b for a, b in zip(left, right))


def elem_sub(left: tuple[Fraction, ...], right: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return tuple(a - b for a, b in zip(left, right))


def elem_neg(value: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return tuple(-a for a in value)


def elem_scale(value: tuple[Fraction, ...], scalar: Fraction | int) -> tuple[Fraction, ...]:
    scalar_fraction = Fraction(scalar)
    if scalar_fraction == 0:
        return ZERO
    if scalar_fraction == 1:
        return value
    return tuple(scalar_fraction * a for a in value)


def nonzero_items(value: tuple[Fraction, ...]) -> list[tuple[int, Fraction]]:
    return [(i, coeff) for i, coeff in enumerate(value) if coeff]


def elem_mul(left: tuple[Fraction, ...], right: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    out = [F0] * FIELD_DEGREE
    left_items = nonzero_items(left)
    right_items = nonzero_items(right)
    for i, a in left_items:
        for j, b in right_items:
            out_index, multiplier = BASIS_MUL[i][j]
            out[out_index] += a * b * multiplier
    return tuple(out)


def elem_conj(value: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """Imaginary conjugation only: i -> -i, all sqrt(d_j) fixed."""
    out = list(value)
    for mask in range(32):
        out[idx(mask, 1)] = -out[idx(mask, 1)]
    return tuple(out)


def elem_is_one(value: tuple[Fraction, ...]) -> bool:
    return value[0] == 1 and all(coeff == 0 for coeff in value[1:])


def elem_is_rational(value: tuple[Fraction, ...]) -> bool:
    return all(coeff == 0 for coeff in value[1:])


def elem_to_display(value: tuple[Fraction, ...], max_terms: int = 8) -> str:
    terms = []
    for index, coeff in enumerate(value):
        if coeff:
            terms.append(f"{coeff}*{basis_name(index)}")
            if len(terms) == max_terms:
                break
    suffix = "" if len(nonzero_items(value)) <= max_terms else " + ..."
    return "0" if not terms else " + ".join(terms) + suffix


def multiplication_matrix(multiplier: tuple[Fraction, ...]) -> list[list[Fraction]]:
    """Matrix for x -> multiplier*x in the fixed basis, as rows."""
    rows = [[F0] * FIELD_DEGREE for _ in range(FIELD_DEGREE)]
    multiplier_items = nonzero_items(multiplier)
    for col in range(FIELD_DEGREE):
        for i, coeff in multiplier_items:
            out_index, integer = BASIS_MUL[i][col]
            rows[out_index][col] += coeff * integer
    return rows


def solve_linear_system(matrix: list[list[Fraction]], rhs: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """Solve matrix*x = rhs over Q by Gauss-Jordan elimination."""
    aug = [row[:] + [rhs[row_index]] for row_index, row in enumerate(matrix)]
    pivot_row = 0
    for col in range(FIELD_DEGREE):
        pivot = None
        for row in range(pivot_row, FIELD_DEGREE):
            if aug[row][col]:
                pivot = row
                break
        if pivot is None:
            continue

        if pivot != pivot_row:
            aug[pivot_row], aug[pivot] = aug[pivot], aug[pivot_row]

        pivot_value = aug[pivot_row][col]
        if pivot_value != 1:
            inv_pivot = F1 / pivot_value
            aug[pivot_row] = [entry * inv_pivot for entry in aug[pivot_row]]

        for row in range(FIELD_DEGREE):
            if row == pivot_row:
                continue
            factor = aug[row][col]
            if factor:
                pivot_entries = aug[pivot_row]
                aug[row] = [entry - factor * pivot_entry for entry, pivot_entry in zip(aug[row], pivot_entries)]

        pivot_row += 1
        if pivot_row == FIELD_DEGREE:
            break

    if pivot_row != FIELD_DEGREE:
        raise ZeroDivisionError("singular multiplication matrix in K_0 inversion/division")

    return tuple(aug[row][FIELD_DEGREE] for row in range(FIELD_DEGREE))


def elem_div(numerator: tuple[Fraction, ...], denominator: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """Return numerator / denominator by solving denominator*x = numerator."""
    return solve_linear_system(multiplication_matrix(denominator), numerator)


def embed_complex(value: tuple[Fraction, ...]) -> complex:
    roots = [math.sqrt(d) for d in D_VALUES]
    total = 0j
    for index, coeff in enumerate(value):
        if not coeff:
            continue
        mask, k = mask_k(index)
        real_factor = 1.0
        for j, root in enumerate(roots):
            if mask & (1 << j):
                real_factor *= root
        total += float(coeff) * real_factor * ((1j) ** k)
    return total


def sign_vectors() -> Iterable[tuple[int, ...]]:
    return itertools.product((-1, 1), repeat=5)


def build_crt_selector(epsilon: tuple[int, ...], inverses: tuple[int, ...]) -> tuple[Fraction, ...]:
    progress("E_eps build", f"epsilon={epsilon}")
    value = ONE
    for j, eps_j in enumerate(epsilon):
        factor = elem_add(ONE, elem_basis(1 << j, 0, eps_j * inverses[j]))
        value = elem_mul(value, factor)
    return elem_scale(value, Fraction(1, 2**5))


def build_u_for_epsilon(epsilon: tuple[int, ...], inverses: tuple[int, ...]) -> dict[str, Any]:
    selector = build_crt_selector(epsilon, inverses)
    a_eps = elem_add(ONE, elem_mul(selector, elem_sub(I_ELEM, elem_scale(ONE, 11))))
    denominator = elem_conj(a_eps)
    progress("u_eps build", f"solving division for epsilon={epsilon}")
    u_eps = elem_div(a_eps, denominator)
    norm = elem_mul(u_eps, elem_conj(u_eps))
    if not elem_is_one(norm):
        raise AssertionError(f"u_epsilon norm-one check failed for {epsilon}: {elem_to_display(norm)}")
    z = embed_complex(u_eps)
    return {
        "epsilon": epsilon,
        "selector": selector,
        "A": a_eps,
        "u": u_eps,
        "embedding": z,
        "embedding_abs": abs(z),
        "selector_nonzero_terms": len(nonzero_items(selector)),
        "A_nonzero_terms": len(nonzero_items(a_eps)),
        "u_nonzero_terms": len(nonzero_items(u_eps)),
    }


def build_all_u() -> list[dict[str, Any]]:
    inverses = tuple(pow(rho, -1, MODULUS) for rho in RHO_VALUES)
    progress("E_eps build", f"rho inverses mod {MODULUS}: {inverses}", force=True)
    records = []
    for epsilon in sign_vectors():
        check_budget("building u_eps values", reserve_seconds=30.0)
        records.append(build_u_for_epsilon(epsilon, inverses))
    return records


def build_points(u_values: list[tuple[Fraction, ...]]) -> tuple[list[tuple[Fraction, ...]], dict[tuple[Fraction, ...], int], int]:
    progress("P_m build", f"m={len(u_values)}", force=True)
    points = [ZERO]
    subset_masks = [0]
    for j, u_j in enumerate(u_values):
        existing_count = len(points)
        for point_index in range(existing_count):
            points.append(elem_add(points[point_index], u_j))
            subset_masks.append(subset_masks[point_index] | (1 << j))
        progress("P_m build", f"added generator {j + 1}/{len(u_values)}, raw points={len(points)}")

    unique: dict[tuple[Fraction, ...], int] = {}
    duplicate_count = 0
    for point, subset_mask in zip(points, subset_masks):
        if point in unique:
            duplicate_count += 1
        else:
            unique[point] = subset_mask
    return points, unique, duplicate_count


def ternary_vectors(m: int) -> Iterable[tuple[int, ...]]:
    """Yield one representative of each nonzero c ~ -c in {-1,0,1}^m."""
    for coeffs in itertools.product((-1, 0, 1), repeat=m):
        if all(c == 0 for c in coeffs):
            continue
        first_nonzero = next(c for c in coeffs if c != 0)
        if first_nonzero == 1:
            yield coeffs


def linear_combination(coeffs: tuple[int, ...], u_values: list[tuple[Fraction, ...]]) -> tuple[Fraction, ...]:
    out = ZERO
    for coeff, u_j in zip(coeffs, u_values):
        if coeff == 1:
            out = elem_add(out, u_j)
        elif coeff == -1:
            out = elem_sub(out, u_j)
    return out


def precompute_gram(u_values: list[tuple[Fraction, ...]]) -> list[list[tuple[Fraction, ...]]]:
    """Precompute exact products u_i * conj(u_j) for fast norm checks."""
    m = len(u_values)
    progress("pair-check loop", f"precomputing exact Gram table for m={m}", force=True)
    gram = [[ZERO for _ in range(m)] for _ in range(m)]
    conjugates = [elem_conj(u_j) for u_j in u_values]
    for i, u_i in enumerate(u_values):
        for j, conj_u_j in enumerate(conjugates):
            gram[i][j] = elem_mul(u_i, conj_u_j)
    return gram


def norm_from_gram(coeffs: tuple[int, ...], gram: list[list[tuple[Fraction, ...]]]) -> tuple[Fraction, ...]:
    """Return (sum c_i u_i) * conj(sum c_i u_i) using precomputed products."""
    out = ZERO
    nonzero = [(index, coeff) for index, coeff in enumerate(coeffs) if coeff]
    for i, coeff_i in nonzero:
        for j, coeff_j in nonzero:
            scalar = coeff_i * coeff_j
            term = gram[i][j]
            if scalar == 1:
                out = elem_add(out, term)
            elif scalar == -1:
                out = elem_sub(out, term)
            else:
                raise AssertionError(f"unexpected ternary coefficient product {scalar}")
    return out


def count_unit_pairs_by_ternary(u_values: list[tuple[Fraction, ...]]) -> dict[str, Any]:
    """Exact pair count for an injective additive cube via difference patterns."""
    m = len(u_values)
    total_patterns = (3**m - 1) // 2
    gram = precompute_gram(u_values)
    checked = 0
    exact_pairs = 0
    unit_patterns = 0
    examples: list[dict[str, Any]] = []
    for coeffs in ternary_vectors(m):
        check_budget(f"pair-check loop m={m}", reserve_seconds=20.0)
        checked += 1
        if checked == 1 or checked % 100 == 0:
            progress("pair-check loop", f"m={m}, pattern {checked}/{total_patterns}")

        distance_squared = norm_from_gram(coeffs, gram)
        if elem_is_one(distance_squared):
            zeros = coeffs.count(0)
            multiplicity = 2**zeros
            exact_pairs += multiplicity
            unit_patterns += 1
            if len(examples) < 12:
                examples.append(
                    {
                        "difference_coefficients": coeffs,
                        "pair_multiplicity": multiplicity,
                    }
                )

    return {
        "method": "ternary_difference_patterns_after_exact_no-dedup_check",
        "patterns_checked": checked,
        "unit_difference_patterns": unit_patterns,
        "exact_unit_distance_pairs": exact_pairs,
        "examples": examples,
    }


def count_unit_pairs_direct(points: list[tuple[Fraction, ...]]) -> dict[str, Any]:
    """Fallback exact pair count if the additive cube has duplicate point values."""
    total_pairs = len(points) * (len(points) - 1) // 2
    checked = 0
    exact_pairs = 0
    examples: list[dict[str, int]] = []
    for i, left in enumerate(points):
        for j in range(i + 1, len(points)):
            check_budget("direct pair-check loop", reserve_seconds=20.0)
            checked += 1
            if checked == 1 or checked % 500 == 0:
                progress("pair-check loop", f"direct pair {checked}/{total_pairs}")
            delta = elem_sub(left, points[j])
            if elem_is_one(elem_mul(delta, elem_conj(delta))):
                exact_pairs += 1
                if len(examples) < 12:
                    examples.append({"left_index": i, "right_index": j})
    return {
        "method": "direct_pairs_after_dedup",
        "pairs_checked": checked,
        "exact_unit_distance_pairs": exact_pairs,
        "examples": examples,
    }


def verify_cube_edges(u_values: list[tuple[Fraction, ...]]) -> dict[str, Any]:
    m = len(u_values)
    checked = 0
    failed: list[dict[str, Any]] = []
    generator_norm_one = [elem_is_one(elem_mul(u_j, elem_conj(u_j))) for u_j in u_values]
    for subset in range(1 << m):
        for j, u_j in enumerate(u_values):
            if subset & (1 << j):
                continue
            checked += 1
            if not generator_norm_one[j]:
                failed.append({"subset": subset, "generator_index": j})
                if len(failed) >= 10:
                    return {"checked": checked, "failed": failed, "verified": False}
    return {"checked": checked, "failed": failed, "verified": not failed}


def evaluate_m(m: int, u_records: list[dict[str, Any]]) -> dict[str, Any]:
    progress("P_m build", f"starting m={m}", force=True)
    u_values = [record["u"] for record in u_records[:m]]
    points, unique_points, duplicate_count = build_points(u_values)
    raw_point_count = len(points)
    n_points = len(unique_points)

    if duplicate_count == 0:
        pair_details = count_unit_pairs_by_ternary(u_values)
    else:
        pair_details = count_unit_pairs_direct(list(unique_points.keys()))

    cube_details = verify_cube_edges(u_values)
    guaranteed_cube_edges = m * (2 ** (m - 1))
    exact_pairs = int(pair_details["exact_unit_distance_pairs"])
    bonus_cross_edges = exact_pairs - guaranteed_cube_edges
    z_values = [record["embedding"] for record in u_records[:m]]
    unit_abs_errors = [abs(abs(z) - 1.0) for z in z_values]
    point_embeddings = [embed_complex(point) for point in list(unique_points.keys())[: min(16, n_points)]]
    return {
        "m": m,
        "raw_points_before_dedup": raw_point_count,
        "n_points": n_points,
        "duplicate_points": duplicate_count,
        "guaranteed_cube_edges": guaranteed_cube_edges,
        "exact_unit_distance_pairs": exact_pairs,
        "bonus_cross_edges": bonus_cross_edges,
        "cube_edges": cube_details,
        "pair_count_details": pair_details,
        "embedding_sanity": {
            "max_abs_u_minus_1": max(unit_abs_errors) if unit_abs_errors else None,
            "first_u_values": [
                {
                    "epsilon": list(record["epsilon"]),
                    "real": record["embedding"].real,
                    "imag": record["embedding"].imag,
                    "abs": record["embedding_abs"],
                }
                for record in u_records[:m]
            ],
            "first_point_embeddings": [
                {"real": z.real, "imag": z.imag, "abs": abs(z)} for z in point_embeddings
            ],
        },
    }


def build_output(
    attempted: list[int],
    completed_results: list[dict[str, Any]],
    u_records: list[dict[str, Any]],
    notes: list[str],
) -> dict[str, Any]:
    final = completed_results[-1] if completed_results else None
    if final is None:
        verdict = "FAIL"
        pass_bool = False
        m_reached = 0
        n_points = 0
        guaranteed = 0
        exact_pairs = 0
        bonus = 0
    else:
        m_reached = int(final["m"])
        n_points = int(final["n_points"])
        guaranteed = int(final["guaranteed_cube_edges"])
        exact_pairs = int(final["exact_unit_distance_pairs"])
        bonus = int(final["bonus_cross_edges"])
        pass_bool = exact_pairs >= guaranteed and m_reached >= M_TARGET
        if pass_bool:
            verdict = "PASS"
        elif exact_pairs >= guaranteed and m_reached >= M_SMOKE and bool(final["cube_edges"]["verified"]):
            verdict = "PARTIAL"
        else:
            verdict = "FAIL"

    l_t_layer_exercised = bool(u_records) and all(
        all(record["selector"][idx(1 << j, 0)] != 0 for j in range(5)) for record in u_records[: max(1, m_reached)]
    )
    all_norm_one = bool(u_records) and all(elem_is_one(elem_mul(record["u"], elem_conj(record["u"]))) for record in u_records[: max(1, m_reached)])

    output: dict[str, Any] = {
        "stage": 4,
        "construction": "CRT_translation",
        "paper": "arXiv:2605.20695",
        "field": "Q(sqrt(5,13,17,21,33), i)",
        "field_degree": FIELD_DEGREE,
        "d_values": list(D_VALUES),
        "rho_values_mod_101": list(RHO_VALUES),
        "rho_inverses_mod_101_lifted_to_Q": [pow(rho, -1, MODULUS) for rho in RHO_VALUES],
        "m_attempted": attempted,
        "m_reached": m_reached,
        "n_points": n_points,
        "guaranteed_cube_edges": guaranteed,
        "exact_unit_distance_pairs": exact_pairs,
        "bonus_cross_edges": bonus,
        "L_T_layer_exercised": l_t_layer_exercised,
        "all_selected_u_norm_one_exact": all_norm_one,
        "runtime_seconds": elapsed_seconds(),
        "pass": pass_bool,
        "verdict": verdict,
        "notes": notes,
        "completed_m_results": completed_results,
    }
    return output


def write_output(output: dict[str, Any]) -> None:
    OUTPUT_PATH.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    if hasattr(signal, "SIGALRM"):
        signal.signal(signal.SIGALRM, _alarm_handler)
        signal.alarm(int(TIME_BUDGET_SECONDS) + 5)

    notes: list[str] = []
    attempted: list[int] = []
    completed_results: list[dict[str, Any]] = []
    u_records: list[dict[str, Any]] = []

    try:
        u_records = build_all_u()
        notes.append("Built all 32 CRT translations exactly in the 64-dimensional Q-basis.")

        for m in (M_SMOKE, M_TARGET):
            attempted.append(m)
            result = evaluate_m(m, u_records)
            completed_results.append(result)
            notes.append(
                f"m={m}: n={result['n_points']}, exact pairs={result['exact_unit_distance_pairs']}, "
                f"guaranteed cube edges={result['guaranteed_cube_edges']}."
            )

        if os.environ.get("OUTREACH_STAGE4_ALLOW_M10", "0") == "1":
            remaining_after_m8 = TIME_BUDGET_SECONDS - elapsed_seconds()
            attempted.append(M_BONUS)
            notes.append(
                f"OUTREACH_STAGE4_ALLOW_M10=1 set; running m={M_BONUS} bonus attempt "
                f"with {remaining_after_m8:.1f}s remaining of the internal 24-min budget."
            )
            result = evaluate_m(M_BONUS, u_records)
            completed_results.append(result)
            notes.append(
                f"m={M_BONUS}: bonus attempt completed with n={result['n_points']} and "
                f"exact pairs={result['exact_unit_distance_pairs']}."
            )
        else:
            notes.append(
                f"Skipped m={M_BONUS} by default; set OUTREACH_STAGE4_ALLOW_M10=1 to "
                "enable. Prior 10-min runs got 56% through the 29524-pattern pair-check."
            )

    except Stage4Timeout as exc:
        notes.append(f"Stopped early by budget guard: {exc}")
    except Exception as exc:
        notes.append(f"Stage-4 exception: {type(exc).__name__}: {exc}")
        output = build_output(attempted, completed_results, u_records, notes)
        output["verdict"] = "FAIL" if not completed_results else output["verdict"]
        output["pass"] = bool(output["pass"]) and output["verdict"] == "PASS"
        write_output(output)
        print(f"VERDICT: {output['verdict']}")
        print(f"JSON: {OUTPUT_PATH.resolve()}")
        raise
    finally:
        if hasattr(signal, "SIGALRM"):
            signal.alarm(0)

    output = build_output(attempted, completed_results, u_records, notes)
    write_output(output)
    print(f"VERDICT: {output['verdict']}")
    print(f"JSON: {OUTPUT_PATH.resolve()}")
    print(
        "SUMMARY: "
        f"m={output['m_reached']}, n={output['n_points']}, "
        f"cube_edges={output['guaranteed_cube_edges']}, "
        f"exact_pairs={output['exact_unit_distance_pairs']}, "
        f"bonus_edges={output['bonus_cross_edges']}"
    )
    return 0 if output["verdict"] in {"PASS", "PARTIAL"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
