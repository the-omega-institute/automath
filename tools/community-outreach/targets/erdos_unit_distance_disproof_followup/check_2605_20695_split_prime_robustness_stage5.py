#!/usr/bin/env python3
"""Stage-5 split-prime robustness sweep for arXiv:2605.20695.

This checker repeats the Stage-4 CRT translation construction at several
split primes q.  The Stage-4 script in this checkout is
``check_2605_20695_CRT_translation_stage4.py``; its generator order is the
lexicographic order on ``itertools.product((-1, 1), repeat=5)``, its m-point
selection is the first m constructed u_eps values, and its exact pair count
uses ternary difference patterns when the additive cube has no duplicates.
Those choices are mirrored here for m=6.
"""

from __future__ import annotations

import itertools
import json
import signal
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

from sympy.ntheory.residue_ntheory import is_quad_residue, sqrt_mod


TARGET_DIR = Path(__file__).resolve().parent
OUTPUT_PATH = TARGET_DIR / "check_2605_20695_split_prime_robustness_stage5_output.json"

T_VALUES = (3, 5, 7, 11, 13, 17)
D_VALUES = (5, 13, 17, 21, 33)
Q_CAND = (101, 1361, 1889, 2141, 2609, 3449, 4241, 5381, 7229, 7309)
FIELD_DEGREE = 64
M = 6
TARGET_SPLIT_PRIME_COUNT = 4
MIN_SPLIT_PRIME_COUNT = 3
PROGRESS_INTERVAL_SECONDS = 20.0
TIME_BUDGET_SECONDS = 25.0 * 60.0
F0 = Fraction(0)
F1 = Fraction(1)

_START = time.monotonic()
_LAST_PROGRESS = 0.0


class Stage5Partial(RuntimeError):
    """Raised when the checker must write a partial JSON result."""


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
        raise Stage5Partial(
            f"time budget guard during {context}: "
            f"elapsed={elapsed_seconds():.3f}s, reserve={reserve_seconds:.3f}s, "
            f"budget={TIME_BUDGET_SECONDS:.3f}s"
        )


def _alarm_handler(signum: int, frame: object) -> None:
    raise Stage5Partial("global Stage-5 alarm fired")


def idx(mask: int, k: int) -> int:
    return 2 * mask + k


def mask_k(index: int) -> tuple[int, int]:
    return index // 2, index % 2


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


def sign_vectors() -> Iterable[tuple[int, ...]]:
    return itertools.product((-1, 1), repeat=5)


def build_crt_selector(epsilon: tuple[int, ...], inverses: tuple[int, ...]) -> tuple[Fraction, ...]:
    value = ONE
    for j, eps_j in enumerate(epsilon):
        factor = elem_add(ONE, elem_basis(1 << j, 0, eps_j * inverses[j]))
        value = elem_mul(value, factor)
    return elem_scale(value, Fraction(1, 2**5))


def build_u_for_epsilon(
    epsilon: tuple[int, ...],
    inverses: tuple[int, ...],
    rho_i: int,
) -> dict[str, Any]:
    selector = build_crt_selector(epsilon, inverses)
    # Stage-4 uses A = 1 + E*(i - 11).  Since 11 = rho_i + 1 for q=101,
    # the split-prime sweep uses the same A = 1 - E + E*(i - rho_i).
    a_eps = elem_add(ONE, elem_mul(selector, elem_sub(I_ELEM, elem_scale(ONE, rho_i + 1))))
    denominator = elem_conj(a_eps)
    u_eps = elem_div(a_eps, denominator)
    norm = elem_mul(u_eps, elem_conj(u_eps))
    if not elem_is_one(norm):
        raise AssertionError(f"u_epsilon norm-one check failed for q-root rho_i={rho_i}, epsilon={epsilon}")
    return {"epsilon": epsilon, "selector": selector, "A": a_eps, "u": u_eps}


def build_selected_u_records(q: int, roots: dict[str, int]) -> list[dict[str, Any]]:
    rho_values = tuple(roots[str(d)] for d in D_VALUES)
    inverses = tuple(pow(rho, -1, q) for rho in rho_values)
    selected_eps = list(itertools.islice(sign_vectors(), M))
    records = []
    for index, epsilon in enumerate(selected_eps, start=1):
        check_budget(f"building u_eps q={q}", reserve_seconds=60.0)
        progress("u_eps build", f"q={q}, selected generator {index}/{M}, epsilon={epsilon}")
        records.append(build_u_for_epsilon(epsilon, inverses, roots["-1"]))
    return records


def build_points(
    u_values: list[tuple[Fraction, ...]],
) -> tuple[list[tuple[Fraction, ...]], dict[tuple[Fraction, ...], int], int]:
    progress("P_m build", f"m={len(u_values)}")
    points = [ZERO]
    subset_masks = [0]
    for j, u_j in enumerate(u_values):
        existing_count = len(points)
        for point_index in range(existing_count):
            points.append(elem_add(points[point_index], u_j))
            subset_masks.append(subset_masks[point_index] | (1 << j))

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


def precompute_gram(u_values: list[tuple[Fraction, ...]]) -> list[list[tuple[Fraction, ...]]]:
    m = len(u_values)
    progress("pair-check loop", f"precomputing exact Gram table for m={m}")
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


def count_unit_pairs_by_ternary(u_values: list[tuple[Fraction, ...]]) -> int:
    """Exact pair count for an injective additive cube via difference patterns."""
    m = len(u_values)
    total_patterns = (3**m - 1) // 2
    gram = precompute_gram(u_values)
    checked = 0
    exact_pairs = 0
    for coeffs in ternary_vectors(m):
        check_budget(f"pair-check loop m={m}", reserve_seconds=40.0)
        checked += 1
        if checked == 1 or checked % 100 == 0:
            progress("pair-check loop", f"m={m}, pattern {checked}/{total_patterns}")

        distance_squared = norm_from_gram(coeffs, gram)
        if elem_is_one(distance_squared):
            exact_pairs += 2 ** coeffs.count(0)
    return exact_pairs


def count_unit_pairs_direct(points: list[tuple[Fraction, ...]]) -> int:
    """Fallback exact pair count if the additive cube has duplicate point values."""
    total_pairs = len(points) * (len(points) - 1) // 2
    checked = 0
    exact_pairs = 0
    for i, left in enumerate(points):
        for j in range(i + 1, len(points)):
            check_budget("direct pair-check loop", reserve_seconds=40.0)
            checked += 1
            if checked == 1 or checked % 500 == 0:
                progress("pair-check loop", f"direct pair {checked}/{total_pairs}")
            delta = elem_sub(left, points[j])
            if elem_is_one(elem_mul(delta, elem_conj(delta))):
                exact_pairs += 1
    return exact_pairs


def verify_splitting_predicate(q: int) -> bool:
    return q % 4 == 1 and all(bool(is_quad_residue(d, q)) for d in D_VALUES)


def roots_for_prime(q: int) -> dict[str, int]:
    roots: dict[str, int] = {}
    for d in D_VALUES:
        root = sqrt_mod(d, q, all_roots=False)
        if root is None:
            raise Stage5Partial(f"sqrt_mod({d}, {q}) unexpectedly returned None")
        roots[str(d)] = int(root)

    i_root = sqrt_mod(-1, q, all_roots=False)
    if i_root is None:
        raise Stage5Partial(f"sqrt_mod(-1, {q}) unexpectedly returned None")
    roots["-1"] = int(i_root)
    return roots


def gs_check() -> dict[str, Any]:
    d = 5
    r_bound = 6
    d_sq_minus_4r = d * d - 4 * r_bound
    return {
        "d": d,
        "r_bound": r_bound,
        "d_sq_minus_4r": d_sq_minus_4r,
        "inequality_holds": d_sq_minus_4r > 0,
    }


def evaluate_prime(q: int) -> dict[str, Any]:
    progress("prime sweep", f"q={q}: computing roots and selected Stage-4 generators", force=True)
    roots = roots_for_prime(q)
    u_records = build_selected_u_records(q, roots)
    u_values = [record["u"] for record in u_records[:M]]
    points, unique_points, duplicate_count = build_points(u_values)
    n_points = len(unique_points)

    if duplicate_count == 0:
        exact_pairs = count_unit_pairs_by_ternary(u_values)
    else:
        exact_pairs = count_unit_pairs_direct(list(unique_points.keys()))

    guaranteed_edges = M * (2 ** (M - 1))
    bonus_edges = exact_pairs - guaranteed_edges
    l_t_layer_exercised = len(set(roots[str(d)] for d in D_VALUES)) == len(D_VALUES) and all(
        roots[str(d)] % q != 0 for d in D_VALUES
    )
    gs = gs_check()
    matches_guarantee = n_points == 2**M and exact_pairs == guaranteed_edges and bonus_edges == 0
    result = {
        "q": q,
        "roots_mod_q": roots,
        "m": M,
        "n_points": n_points,
        "guaranteed_edges": guaranteed_edges,
        "exact_unit_distance_pairs": exact_pairs,
        "bonus_edges": bonus_edges,
        "L_T_layer_exercised": l_t_layer_exercised,
        "matches_guarantee": matches_guarantee,
        "GS_check": gs,
    }
    progress(
        "prime sweep",
        f"q={q}: n={n_points}, exact_pairs={exact_pairs}, bonus={bonus_edges}",
        force=True,
    )
    return result


def base_output(splits_verified: dict[str, bool], validated: list[int], per_prime: list[dict[str, Any]]) -> dict[str, Any]:
    all_primes_match = bool(per_prime) and all(
        result["n_points"] == 2**M
        and result["exact_unit_distance_pairs"] == result["guaranteed_edges"]
        and result["bonus_edges"] == 0
        and result["L_T_layer_exercised"]
        and result["GS_check"]["inequality_holds"]
        for result in per_prime
    )

    enough_split_primes = len(validated) >= MIN_SPLIT_PRIME_COUNT and any(q != 101 for q in validated)
    if enough_split_primes and len(per_prime) >= MIN_SPLIT_PRIME_COUNT and all_primes_match:
        verdict = "PASS_SPLIT_PRIME_ROBUSTNESS"
    elif len(validated) < MIN_SPLIT_PRIME_COUNT:
        verdict = "PARTIAL_TOO_FEW_SPLIT_PRIMES_VERIFIED"
    elif not per_prime:
        verdict = "FAIL_NO_PRIME_RESULTS"
    elif not all_primes_match:
        verdict = "FAIL_PRIME_RESULT_MISMATCH"
    else:
        verdict = "PARTIAL_INSUFFICIENT_PRIME_RESULTS"

    return {
        "paper": "arXiv:2605.20695",
        "stage": "5 split-prime robustness sweep",
        "T": list(T_VALUES),
        "L_T": "Q(sqrt 5, sqrt 13, sqrt 17, sqrt 21, sqrt 33)",
        "candidate_primes": list(Q_CAND),
        "splits_verified": splits_verified,
        "splitting_validated_primes": validated,
        "per_prime_stage4_results": per_prime,
        "all_primes_match_guarantee": all_primes_match,
        "verdict": verdict,
    }


def write_output(output: dict[str, Any]) -> None:
    OUTPUT_PATH.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    if hasattr(signal, "SIGALRM"):
        signal.signal(signal.SIGALRM, _alarm_handler)
        signal.alarm(int(TIME_BUDGET_SECONDS) + 5)

    splits_verified: dict[str, bool] = {}
    validated: list[int] = []
    per_prime: list[dict[str, Any]] = []

    try:
        progress("split predicate", "checking candidate primes", force=True)
        for q in Q_CAND:
            ok = verify_splitting_predicate(q)
            splits_verified[str(q)] = ok
            if ok:
                validated.append(q)

        primes_to_run = validated[:TARGET_SPLIT_PRIME_COUNT]
        if len(primes_to_run) < MIN_SPLIT_PRIME_COUNT:
            raise Stage5Partial(f"only {len(primes_to_run)} split primes available for Stage-4 replication")

        for q in primes_to_run:
            check_budget(f"starting q={q}", reserve_seconds=120.0)
            per_prime.append(evaluate_prime(q))

    except Exception as exc:
        output = base_output(splits_verified, validated, per_prime)
        if not output["verdict"].startswith("FAIL"):
            reason = str(exc).replace(" ", "_")[:80] or exc.__class__.__name__
            output["verdict"] = f"PARTIAL_{reason}"
        write_output(output)
        print(f"Stage-5 wrote partial output to {OUTPUT_PATH}: {output['verdict']}", file=sys.stderr)
        if isinstance(exc, Stage5Partial):
            return 2
        raise

    output = base_output(splits_verified, validated, per_prime)
    write_output(output)
    print(f"Stage-5 wrote output to {OUTPUT_PATH}: {output['verdict']}", file=sys.stderr)
    return 0 if output["verdict"] == "PASS_SPLIT_PRIME_ROBUSTNESS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
