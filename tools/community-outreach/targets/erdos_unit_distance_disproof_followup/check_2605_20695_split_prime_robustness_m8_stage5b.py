#!/usr/bin/env python3
"""Stage-5b split-prime robustness sweep for arXiv:2605.20695.

This checker extends the Stage-5 split-prime robustness sweep from m=6 to
m=8.  The Stage-4 script in this checkout is
``check_2605_20695_CRT_translation_stage4.py``; its generator order is the
lexicographic order on ``itertools.product((-1, 1), repeat=5)``, its m-point
selection is the first m constructed u_eps values, and its exact pair count
uses ternary difference patterns when the additive cube has no duplicates.
Those choices are mirrored here for m=8 at the four Stage-5 split primes.
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
OUTPUT_PATH = TARGET_DIR / "check_2605_20695_split_prime_robustness_m8_stage5b_output.json"

T_VALUES = (3, 5, 7, 11, 13, 17)
D_VALUES = (5, 13, 17, 21, 33)
PRIMES = (101, 1361, 1889, 2141)
FIELD_DEGREE = 64
M = 8
PROGRESS_INTERVAL_SECONDS = 20.0
TIME_BUDGET_SECONDS = 20.0 * 60.0
PER_PRIME_TIMEOUT_SECONDS = 5.0 * 60.0
F0 = Fraction(0)
F1 = Fraction(1)

_START = time.monotonic()
_LAST_PROGRESS = 0.0


class Stage5bPartial(RuntimeError):
    """Raised when the checker must write a partial JSON result."""


class Stage5bPrimeTimeout(RuntimeError):
    """Raised when a single prime exceeds its allowed wallclock budget."""


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
        raise Stage5bPartial(
            f"time budget guard during {context}: "
            f"elapsed={elapsed_seconds():.3f}s, reserve={reserve_seconds:.3f}s, "
            f"budget={TIME_BUDGET_SECONDS:.3f}s"
        )


def _alarm_handler(signum: int, frame: object) -> None:
    raise Stage5bPrimeTimeout("single-prime timeout fired")


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
            raise Stage5bPartial(f"sqrt_mod({d}, {q}) unexpectedly returned None")
        roots[str(d)] = int(root)

    i_root = sqrt_mod(-1, q, all_roots=False)
    if i_root is None:
        raise Stage5bPartial(f"sqrt_mod(-1, {q}) unexpectedly returned None")
    roots["-1"] = int(i_root)
    return roots


def evaluate_prime(q: int) -> dict[str, Any]:
    progress("prime sweep", f"q={q}: computing roots and selected Stage-4 generators", force=True)
    build_start = time.monotonic()
    roots = roots_for_prime(q)
    u_records = build_selected_u_records(q, roots)
    u_values = [record["u"] for record in u_records[:M]]
    points, unique_points, duplicate_count = build_points(u_values)
    n_points = len(unique_points)
    build_time_sec = time.monotonic() - build_start

    pair_count_start = time.monotonic()
    if duplicate_count == 0:
        exact_pairs = count_unit_pairs_by_ternary(u_values)
    else:
        exact_pairs = count_unit_pairs_direct(list(unique_points.keys()))
    pair_count_time_sec = time.monotonic() - pair_count_start

    guaranteed_edges = M * (2 ** (M - 1))
    bonus_edges = exact_pairs - guaranteed_edges
    result = {
        "n_points": n_points,
        "edges_total": exact_pairs,
        "guaranteed": guaranteed_edges,
        "bonus_edges": bonus_edges,
        "sqrt_minus_one_root": roots["-1"],
        "build_time_sec": round(build_time_sec, 6),
        "pair_count_time_sec": round(pair_count_time_sec, 6),
    }
    progress(
        "prime sweep",
        f"q={q}: n={n_points}, exact_pairs={exact_pairs}, bonus={bonus_edges}",
        force=True,
    )
    return result


def timeout_result(note: str) -> dict[str, Any]:
    return {
        "n_points": None,
        "edges_total": None,
        "guaranteed": M * (2 ** (M - 1)),
        "bonus_edges": None,
        "sqrt_minus_one_root": None,
        "build_time_sec": None,
        "pair_count_time_sec": None,
        "timeout": note,
    }


def base_output(per_prime: dict[str, dict[str, Any]]) -> dict[str, Any]:
    expected_n = 2**M
    guaranteed_edges = M * (2 ** (M - 1))
    timed_out = [q for q in PRIMES if per_prime.get(str(q), {}).get("timeout")]
    all_primes_match = len(per_prime) == len(PRIMES) and all(
        per_prime[str(q)].get("n_points") == expected_n
        and per_prime[str(q)].get("edges_total") == guaranteed_edges
        and per_prime[str(q)].get("bonus_edges") == 0
        for q in PRIMES
    )
    return {
        "stage": "5b split-prime robustness sweep m=8",
        "m": M,
        "n_points_expected": expected_n,
        "guaranteed_edges_per_prime": guaranteed_edges,
        "primes": list(PRIMES),
        "per_prime": per_prime,
        "timed_out_primes": timed_out,
        "verdict": "PASS" if all_primes_match and not timed_out else "FAIL",
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }


def write_output(output: dict[str, Any]) -> None:
    OUTPUT_PATH.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_prime_with_timeout(q: int) -> dict[str, Any]:
    if not verify_splitting_predicate(q):
        return timeout_result("prime failed the split predicate before evaluation")

    if hasattr(signal, "SIGALRM"):
        signal.alarm(int(PER_PRIME_TIMEOUT_SECONDS))

    try:
        check_budget(f"starting q={q}", reserve_seconds=15.0)
        return evaluate_prime(q)
    except Stage5bPrimeTimeout:
        progress("prime sweep", f"q={q}: timeout after {PER_PRIME_TIMEOUT_SECONDS:.0f}s", force=True)
        return timeout_result(f"single-prime timeout after {PER_PRIME_TIMEOUT_SECONDS:.0f} seconds")
    finally:
        if hasattr(signal, "SIGALRM"):
            signal.alarm(0)


def main() -> int:
    if hasattr(signal, "SIGALRM"):
        signal.signal(signal.SIGALRM, _alarm_handler)

    per_prime: dict[str, dict[str, Any]] = {}

    try:
        progress("split predicate", "checking fixed Stage-5b primes", force=True)
        for q in PRIMES:
            if elapsed_seconds() >= TIME_BUDGET_SECONDS:
                per_prime[str(q)] = timeout_result("global 20 minute wallclock budget exhausted before this prime")
                continue
            per_prime[str(q)] = run_prime_with_timeout(q)
            write_output(base_output(per_prime))

    except Stage5bPartial as exc:
        for q in PRIMES:
            if str(q) not in per_prime:
                per_prime[str(q)] = timeout_result(str(exc))
    except Exception as exc:
        for q in PRIMES:
            if str(q) not in per_prime:
                per_prime[str(q)] = timeout_result(f"evaluation error: {exc.__class__.__name__}: {exc}")
        output = base_output(per_prime)
        write_output(output)
        print(f"Stage-5b wrote failure output to {OUTPUT_PATH}: {output['verdict']}", file=sys.stderr)
        raise

    output = base_output(per_prime)
    write_output(output)
    print(f"Stage-5b wrote output to {OUTPUT_PATH}: {output['verdict']}", file=sys.stderr)
    return 0 if output["verdict"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
