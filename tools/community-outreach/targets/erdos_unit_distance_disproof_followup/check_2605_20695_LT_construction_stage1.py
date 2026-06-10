#!/usr/bin/env python3
"""Stage-1 verification artifact for arXiv:2605.20695.

This script deliberately uses Python's standard library only. It verifies the
small multiquadratic and Legendre-symbol checks that do not require algebraic
number theory infrastructure, then records the class-field-theory gap honestly.
"""

from __future__ import annotations

import datetime as _datetime
import json
import math
import os
import signal
import time
from typing import Dict, List, Sequence, Tuple


TIME_BUDGET_SECONDS = 20 * 60
PROGRESS_INTERVAL_SECONDS = 20
PAPER = "arXiv:2605.20695"
GENERATORS = [5, 13, 17, 21, 33]
VECTOR_PRIMES = [3, 5, 7, 11, 13, 17]
SPLITTING_PRIME = 101
OUTPUT_NAME = "check_2605_20695_LT_construction_stage1_output.json"


class VerificationAbort(RuntimeError):
    """Raised when the script exceeds its Stage-1 runtime budget."""


_START_MONOTONIC = time.monotonic()
_LAST_PROGRESS = 0.0


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    """Print timestamped progress, throttled to keep gaps below 20 seconds."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        _LAST_PROGRESS = now


def check_time_budget(context: str) -> None:
    elapsed = time.monotonic() - _START_MONOTONIC
    if elapsed > TIME_BUDGET_SECONDS:
        raise VerificationAbort(
            f"INSUFFICIENT_INFRASTRUCTURE: time budget exceeded during {context}; "
            f"elapsed_seconds={elapsed:.3f}, budget_seconds={TIME_BUDGET_SECONDS}"
        )


def _alarm_handler(signum, frame) -> None:  # type: ignore[no-untyped-def]
    raise VerificationAbort(
        "INSUFFICIENT_INFRASTRUCTURE: global 20-minute alarm fired before Stage-1 completed"
    )


def prime_factorization(n: int) -> Dict[int, int]:
    if n == 0:
        raise ValueError("0 has no squarefree part in Q*/(Q*)^2")
    n_abs = abs(n)
    factors: Dict[int, int] = {}
    d = 2
    while d * d <= n_abs:
        while n_abs % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n_abs //= d
        d += 1 if d == 2 else 2
    if n_abs > 1:
        factors[n_abs] = factors.get(n_abs, 0) + 1
    if n < 0:
        factors[-1] = factors.get(-1, 0) + 1
    return factors


def squarefree_part(n: int) -> int:
    factors = prime_factorization(n)
    result = 1
    for prime, exponent in sorted(factors.items(), key=lambda item: item[0]):
        if exponent % 2:
            result *= prime
    return result


def exponent_vector_mod2(n: int, primes: Sequence[int]) -> List[int]:
    factors = prime_factorization(squarefree_part(n))
    return [factors.get(prime, 0) % 2 for prime in primes]


def f2_rank_and_basis(rows: Sequence[Sequence[int]]) -> Tuple[int, List[List[int]], List[int]]:
    """Return rank, pivot-normalized basis rows, and pivot columns over F_2."""
    matrix = [list(row) for row in rows]
    if not matrix:
        return 0, [], []

    row_count = len(matrix)
    col_count = len(matrix[0])
    pivot_row = 0
    pivots: List[int] = []

    for col in range(col_count):
        pivot = None
        for row in range(pivot_row, row_count):
            if matrix[row][col] % 2:
                pivot = row
                break
        if pivot is None:
            continue

        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        for row in range(row_count):
            if row != pivot_row and matrix[row][col] % 2:
                matrix[row] = [(a ^ b) for a, b in zip(matrix[row], matrix[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break

    basis = [matrix[row] for row in range(pivot_row)]
    return pivot_row, basis, pivots


def legendre_symbol(a: int, p: int) -> int:
    if p == 2 or p < 2:
        raise ValueError("Euler-criterion Legendre symbol requires an odd prime p")
    residue = a % p
    if residue == 0:
        return 0
    value = pow(residue, (p - 1) // 2, p)
    if value == 1:
        return 1
    if value == p - 1:
        return -1
    raise ValueError(f"unexpected Euler-criterion value {value} for ({a}/{p})")


def verify_degree() -> Dict[str, object]:
    progress("STEP 1: computing squarefree exponent vectors and F_2 rank", force=True)
    check_time_budget("degree verification")

    squarefree_generators = [squarefree_part(n) for n in GENERATORS]
    vectors = [exponent_vector_mod2(n, VECTOR_PRIMES) for n in squarefree_generators]
    rank, basis, pivots = f2_rank_and_basis(vectors)
    degree = 2**rank

    vector_records = []
    for generator, squarefree, vector in zip(GENERATORS, squarefree_generators, vectors):
        vector_records.append(
            {
                "generator": generator,
                "squarefree_part": squarefree,
                "prime_order": VECTOR_PRIMES,
                "vector_mod_2": vector,
            }
        )

    verified = rank == 5 and degree == 32
    progress(
        f"STEP 1 complete: F_2 rank={rank}, degree=2^{rank}={degree}, verified={verified}",
        force=True,
    )
    return {
        "squarefree_generators": squarefree_generators,
        "vector_primes": VECTOR_PRIMES,
        "vectors": vector_records,
        "rank": rank,
        "basis": basis,
        "pivot_columns": pivots,
        "degree": degree,
        "verified": verified,
    }


def verify_splitting() -> Dict[str, object]:
    progress("STEP 2: computing Legendre symbols for the 101 splitting check", force=True)
    check_time_budget("splitting verification")

    legendre = {str(a): legendre_symbol(a, SPLITTING_PRIME) for a in GENERATORS}
    all_qr = all(value == 1 for value in legendre.values())
    coprime_to_generators = all(math.gcd(SPLITTING_PRIME, a) == 1 for a in GENERATORS)
    p_odd = SPLITTING_PRIME % 2 == 1
    splits = bool(p_odd and coprime_to_generators and all_qr)

    reciprocity_cross_check = {
        str(q): legendre_symbol(SPLITTING_PRIME, q) for q in VECTOR_PRIMES
    }

    progress(
        f"STEP 2 complete: all generator Legendre symbols are +1? {all_qr}; "
        f"splits_completely={splits}",
        force=True,
    )
    return {
        "p": SPLITTING_PRIME,
        "legendre_symbols": legendre,
        "all_QR": all_qr,
        "p_odd": p_odd,
        "coprime_to_generators": coprime_to_generators,
        "splits_completely": splits,
        "reciprocity_cross_check_101_over_prime": reciprocity_cross_check,
    }


def verify_golod_shafarevich() -> Dict[str, object]:
    progress("STEP 3: checking Golod-Shafarevich numerical consequence", force=True)
    check_time_budget("Golod-Shafarevich verification")

    d_claimed = 5
    r_claimed_upper_bound = 6
    d_squared = d_claimed * d_claimed
    four_r = 4 * r_claimed_upper_bound
    inequality = d_squared > four_r
    infrastructure_gap = (
        "Computing d(G_T^S) and r(G_T^S) requires S-unit group + class field theory; "
        "out of stdlib Python scope. PARI/GP bnfinit/bnrclassfield or sage K.S_class_group needed."
    )

    progress(
        f"STEP 3 complete: using paper claims d={d_claimed}, r<={r_claimed_upper_bound}; "
        f"{d_squared}>{four_r} is {inequality}",
        force=True,
    )
    return {
        "d_claimed_by_paper": d_claimed,
        "r_claimed_by_paper": r_claimed_upper_bound,
        "d_squared": d_squared,
        "four_r": four_r,
        "d_squared_gt_4r": inequality,
        "infinite_tower_implied": inequality,
        "d_and_r_computed_from_scratch": False,
        "infrastructure_status": "INSUFFICIENT_INFRASTRUCTURE",
        "infrastructure_gap": infrastructure_gap,
    }


def build_verdict(degree_result: Dict[str, object], splitting_result: Dict[str, object], gs_result: Dict[str, object]) -> Tuple[Dict[str, str], str]:
    verdict_per_step = {
        "degree": "PASS" if degree_result["verified"] else "FAIL",
        "splitting_101": "PASS" if splitting_result["splits_completely"] else "FAIL",
        "golod_shafarevich_consequence": "PASS" if gs_result["d_squared_gt_4r"] else "FAIL",
        "d_and_r_from_scratch": "INSUFFICIENT_INFRASTRUCTURE",
    }

    if any(value == "FAIL" for value in verdict_per_step.values()):
        overall = "FAIL_WITH_INFRASTRUCTURE_NOTE"
    else:
        overall = "PASS_WITH_INFRASTRUCTURE_NOTE"
    return verdict_per_step, overall


def write_output(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    progress(f"STEP 4: writing JSON output to {output_path}", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def main() -> int:
    if hasattr(signal, "SIGALRM"):
        signal.signal(signal.SIGALRM, _alarm_handler)
        signal.alarm(TIME_BUDGET_SECONDS)

    progress("Starting Stage-1 verification for arXiv:2605.20695", force=True)
    try:
        degree_result = verify_degree()
        splitting_result = verify_splitting()
        gs_result = verify_golod_shafarevich()
        verdict_per_step, overall_verdict = build_verdict(degree_result, splitting_result, gs_result)

        discrepancy = None
        if not splitting_result["splits_completely"]:
            discrepancy = (
                "The direct Legendre-symbol check does not verify complete splitting of 101 "
                "for all listed generators. This may indicate a convention mismatch or a data issue."
            )

        output = {
            "paper": PAPER,
            "paper_citation": (
                "Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood. "
                "Remarks on the disproof of the unit distance conjecture. arXiv:2605.20695, May 2026."
            ),
            "stage": 1,
            "timestamp_utc": utc_now_iso(),
            "T": [3, 5, 7, 11, 13, 17],
            "S": [101, "infinity"],
            "L_T_generators_squarefree": degree_result["squarefree_generators"],
            "L_T_degree_over_Q": degree_result["degree"],
            "L_T_degree_verified": degree_result["verified"],
            "multiplicative_independence_basis": degree_result["basis"],
            "multiplicative_independence_details": {
                "prime_order": degree_result["vector_primes"],
                "generator_vectors": degree_result["vectors"],
                "rank_over_F2": degree_result["rank"],
                "pivot_columns": degree_result["pivot_columns"],
            },
            "p_splits_completely": {
                "p": splitting_result["p"],
                "legendre_symbols": splitting_result["legendre_symbols"],
                "all_QR": splitting_result["all_QR"],
                "splits_completely": splitting_result["splits_completely"],
            },
            "splitting_cross_checks": {
                "p_odd": splitting_result["p_odd"],
                "coprime_to_generators": splitting_result["coprime_to_generators"],
                "legendre_symbols_101_over_prime": splitting_result[
                    "reciprocity_cross_check_101_over_prime"
                ],
            },
            "golod_shafarevich": gs_result,
            "verdict_per_step": verdict_per_step,
            "overall_verdict": overall_verdict,
            "discrepancy": discrepancy,
            "runtime_seconds": round(time.monotonic() - _START_MONOTONIC, 6),
        }

        output_path = write_output(output)

        progress("STEP 5: printing final verdict and human-readable summary", force=True)
        print(f"VERDICT: {overall_verdict}")
        print(f"JSON_OUTPUT: {output_path}")
        print(
            "SUMMARY: Degree check PASS; 101 splitting check "
            f"{verdict_per_step['splitting_101']}; Golod-Shafarevich consequence PASS "
            "from the paper's claimed d=5 and r<=6. Direct computation of d(G_T^S) and "
            "r(G_T^S) is marked INSUFFICIENT_INFRASTRUCTURE because it requires S-unit "
            "and class-field-theory machinery outside Python stdlib."
        )
        if discrepancy:
            print(f"DISCREPANCY: {discrepancy}")
        else:
            print("DISCREPANCY: none found in the Stage-1 stdlib checks.")
        return 0 if not overall_verdict.startswith("FAIL") else 1
    except VerificationAbort as exc:
        output = {
            "paper": PAPER,
            "stage": 1,
            "timestamp_utc": utc_now_iso(),
            "overall_verdict": "INSUFFICIENT_INFRASTRUCTURE",
            "abort_reason": str(exc),
            "runtime_seconds": round(time.monotonic() - _START_MONOTONIC, 6),
        }
        output_path = write_output(output)
        print("VERDICT: INSUFFICIENT_INFRASTRUCTURE")
        print(f"JSON_OUTPUT: {output_path}")
        print(f"SUMMARY: {exc}")
        return 2
    finally:
        if hasattr(signal, "SIGALRM"):
            signal.alarm(0)


if __name__ == "__main__":
    raise SystemExit(main())
