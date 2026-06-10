#!/usr/bin/env python3
"""Stage-1 verification artifact for arXiv:2604.20970, Proposition 3.6.

This script deliberately uses Python's standard library only. It enumerates the
Fermat cubic Jacobian ring R = Z[x0,...,x4]/(x0^2,...,x4^2), computes ranks of
naive graded multiplication candidates, and records honestly whether any such
candidate realizes the paper's stated rank 50.
"""

from __future__ import annotations

import datetime as _datetime
from fractions import Fraction
import itertools
import json
import os
import signal
import time
from typing import Dict, Iterable, List, Sequence, Tuple


TIME_BUDGET_SECONDS = 20 * 60
PROGRESS_INTERVAL_SECONDS = 20
PAPER = "arXiv:2604.20970"
TARGET = "Proposition 3.6 Fermat cubic Jacobian ring cup-product rank"
OUTPUT_NAME = "check_2604_20970_fermat_jacobian_stage1_output.json"
VARIABLE_COUNT = 5
EXPECTED_HILBERT_SERIES = [1, 5, 10, 10, 5, 1]


class VerificationAbort(RuntimeError):
    """Raised when the script exceeds its Stage-1 runtime budget."""


_START_MONOTONIC = time.monotonic()
_LAST_PROGRESS = 0.0


Subset = Tuple[int, ...]
Matrix = List[List[int]]


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


def build_squarefree_bases(variable_count: int = VARIABLE_COUNT) -> Dict[int, List[Subset]]:
    bases: Dict[int, List[Subset]] = {}
    variables = range(variable_count)
    for degree in range(variable_count + 1):
        bases[degree] = [tuple(combo) for combo in itertools.combinations(variables, degree)]
    return bases


def multiply_squarefree(left: Subset, right: Subset) -> Subset | None:
    left_set = set(left)
    right_set = set(right)
    if left_set.intersection(right_set):
        return None
    return tuple(sorted(left_set.union(right_set)))


def build_multiplication_matrix(
    bases: Dict[int, List[Subset]],
    a: int,
    b: int,
) -> Matrix:
    """Rows index R_a tensor R_b; columns index R_{a+b}."""
    source_left = bases[a]
    source_right = bases[b]
    target = bases[a + b]
    target_index = {monomial: index for index, monomial in enumerate(target)}

    matrix: Matrix = []
    for left in source_left:
        for right in source_right:
            row = [0] * len(target)
            product = multiply_squarefree(left, right)
            if product is not None:
                row[target_index[product]] = 1
            matrix.append(row)
    return matrix


def rank_over_q(matrix: Sequence[Sequence[int]]) -> int:
    """Compute exact matrix rank over Q by Gaussian elimination with Fraction."""
    if not matrix:
        return 0
    row_count = len(matrix)
    col_count = len(matrix[0]) if matrix[0] else 0
    if col_count == 0:
        return 0

    work: List[List[Fraction]] = [[Fraction(entry) for entry in row] for row in matrix]
    pivot_row = 0

    for col in range(col_count):
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
            if row != pivot_row and work[row][col] != 0:
                factor = work[row][col]
                work[row] = [
                    entry - factor * pivot_entry
                    for entry, pivot_entry in zip(work[row], work[pivot_row])
                ]

        pivot_row += 1
        if pivot_row == row_count:
            break

    return pivot_row


def transpose(matrix: Sequence[Sequence[int]]) -> Matrix:
    if not matrix:
        return []
    return [list(row) for row in zip(*matrix)]


def build_phi_matrix(
    bases: Dict[int, List[Subset]],
    a: int,
    b: int,
) -> Matrix:
    """Rows index R_a; columns index Hom-basis coordinates R_b^* tensor R_{a+b}."""
    source = bases[a]
    right = bases[b]
    target = bases[a + b]
    target_index = {monomial: index for index, monomial in enumerate(target)}
    column_count = len(right) * len(target)

    matrix: Matrix = []
    for left in source:
        row = [0] * column_count
        for right_index, right_monomial in enumerate(right):
            product = multiply_squarefree(left, right_monomial)
            if product is not None:
                col = right_index * len(target) + target_index[product]
                row[col] = 1
        matrix.append(row)
    return matrix


def matrix_rank_candidate(
    bases: Dict[int, List[Subset]],
    a: int,
    b: int,
    kind: str,
) -> Dict[str, int | str]:
    if kind == "mul":
        matrix = build_multiplication_matrix(bases, a, b)
        source_dim = len(bases[a]) * len(bases[b])
        target_dim = len(bases[a + b])
    elif kind == "phi":
        matrix = build_phi_matrix(bases, a, b)
        source_dim = len(bases[a])
        target_dim = len(bases[b]) * len(bases[a + b])
    else:
        raise ValueError(f"unknown candidate kind: {kind}")

    return {
        "a": a,
        "b": b,
        "source_dim": source_dim,
        "target_dim": target_dim,
        "rank": rank_over_q(matrix),
        "kind": kind,
    }


def ordered_degree_pairs() -> Iterable[Tuple[int, int]]:
    for a in range(VARIABLE_COUNT + 1):
        for b in range(VARIABLE_COUNT + 1):
            if a + b <= VARIABLE_COUNT:
                yield a, b


def compute_candidate_table(bases: Dict[int, List[Subset]]) -> List[Dict[str, int | str]]:
    table: List[Dict[str, int | str]] = []
    progress("STEP 2: computing all ordered multiplication and phi candidate ranks", force=True)
    for a, b in ordered_degree_pairs():
        check_time_budget(f"candidate rank computation for ({a},{b})")
        table.append(matrix_rank_candidate(bases, a, b, "mul"))
        table.append(matrix_rank_candidate(bases, a, b, "phi"))
    return table


def format_candidate_summary(candidate_table: Sequence[Dict[str, int | str]]) -> str:
    lines = []
    for candidate in candidate_table:
        lines.append(
            "  "
            f"{candidate['kind']} "
            f"({candidate['a']},{candidate['b']}): "
            f"source_dim={candidate['source_dim']}, "
            f"target_dim={candidate['target_dim']}, "
            f"rank={candidate['rank']}"
        )
    return "\n".join(lines)


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

    progress("Starting Stage-1 Fermat Jacobian-ring check for arXiv:2604.20970", force=True)
    try:
        progress("STEP 1: building squarefree monomial bases for R", force=True)
        bases = build_squarefree_bases()
        hilbert_series = [len(bases[degree]) for degree in range(VARIABLE_COUNT + 1)]
        print(f"HILBERT_SERIES: {hilbert_series}", flush=True)
        assert hilbert_series == EXPECTED_HILBERT_SERIES, (
            f"unexpected Hilbert series {hilbert_series}; expected {EXPECTED_HILBERT_SERIES}"
        )

        candidate_table = compute_candidate_table(bases)

        progress("STEP 3: checking specific R_2 tensor R_2 -> R_4 Macaulay/Koszul candidate", force=True)
        r2r2_candidates = [
            candidate
            for candidate in candidate_table
            if candidate["kind"] == "mul" and candidate["a"] == 2 and candidate["b"] == 2
        ]
        r2_tensor_r2_to_r4_rank = r2r2_candidates[0]["rank"] if r2r2_candidates else None

        hit_rank_50 = [candidate for candidate in candidate_table if candidate["rank"] == 50]
        verdict = "PASS_HIT_50" if hit_rank_50 else "INCONCLUSIVE_NEED_PDF_DEEP_READ"
        if hit_rank_50:
            notes = (
                "At least one naive ordered graded multiplication or phi-form candidate "
                "has exact rank 50 over Q in the Fermat Jacobian ring."
            )
        else:
            notes = (
                "No naive ordered graded multiplication R_a tensor R_b -> R_{a+b} or "
                "phi-form candidate in the squarefree Fermat Jacobian ring has rank 50. "
                "Proposition 3.6's mu is more specific than the naive graded multiplication "
                "R_a tensor R_b -> R_{a+b}; needs section 3 PDF deep-read."
            )

        output = {
            "paper": PAPER,
            "paper_citation": (
                "D. Litt, T. Kramer, G. Maculan. E6 local systems from cubic threefolds. "
                "arXiv:2604.20970, 2026."
            ),
            "stage": 1,
            "timestamp_utc": utc_now_iso(),
            "target": TARGET,
            "fermat_cubic": "F = x0^3 + x1^3 + x2^3 + x3^3 + x4^3",
            "jacobian_ideal": ["x0^2", "x1^2", "x2^2", "x3^2", "x4^2"],
            "hilbert_series": hilbert_series,
            "total_dimension": sum(hilbert_series),
            "candidate_table": candidate_table,
            "macaulay_koszul_candidate": {
                "description": "R_2 tensor R_2 -> R_4",
                "rank": r2_tensor_r2_to_r4_rank,
            },
            "hit_rank_50": hit_rank_50,
            "verdict": verdict,
            "notes": notes,
            "runtime_seconds": round(time.monotonic() - _START_MONOTONIC, 6),
        }

        output_path = write_output(output)

        progress("STEP 5: printing final verdict and candidate summary", force=True)
        print(f"VERDICT: {verdict}")
        print(f"JSON_OUTPUT: {output_path}")
        print(f"HIT_RANK_50: {hit_rank_50}")
        print("CANDIDATE_TABLE_SUMMARY:")
        print(format_candidate_summary(candidate_table))
        print(f"R2_TENSOR_R2_TO_R4_RANK: {r2_tensor_r2_to_r4_rank}")
        print(f"NOTES: {notes}")
        return 0
    except VerificationAbort as exc:
        output = {
            "paper": PAPER,
            "stage": 1,
            "timestamp_utc": utc_now_iso(),
            "target": TARGET,
            "verdict": "INSUFFICIENT_INFRASTRUCTURE",
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
