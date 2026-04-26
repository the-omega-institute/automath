#!/usr/bin/env python3
"""Audit signed companion collision-moment certificates.

This script reads the audited recurrence rows from the repository's generated
tables and uses the sync-kernel certificate, then computes:

* the q=2..23 Lucas/e2/signed-excess coincidence table;
* the q=2..23 exterior-Lucas certificate table;
* the q>=6 coincidence scan;
* the q=2..8 standard/signed determinant conversion identity.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[4]
GENERATED = (
    ROOT
    / "theory"
    / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    / "sections"
    / "generated"
)
RECURRENCE_TABLES = [
    GENERATED / "tab_fold_collision_moment_recursions.tex",
    GENERATED / "tab_fold_collision_moment_recursions_9_17.tex",
    GENERATED / "tab_fold_collision_moment_recursions_18_23.tex",
]
EXTERIOR_LUCAS_CERTIFICATE = (
    Path(__file__).resolve().parent / "exterior_lucas_certificate_q2_23.json"
)
ROW_RE = re.compile(r"^\s*(\d+)\s*&.*&\s*\(([-0-9,\s]+)\)\\\\")


def fib(n: int) -> int:
    if n < 0:
        raise ValueError("n must be nonnegative")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def lucas(q: int) -> int:
    return fib(q - 1) + fib(q + 1)


def recurrence_rows() -> dict[int, list[int]]:
    rows: dict[int, list[int]] = {}
    for table in RECURRENCE_TABLES:
        for line in table.read_text().splitlines():
            match = ROW_RE.match(line)
            if not match:
                continue
            q = int(match.group(1))
            coeffs = [int(part.strip()) for part in match.group(2).split(",")]
            rows[q] = coeffs
    missing = [q for q in range(2, 24) if q not in rows]
    if missing:
        raise RuntimeError(f"missing audited recurrence rows for q={missing}")
    return rows


def det_standard(coeffs: list[int]) -> int:
    return 1 - sum(coeffs)


def det_signed(coeffs: list[int]) -> int:
    return 1 + sum(coeffs)


def issue_excess_signed_proxy(q: int, coeffs: list[int]) -> int:
    return abs(det_signed(coeffs)) - fib(2 * (q - 1))


def output_subgraph_certificate() -> dict[str, Any]:
    states = [
        "000",
        "001",
        "002",
        "010",
        "100",
        "101",
        "0-12",
        "1-12",
        "01-1",
        "11-1",
    ]
    edges: list[tuple[str, str, int, int]] = []
    for d in (0, 1, 2):
        edges.append(("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(("100", f"00{d}", d, 1))
    edges += [
        ("001", "010", 0, 0),
        ("001", "100", 1, 0),
        ("001", "101", 2, 0),
        ("002", "11-1", 0, 0),
        ("002", "000", 1, 1),
        ("002", "001", 2, 1),
        ("010", "100", 0, 0),
        ("010", "101", 1, 0),
        ("010", "0-12", 2, 1),
        ("101", "010", 0, 1),
        ("101", "100", 1, 1),
        ("101", "101", 2, 1),
        ("0-12", "01-1", 0, 0),
        ("0-12", "010", 1, 0),
        ("0-12", "100", 2, 0),
        ("1-12", "01-1", 0, 1),
        ("1-12", "010", 1, 1),
        ("1-12", "100", 2, 1),
        ("01-1", "001", 0, 0),
        ("01-1", "002", 1, 0),
        ("01-1", "1-12", 2, 0),
        ("11-1", "001", 0, 1),
        ("11-1", "002", 1, 1),
        ("11-1", "1-12", 2, 1),
    ]
    by_output: dict[int, list[tuple[str, str, int]]] = {0: [], 1: []}
    self_loops: list[dict[str, int | str]] = []
    for src, dst, digit, output in edges:
        by_output[output].append((src, dst, digit))
        if src == dst:
            self_loops.append({"state": src, "input": digit, "output": output})

    def acyclic_after_deleting_self_loops(output: int) -> bool:
        graph: dict[str, list[str]] = {state: [] for state in states}
        for src, dst, _digit in by_output[output]:
            if src != dst:
                graph[src].append(dst)

        visiting: set[str] = set()
        done: set[str] = set()

        def dfs(state: str) -> bool:
            if state in visiting:
                return False
            if state in done:
                return True
            visiting.add(state)
            for nxt in graph[state]:
                if not dfs(nxt):
                    return False
            visiting.remove(state)
            done.add(state)
            return True

        return all(dfs(state) for state in states)

    return {
        "self_loops": self_loops,
        "output_0_acyclic_after_deleting_self_loops": acyclic_after_deleting_self_loops(0),
        "output_1_acyclic_after_deleting_self_loops": acyclic_after_deleting_self_loops(1),
        "trace_conclusion": (
            "For every q>=1, the histogram q-collision kernel has trace 2: "
            "the only diagonal histogram transitions are all q tracks on 000 "
            "with output 0 and all q tracks on 101 with output 1."
        ),
    }


def coincidence_table() -> list[dict[str, Any]]:
    rows = recurrence_rows()
    table: list[dict[str, Any]] = []
    for q in sorted(rows):
        coeffs = rows[q]
        e2 = int(coeffs[1])
        lq = lucas(q)
        excess = issue_excess_signed_proxy(q, coeffs)
        table.append(
            {
                "q": q,
                "e2": e2,
                "Lq": lq,
                "excess": excess,
                "e2_equals_Lq": e2 == lq,
                "excess_equals_Lq": excess == lq,
            }
        )
    return table


def exterior_lucas_certificate() -> list[dict[str, Any]]:
    rows = recurrence_rows()
    table: list[dict[str, Any]] = []
    for q in range(2, 24):
        coeffs = rows[q]
        c_q_2 = int(coeffs[1])
        lq = lucas(q)
        table.append(
            {
                "q": q,
                "c_{q,2}": c_q_2,
                "lucas(q)": lq,
                "match": c_q_2 == lq,
            }
        )
    true_rows = [row["q"] for row in table if row["match"]]
    if len(table) != 22 or true_rows != [3, 4, 5]:
        raise RuntimeError(
            "exterior-Lucas certificate failed: "
            f"row_count={len(table)}, true_rows={true_rows}"
        )
    return table


def determinant_conversion_table() -> list[dict[str, Any]]:
    rows = recurrence_rows()
    table: list[dict[str, Any]] = []
    for q in range(2, 9):
        coeffs = rows[q]
        det_std = det_standard(coeffs)
        det_sgn = det_signed(coeffs)
        table.append(
            {
                "q": q,
                "det_standard": det_std,
                "det_signed": det_sgn,
                "det_standard_plus_det_signed": det_std + det_sgn,
                "identity_holds": det_std == -det_sgn + 2,
            }
        )
    return table


def main() -> None:
    coincidences = coincidence_table()
    exterior_lucas = exterior_lucas_certificate()
    dets = determinant_conversion_table()
    exterior_lucas_payload = {
        "source": [str(path) for path in RECURRENCE_TABLES],
        "row_count": len(exterior_lucas),
        "true_q": [row["q"] for row in exterior_lucas if row["match"]],
        "rows": exterior_lucas,
    }
    EXTERIOR_LUCAS_CERTIFICATE.write_text(
        json.dumps(exterior_lucas_payload, indent=2, sort_keys=True) + "\n"
    )
    payload = {
        "source": [str(path) for path in RECURRENCE_TABLES],
        "coincidence_table_q2_23": coincidences,
        "exterior_lucas_certificate_path": str(EXTERIOR_LUCAS_CERTIFICATE),
        "exterior_lucas_true_q": exterior_lucas_payload["true_q"],
        "q_ge_6_e2_equals_Lq": [
            row["q"] for row in coincidences if row["q"] >= 6 and row["e2_equals_Lq"]
        ],
        "q_ge_6_excess_equals_Lq": [
            row["q"]
            for row in coincidences
            if row["q"] >= 6 and row["excess_equals_Lq"]
        ],
        "determinant_conversion_q2_8": dets,
        "determinant_identity_all_q2_8": all(row["identity_holds"] for row in dets),
        "sync_kernel_trace_certificate": output_subgraph_certificate(),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
