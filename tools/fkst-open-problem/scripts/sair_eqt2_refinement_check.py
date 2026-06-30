#!/usr/bin/env python3
"""Emit SAIR-EQT2 p13/p89 linear-magma refinement evidence.

This checker is deliberately narrow.  It replays the existing linear magma
search for the two-variable ETP equation subset at p=13 and p=89, compares the
complete distinct satisfaction-pattern sets, and appends one research_run-shaped
row to the sibling refinement artifact when requested.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
EQT_DIR = (
    REPO
    / "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    / "scripts/equational_theory"
)
LINEAR_MAGMA_SEARCH = EQT_DIR / "linear_magma_search.py"
DEFAULT_ARTIFACT = ROOT / "artifacts" / "sair-eqt2" / "research_refinement.jsonl"

EXPECTED_VAR2_EQUATIONS = 810
EXPECTED_COUNTS = {13: 129, 89: 263}
ACTION_ID = "linear-magma-refinement-vars2-p13-p89"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_json(payload: Any) -> str:
    encoded = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def load_linear_magma_search() -> Any:
    sys.path.insert(0, str(EQT_DIR))
    spec = importlib.util.spec_from_file_location("linear_magma_search", LINEAR_MAGMA_SEARCH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {LINEAR_MAGMA_SEARCH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["linear_magma_search"] = module
    spec.loader.exec_module(module)
    return module


def canonical_pattern_key(pattern: tuple[int, ...]) -> str:
    return ",".join(str(item) for item in pattern)


def pattern_summary(
    *,
    prime: int,
    result: dict[str, Any],
    patterns: set[tuple[int, ...]],
) -> dict[str, Any]:
    expected = EXPECTED_COUNTS[prime]
    observed = len(patterns)
    return {
        "prime": prime,
        "coefficients_tested": result.get("coefficients_tested"),
        "equations_checked": result.get("equations_checked"),
        "max_variables": result.get("max_variables"),
        "distinct_satisfaction_patterns": result.get("distinct_satisfaction_patterns"),
        "captured_pattern_count": observed,
        "expected_distinct_satisfaction_patterns": expected,
        "matches_expected_distinct_satisfaction_patterns": observed == expected,
        "elapsed_seconds": result.get("elapsed_seconds"),
    }


def build_row(example_limit: int) -> dict[str, Any]:
    linear_magma_search = load_linear_magma_search()
    started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    start = time.perf_counter()

    equations, source_info = linear_magma_search.load_equations()
    selected = linear_magma_search.equations_with_var_bound(equations, 2)
    selected_ids = tuple(equation.number for equation in selected)
    if len(selected_ids) != EXPECTED_VAR2_EQUATIONS:
        raise RuntimeError(
            f"vars2 equation count mismatch: got {len(selected_ids)}, "
            f"expected {EXPECTED_VAR2_EQUATIONS}"
        )

    command_parameters = {
        "primes": [13, 89],
        "max_variables": 2,
        "pattern_detail_limit": 0,
        "pattern_capture": "complete returned pattern set from linear_magma_search.run_prime",
        "canonical_key": "comma-separated satisfied ETP equation numbers within vars<=2 universe",
        "example_limit": example_limit,
    }

    p13_result, p13_patterns = linear_magma_search.run_prime(13, equations, 2, 0)
    p89_result, p89_patterns = linear_magma_search.run_prime(89, equations, 2, 0)

    p13_keys = sorted(canonical_pattern_key(pattern) for pattern in p13_patterns)
    p89_keys = sorted(canonical_pattern_key(pattern) for pattern in p89_patterns)
    p13_key_set = set(p13_keys)
    p89_key_set = set(p89_keys)
    intersection_keys = p13_key_set & p89_key_set
    p89_only_keys = sorted(p89_key_set - p13_key_set)
    p13_only_keys = sorted(p13_key_set - p89_key_set)

    sanity = {
        "expected": {"p13": EXPECTED_COUNTS[13], "p89": EXPECTED_COUNTS[89]},
        "observed": {"p13": len(p13_patterns), "p89": len(p89_patterns)},
        "matches_expected": (
            len(p13_patterns) == EXPECTED_COUNTS[13]
            and len(p89_patterns) == EXPECTED_COUNTS[89]
        ),
    }
    if not sanity["matches_expected"]:
        sanity["mismatch"] = {
            "p13_delta": len(p13_patterns) - EXPECTED_COUNTS[13],
            "p89_delta": len(p89_patterns) - EXPECTED_COUNTS[89],
        }

    source = {
        "equation_source": source_info,
        "linear_magma_search_path": str(LINEAR_MAGMA_SEARCH.relative_to(REPO)),
        "linear_magma_search_sha256": sha256_file(LINEAR_MAGMA_SEARCH),
    }
    equation_universe = {
        "description": "ETP equations with at most two variables",
        "equations_checked": len(selected_ids),
        "expected_equations_checked": EXPECTED_VAR2_EQUATIONS,
        "equation_numbers_sha256": sha256_json(selected_ids),
    }
    refinement_comparison = {
        "p13_pattern_count": len(p13_patterns),
        "p89_pattern_count": len(p89_patterns),
        "intersection_count": len(intersection_keys),
        "p89_only_count": len(p89_only_keys),
        "p13_only_count": len(p13_only_keys),
    }
    digest_payload = {
        "schema": "omega.research_run.v1",
        "target": "SAIR-EQT2",
        "run_id": "sair-eqt2-research-refinement-v1",
        "candidate_action_id": ACTION_ID,
        "checker_name": "sair_eqt2_refinement_check.py",
        "command_parameters": command_parameters,
        "source": source,
        "equation_universe": equation_universe,
        "prime_pattern_sets": {
            "p13": {
                "prime": 13,
                "distinct_satisfaction_patterns": len(p13_keys),
                "canonical_pattern_keys": p13_keys,
            },
            "p89": {
                "prime": 89,
                "distinct_satisfaction_patterns": len(p89_keys),
                "canonical_pattern_keys": p89_keys,
            },
        },
        "refinement_comparison": refinement_comparison,
    }

    evidence_base = {
        "refinement_comparison": {
            **refinement_comparison,
            "p89_only_example_canonical_keys": p89_only_keys[:example_limit],
        },
        "command_parameters": command_parameters,
        "source": source,
        "equation_universe": equation_universe,
        "prime_results": {
            "p13": pattern_summary(prime=13, result=p13_result, patterns=p13_patterns),
            "p89": pattern_summary(prime=89, result=p89_result, patterns=p89_patterns),
        },
        "sanity": sanity,
        "elapsed_seconds": round(time.perf_counter() - start, 6),
    }
    evidence = dict(evidence_base)
    evidence["output_sha256"] = sha256_json(digest_payload)

    checker_status = "checked" if sanity["matches_expected"] else "error"
    return {
        "schema": "omega.research_run.v1",
        "target": "SAIR-EQT2",
        "run_id": "sair-eqt2-research-refinement-v1",
        "state": "checker-ran",
        "claim_scope": "automation-research-evidence-not-proof",
        "candidate_action_id": ACTION_ID,
        "candidate_hypothesis": (
            "Compare complete p=13 and p=89 two-variable linear-magma "
            "satisfaction-pattern collections."
        ),
        "candidate_source": "manual-refinement-check",
        "candidate_frequency": "manual",
        "checker_name": "sair_eqt2_refinement_check.py",
        "checker_exit_code": 0 if checker_status == "checked" else 2,
        "checker_status": checker_status,
        "summary": (
            "Deterministic linear-magma replay compared complete p=13 and p=89 "
            "two-variable satisfaction-pattern collections."
        ),
        "evidence": evidence,
        "must_not_claim": [
            "FKST consensus as proof",
            "SAIR-EQT2 accepted",
            "new theorem",
        ],
        "run_started": started,
        "run_finished": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }


def append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row, separators=(",", ":"), sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true", help="append the row to the sibling artifact")
    parser.add_argument("--output", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--example-limit", type=int, default=50)
    args = parser.parse_args()

    row = build_row(args.example_limit)
    print(json.dumps(row, separators=(",", ":"), sort_keys=True))
    if args.emit:
        append_jsonl(args.output, row)
    return 0 if row.get("checker_status") == "checked" else 2


if __name__ == "__main__":
    raise SystemExit(main())
