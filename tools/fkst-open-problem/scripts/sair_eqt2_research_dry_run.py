#!/usr/bin/env python3
"""Generate the SAIR-EQT2 checker-backed research_run artifact.

This is the non-GitHub-write dry-run companion to the FKST research departments.
It runs the deterministic checker and writes one target-specific JSONL row.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
CHECKER = ROOT / "scripts" / "sair_eqt2_research_check.py"
RESEARCH_ARTIFACT = ROOT / "artifacts" / "sair-eqt2" / "research_run.jsonl"

DEFAULT_CANDIDATE = {
    "action_id": "coefficient-analysis-baseline",
    "state": "candidate-generated",
    "hypothesis": "Check local coefficient analysis baseline before submission claims.",
    "checker_plan": "Run coefficient_analysis.py --no-scan.",
    "expected_artifact": "Checker-backed research_run row.",
}
PORTFOLIO_CANDIDATES = [
    DEFAULT_CANDIDATE,
    {
        "action_id": "claim-boundary-audit",
        "state": "candidate-generated",
        "hypothesis": "Audit SAIR-EQT2 artifacts for target scope and prohibited proof/submission claims.",
        "checker_plan": "Parse claim_state.jsonl and research_run.jsonl for boundary violations.",
        "expected_artifact": "Boundary audit row proving the automation output remains claim-safe.",
        "frequency": "default",
        "source": "deterministic-portfolio",
    },
    {
        "action_id": "linear-magma-smoke",
        "state": "candidate-generated",
        "hypothesis": "Run a bounded linear magma smoke check.",
        "checker_plan": "Run linear_magma_search.py with a short timeout.",
        "expected_artifact": "Smoke-check row with status or timeout.",
        "frequency": "low-frequency",
        "source": "deterministic-portfolio",
    },
    {
        "action_id": "linear-magma-shard-vars1-p13",
        "state": "candidate-generated",
        "hypothesis": "Run a bounded p=13 linear-magma shard over local one-variable ETP laws.",
        "checker_plan": "Run linear_magma_search.py with max_vars_p13=1 and bounded baseline primes.",
        "expected_artifact": "Checker-backed search row with local 4694-equation source and p=13 pattern evidence.",
        "frequency": "default",
        "source": "deterministic-portfolio",
    },
    {
        "action_id": "linear-magma-shard-vars2-p13",
        "state": "candidate-generated",
        "hypothesis": "Run a bounded p=13 linear-magma shard over local two-variable ETP laws.",
        "checker_plan": "Run linear_magma_search.py with max_vars_p13=2 and bounded baseline primes.",
        "expected_artifact": "Checker-backed search row with two-variable p=13 pattern evidence.",
        "frequency": "default",
        "source": "deterministic-portfolio",
    },
    {
        "action_id": "linear-magma-shard-vars1-p89",
        "state": "candidate-generated",
        "hypothesis": "Run a bounded p=89 linear-magma shard over local one-variable ETP laws.",
        "checker_plan": "Run linear_magma_search.py with max_vars_p89=1 and bounded baseline primes.",
        "expected_artifact": "Checker-backed search row with p=89 one-variable pattern evidence.",
        "frequency": "default",
        "source": "deterministic-portfolio",
    },
    {
        "action_id": "linear-magma-shard-vars2-p89",
        "state": "candidate-generated",
        "hypothesis": "Run a bounded p=89 linear-magma shard over local two-variable ETP laws.",
        "checker_plan": "Run linear_magma_search.py with max_vars_p89=2 and bounded baseline primes.",
        "expected_artifact": "Checker-backed search row with p=89 two-variable pattern evidence.",
        "frequency": "default",
        "source": "deterministic-portfolio",
    },
]


def run_checker(candidate: dict[str, Any]) -> dict[str, Any]:
    return run_checker_with_env(candidate, {})


def run_checker_with_env(candidate: dict[str, Any], extra_env: dict[str, str]) -> dict[str, Any]:
    env = os.environ.copy()
    env.update(extra_env)
    completed = subprocess.run(
        [
            sys.executable,
            str(CHECKER),
            "--candidate-json",
            json.dumps(candidate, sort_keys=True),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=900,
        check=False,
        env=env,
    )
    if completed.returncode != 0:
        raise SystemExit(
            "research checker process failed: "
            f"exit={completed.returncode} stderr={completed.stderr[:1000]}"
        )
    try:
        payload = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"research checker returned invalid JSON: {exc}") from exc
    if payload.get("target") != "SAIR-EQT2":
        raise SystemExit("research checker returned out-of-scope target")
    return payload


def stable_evidence(checker: dict[str, Any]) -> dict[str, Any]:
    evidence = checker.get("summary", {}).get("evidence")
    if isinstance(evidence, dict):
        return evidence
    coefficient = checker.get("summary", {}).get("coefficient_analysis", {})
    keys = [
        "equation_count",
        "matches_expected_count",
        "max_coefficient_polynomial_degree",
        "max_abs_integer_coefficient_in_term_coefficients",
        "max_abs_integer_coefficient_in_difference_polynomials",
        "critical_content_prime",
    ]
    return {key: coefficient.get(key) for key in keys}


def render_row(candidate: dict[str, Any], checker: dict[str, Any]) -> dict[str, Any]:
    evidence = stable_evidence(checker)
    return {
        "schema": "omega.research_run.v1",
        "target": "SAIR-EQT2",
        "run_id": "sair-eqt2-research-v1",
        "state": "checker-ran",
        "claim_scope": "automation-research-evidence-not-proof",
        "candidate_action_id": candidate.get("action_id"),
        "candidate_hypothesis": candidate.get("hypothesis"),
        "candidate_source": candidate.get("source", "manual-dry-run"),
        "candidate_frequency": candidate.get("frequency", "default"),
        "checker_name": checker.get("checker_name"),
        "checker_exit_code": checker.get("exit_code"),
        "checker_status": checker.get("status"),
        "summary": checker.get("summary", {}).get("text"),
        "evidence": evidence,
        "must_not_claim": [
            "FKST consensus as mathematical proof",
            "SAIR-EQT2 submission accepted",
            "new theorem beyond Lean/checker/source artifacts",
        ],
    }


def validate_row(row: dict[str, Any]) -> None:
    if row.get("target") != "SAIR-EQT2":
        raise SystemExit("research artifact target must be SAIR-EQT2")
    if row.get("checker_status") not in {"checked", "timeout"}:
        raise SystemExit("research checker did not reach checked status")
    evidence = row.get("evidence", {})
    if row.get("candidate_action_id") == "coefficient-analysis-baseline":
        if evidence.get("equation_count") != 4694:
            raise SystemExit("research evidence must record 4694 ETP equations")
        if evidence.get("matches_expected_count") is not True:
            raise SystemExit("research evidence must match expected ETP equation count")
    blocked_terms = ("Israel", "Tolmetes", "omega-open-problem")
    encoded = json.dumps(row, sort_keys=True)
    for term in blocked_terms:
        if term in encoded:
            raise SystemExit(f"out-of-scope term in research artifact: {term}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=RESEARCH_ARTIFACT)
    parser.add_argument(
        "--include-low-frequency",
        action="store_true",
        help="Also run low-frequency smoke checks that may time out.",
    )
    args = parser.parse_args()

    candidates = [
        item for item in PORTFOLIO_CANDIDATES
        if args.include_low_frequency or item.get("frequency") != "low-frequency"
    ]
    audit_candidates = [item for item in candidates if item.get("action_id") == "claim-boundary-audit"]
    checker_candidates = [item for item in candidates if item.get("action_id") != "claim-boundary-audit"]

    rows = []
    for candidate in checker_candidates:
        checker = run_checker(candidate)
        row = render_row(candidate, checker)
        validate_row(row)
        rows.append(row)

    with tempfile.TemporaryDirectory(prefix="sair-eqt2-research-dry-run-") as temp_dir:
        generated_research = Path(temp_dir) / "research_run.generated.jsonl"
        generated_research.write_text(
            "".join(json.dumps(row, separators=(",", ":"), sort_keys=True) + "\n" for row in rows),
            encoding="utf-8",
        )
        for candidate in audit_candidates:
            checker = run_checker_with_env(
                candidate,
                {"SAIR_EQT2_RESEARCH_RUN": str(generated_research)},
            )
            row = render_row(candidate, checker)
            validate_row(row)
            rows.insert(1, row)

    text = "".join(json.dumps(row, separators=(",", ":"), sort_keys=True) + "\n" for row in rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    print(f"target: SAIR-EQT2")
    print(f"generated: {args.output}")
    print(f"rows: {len(rows)}")
    for row in rows:
        print(f"{row['candidate_action_id']}: {row['checker_status']}")
    print("github_write: disabled")


if __name__ == "__main__":
    main()
