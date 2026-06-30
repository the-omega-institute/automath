#!/usr/bin/env python3
"""Run one SAIR-EQT2 research checker step for FKST dogfooding.

This script is deliberately target-specific. Codex may propose a candidate
action, but this script records only deterministic checker output as evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
COEFFICIENT_ANALYSIS = (
    REPO
    / "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    / "scripts/equational_theory/coefficient_analysis.py"
)
LINEAR_MAGMA_SEARCH = (
    REPO
    / "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    / "scripts/equational_theory/linear_magma_search.py"
)
DEFAULT_CLAIM_STATE = ROOT / "artifacts" / "sair-eqt2" / "claim_state.jsonl"
DEFAULT_RESEARCH_RUN = ROOT / "artifacts" / "sair-eqt2" / "research_run.jsonl"
SELECTED_PRIME_ALLOWLIST = frozenset({2, 3, 5, 7, 11, 13, 17, 19, 89, 233})
LINEAR_MAGMA_SHARD_RE = re.compile(r"^linear-magma-shard-vars(?P<vars>\d+)-p(?P<prime>\d+)$")


def load_candidate(text: str) -> dict[str, Any]:
    try:
        candidate = json.loads(text)
    except json.JSONDecodeError as exc:
        return {
            "action_id": "candidate-json-invalid",
            "state": "candidate-invalid",
            "parse_error": str(exc),
        }
    if not isinstance(candidate, dict):
        return {
            "action_id": "candidate-json-not-object",
            "state": "candidate-invalid",
        }
    return candidate


def run_coefficient_analysis(output: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(COEFFICIENT_ANALYSIS),
            "--no-scan",
            "--output",
            str(output),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=900,
        check=False,
    )


LINEAR_MAGMA_SHARDS: dict[str, dict[str, Any]] = {
    "linear-magma-shard-vars1-p13": {
        "timeout": 120,
        "args": [
            "--max-vars-p13",
            "1",
            "--max-vars-p89",
            "0",
            "--max-vars-p233",
            "0",
            "--max-vars-baseline",
            "1",
            "--baseline-primes",
            "2,3,5,7,11,13",
            "--pattern-detail-limit",
            "4",
            "--novel-pair-limit",
            "20",
            "--bruteforce-sanity-max-vars",
            "1",
            "--bruteforce-sanity-coefficients",
            "1",
        ],
    },
    "linear-magma-shard-vars2-p13": {
        "timeout": 180,
        "args": [
            "--max-vars-p13",
            "2",
            "--max-vars-p89",
            "0",
            "--max-vars-p233",
            "0",
            "--max-vars-baseline",
            "1",
            "--baseline-primes",
            "2,3,5,7,11,13",
            "--pattern-detail-limit",
            "4",
            "--novel-pair-limit",
            "20",
            "--bruteforce-sanity-max-vars",
            "1",
            "--bruteforce-sanity-coefficients",
            "1",
        ],
    },
    "linear-magma-shard-vars1-p89": {
        "timeout": 180,
        "args": [
            "--max-vars-p13",
            "0",
            "--max-vars-p89",
            "1",
            "--max-vars-p233",
            "0",
            "--max-vars-baseline",
            "1",
            "--baseline-primes",
            "2,3,5,7,11,13,17,19",
            "--pattern-detail-limit",
            "4",
            "--novel-pair-limit",
            "20",
            "--bruteforce-sanity-max-vars",
            "1",
            "--bruteforce-sanity-coefficients",
            "1",
        ],
    },
    "linear-magma-shard-vars2-p89": {
        "timeout": 240,
        "args": [
            "--max-vars-p13",
            "0",
            "--max-vars-p89",
            "2",
            "--max-vars-p233",
            "0",
            "--max-vars-baseline",
            "1",
            "--baseline-primes",
            "2,3,5,7,11,13,17,19",
            "--pattern-detail-limit",
            "4",
            "--novel-pair-limit",
            "20",
            "--bruteforce-sanity-max-vars",
            "1",
            "--bruteforce-sanity-coefficients",
            "1",
        ],
    },
}


def linear_magma_shard_config(action_id: str) -> dict[str, Any]:
    legacy = LINEAR_MAGMA_SHARDS.get(action_id)
    if legacy is not None:
        return legacy

    shard_match = LINEAR_MAGMA_SHARD_RE.fullmatch(action_id)
    if shard_match:
        max_vars = int(shard_match.group("vars"))
        prime = int(shard_match.group("prime"))
        if prime in SELECTED_PRIME_ALLOWLIST:
            return {
                "timeout": 240,
                "args": [
                    "--selected-primes",
                    str(prime),
                    "--max-vars-selected",
                    str(max_vars),
                    "--max-vars-p13",
                    "0",
                    "--max-vars-p89",
                    "0",
                    "--max-vars-p233",
                    "0",
                    "--max-vars-baseline",
                    "1",
                    "--baseline-primes",
                    "2,3,5,7,11,13",
                    "--pattern-detail-limit",
                    "4",
                    "--novel-pair-limit",
                    "20",
                    "--bruteforce-sanity-max-vars",
                    "1",
                    "--bruteforce-sanity-coefficients",
                    "1",
                ],
            }

    return {
        "timeout": 20,
        "args": [
            "--max-vars-p13",
            "2",
            "--max-vars-p89",
            "2",
            "--max-vars-p233",
            "1",
            "--max-vars-baseline",
            "1",
            "--baseline-primes",
            "2,3,5,7,11,13",
            "--pattern-detail-limit",
            "2",
            "--novel-pair-limit",
            "5",
            "--bruteforce-sanity-max-vars",
            "1",
            "--bruteforce-sanity-coefficients",
            "1",
        ],
    }


def rejected_linear_magma_shard(action_id: str) -> dict[str, Any] | None:
    shard_match = LINEAR_MAGMA_SHARD_RE.fullmatch(action_id)
    if not shard_match:
        return None
    prime = int(shard_match.group("prime"))
    if prime in SELECTED_PRIME_ALLOWLIST:
        return None
    return {
        "action_id": action_id,
        "reason": "selected prime is not allowlisted for linear_magma_search dispatch",
        "rejected_prime": prime,
        "allowed_primes": sorted(SELECTED_PRIME_ALLOWLIST),
        "fallback_checker": "coefficient_analysis.py --no-scan",
    }


def run_linear_magma_search(output: Path, config: dict[str, Any]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(LINEAR_MAGMA_SEARCH),
            "--output",
            str(output),
            *config["args"],
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=int(config["timeout"]),
        check=False,
    )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def summarize_results(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    generation = data.get("generation", {})
    stats = data.get("global_statistics", {})
    bound = data.get("critical_prime_bound", {})
    return {
        "equation_count": generation.get("equation_count"),
        "matches_expected_count": generation.get("matches_expected_count"),
        "max_coefficient_polynomial_degree": stats.get(
            "max_coefficient_polynomial_degree"
        ),
        "max_abs_integer_coefficient_in_term_coefficients": stats.get(
            "max_abs_integer_coefficient_in_term_coefficients"
        ),
        "max_abs_integer_coefficient_in_difference_polynomials": stats.get(
            "max_abs_integer_coefficient_in_difference_polynomials"
        ),
        "critical_content_prime": bound.get("largest_prime"),
        "elapsed_seconds": data.get("elapsed_seconds"),
        "output_sha256": sha256_file(path),
    }


def checked_result(
    *,
    checker_name: str,
    status: str,
    exit_code: int,
    candidate: dict[str, Any],
    text: str,
    evidence: dict[str, Any] | str,
    output_path: str = "",
    stdout_excerpt: str = "",
    stderr_excerpt: str = "",
) -> dict[str, Any]:
    return {
        "schema": "omega.sair_eqt2.checker_result.v1",
        "target": "SAIR-EQT2",
        "checker_name": checker_name,
        "status": status,
        "exit_code": exit_code,
        "candidate": candidate,
        "summary": {
            "text": text,
            "evidence": evidence,
        },
        "evidence": json.dumps(evidence, sort_keys=True)
        if isinstance(evidence, dict)
        else evidence,
        "output_path": output_path,
        "stdout_excerpt": stdout_excerpt[:2000],
        "stderr_excerpt": stderr_excerpt[:2000],
        "truth_boundary": (
            "This checker output is deterministic evidence only; FKST/Codex "
            "text is not mathematical proof."
        ),
    }


def run_coefficient_candidate(candidate: dict[str, Any], out_dir: Path) -> dict[str, Any]:
    output = out_dir / "coefficient_analysis_results.json"
    try:
        completed = run_coefficient_analysis(output)
    except subprocess.TimeoutExpired as exc:
        return checked_result(
            checker_name="coefficient_analysis.py --no-scan",
            status="timeout",
            exit_code=-1,
            candidate=candidate,
            text=f"Coefficient analysis timed out after {exc.timeout} seconds; no mathematical claim is made.",
            evidence={},
            output_path=str(output),
        )

    if completed.returncode == 0 and output.exists():
        summary = summarize_results(output)
        return checked_result(
            checker_name="coefficient_analysis.py --no-scan",
            status="checked",
            exit_code=completed.returncode,
            candidate=candidate,
            text=(
                "Deterministic coefficient analysis generated the standard ETP "
                f"equation count {summary['equation_count']} and matches_expected_count="
                f"{summary['matches_expected_count']}."
            ),
            evidence=summary,
            output_path=str(output),
            stdout_excerpt=completed.stdout,
            stderr_excerpt=completed.stderr,
        )

    return checked_result(
        checker_name="coefficient_analysis.py --no-scan",
        status="checker-failed",
        exit_code=completed.returncode,
        candidate=candidate,
        text="Coefficient analysis failed; no mathematical claim is made.",
        evidence=(completed.stdout + "\n" + completed.stderr).strip()[:4000],
        output_path=str(output),
        stdout_excerpt=completed.stdout,
        stderr_excerpt=completed.stderr,
    )


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    if not path.exists():
        return rows
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        row = json.loads(line)
        row["_line"] = line_number
        rows.append(row)
    return rows


def configured_path(env_name: str, default: Path) -> Path:
    raw = os.environ.get(env_name)
    if raw:
        return Path(raw)
    return default


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO))
    except ValueError:
        return str(path)


def run_claim_boundary_audit(candidate: dict[str, Any]) -> dict[str, Any]:
    claim_state = configured_path("SAIR_EQT2_CLAIM_STATE", DEFAULT_CLAIM_STATE)
    research_run = configured_path("SAIR_EQT2_RESEARCH_RUN", DEFAULT_RESEARCH_RUN)
    claim_rows = load_jsonl(claim_state)
    research_rows = load_jsonl(research_run)
    rows = claim_rows + research_rows
    violations: list[str] = []
    for row in rows:
        if row.get("target") != "SAIR-EQT2":
            violations.append(f"line {row.get('_line')}: target is {row.get('target')!r}")
        encoded = json.dumps(row, sort_keys=True)
        for blocked in ("Israel", "Tolmetes", "omega-open-problem"):
            if blocked in encoded:
                violations.append(f"line {row.get('_line')}: out-of-scope term {blocked}")
        allowed_context = json.dumps(row.get("must_not_claim", []), sort_keys=True)
        claim_text = re.sub(re.escape(allowed_context), "", encoded)
        for phrase in ("submission accepted", "submitted to SAIR", "mathematical proof"):
            if phrase in claim_text:
                violations.append(f"line {row.get('_line')}: unsafe claim phrase {phrase!r}")

    evidence = {
        "files_checked": [display_path(claim_state), display_path(research_run)],
        "claim_rows_checked": len(claim_rows),
        "research_rows_checked": len(research_rows),
        "rows_checked": len(rows),
        "self_row_excluded_from_scan": True,
        "violations": violations,
        "violation_count": len(violations),
    }
    return checked_result(
        checker_name="sair_eqt2_claim_boundary_audit",
        status="checked" if not violations else "violations-found",
        exit_code=0 if not violations else 2,
        candidate=candidate,
        text=(
            "SAIR-EQT2 artifact boundary audit passed."
            if not violations
            else "SAIR-EQT2 artifact boundary audit found violations; no mathematical claim is made."
        ),
        evidence=evidence,
    )


def summarize_linear_magma(path: Path, config: dict[str, Any], stdout: str) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    selected = data.get("selected_prime_results", {})
    return {
        "parameters": config["args"],
        "timeout_seconds": config["timeout"],
        "source": data.get("source_info", {}).get("source"),
        "synthetic_fallback": data.get("source_info", {}).get("synthetic_fallback"),
        "equation_count_total": data.get("equation_count_total"),
        "selected_prime_results": {
            prime: {
                "equations_checked": item.get("equations_checked"),
                "coefficients_tested": item.get("coefficients_tested"),
                "distinct_satisfaction_patterns": item.get("distinct_satisfaction_patterns"),
                "elapsed_seconds": item.get("elapsed_seconds"),
                "pattern_details": item.get("pattern_details", [])[:4],
                "pattern_details_truncated": item.get("pattern_details_truncated"),
            }
            for prime, item in selected.items()
        },
        "baseline": {
            "primes": data.get("baseline", {}).get("primes"),
            "equations_checked": data.get("baseline", {}).get("equations_checked"),
            "anti_implication_count": data.get("baseline", {}).get("anti_implication_count"),
            "elapsed_seconds": data.get("baseline", {}).get("elapsed_seconds"),
        },
        "p233_novelty": {
            "equations_checked": data.get("p233_novelty", {}).get("equations_checked"),
            "p233_anti_implication_count": data.get("p233_novelty", {}).get("p233_anti_implication_count"),
            "novel_anti_implication_count": data.get("p233_novelty", {}).get("novel_anti_implication_count"),
            "novel_anti_implications": data.get("p233_novelty", {}).get("novel_anti_implications", [])[:20],
            "novel_anti_implications_truncated": data.get("p233_novelty", {}).get("novel_anti_implications_truncated"),
        },
        "bruteforce_sanity": data.get("bruteforce_sanity"),
        "stdout_lines": stdout.splitlines()[:40],
        "output_sha256": sha256_file(path),
    }


def run_linear_magma_candidate(candidate: dict[str, Any], out_dir: Path) -> dict[str, Any]:
    action_id = str(candidate.get("action_id", "linear-magma-smoke"))
    config = linear_magma_shard_config(action_id)
    output = out_dir / f"{action_id}.json"
    try:
        completed = run_linear_magma_search(output, config)
    except subprocess.TimeoutExpired as exc:
        return checked_result(
            checker_name=f"linear_magma_search.py {action_id}",
            status="timeout",
            exit_code=-1,
            candidate=candidate,
            text=(
                "Bounded linear magma shard timed out; this is a scheduling finding, "
                "not a mathematical result."
            ),
            evidence={
                "parameters": config["args"],
                "timeout_seconds": exc.timeout,
                "output_path": str(output),
            },
            output_path=str(output),
        )

    stdout = completed.stdout
    if completed.returncode == 0 and output.exists():
        evidence = summarize_linear_magma(output, config, stdout)
        sanity = evidence.get("bruteforce_sanity") or {}
        status = "checked" if not sanity.get("mismatches") else "checker-failed"
    else:
        evidence = {
            "parameters": config["args"],
            "timeout_seconds": config["timeout"],
            "output_path": str(output),
            "stdout_lines": stdout.splitlines()[:40],
            "stderr_excerpt": completed.stderr[:2000],
        }
        status = "checker-failed"
    return checked_result(
        checker_name=f"linear_magma_search.py {action_id}",
        status=status,
        exit_code=completed.returncode,
        candidate=candidate,
        text=(
            "Bounded linear magma shard completed against local 4694-equation ETP enumeration."
            if status == "checked"
            else "Bounded linear magma shard failed; no mathematical claim is made."
        ),
        evidence=evidence,
        output_path=str(output),
        stdout_excerpt=stdout,
        stderr_excerpt=completed.stderr,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-json", required=True)
    args = parser.parse_args()

    candidate = load_candidate(args.candidate_json)
    out_dir = Path(tempfile.mkdtemp(prefix="sair-eqt2-research-check-"))
    action_id = str(candidate.get("action_id", ""))
    shard_match = LINEAR_MAGMA_SHARD_RE.fullmatch(action_id)
    if action_id == "claim-boundary-audit":
        result = run_claim_boundary_audit(candidate)
    elif action_id == "linear-magma-smoke" or action_id in LINEAR_MAGMA_SHARDS or (
        shard_match and int(shard_match.group("prime")) in SELECTED_PRIME_ALLOWLIST
    ):
        result = run_linear_magma_candidate(candidate, out_dir)
    else:
        dispatch_rejection = rejected_linear_magma_shard(action_id)
        result = run_coefficient_candidate(candidate, out_dir)
        if dispatch_rejection is not None:
            result["dispatch_rejection"] = dispatch_rejection
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
