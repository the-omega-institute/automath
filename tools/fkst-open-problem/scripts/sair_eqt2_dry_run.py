#!/usr/bin/env python3
"""SAIR-EQT2-only FKST dry run.

This script intentionally models one target and one durable output. It does not
start an FKST supervisor, write GitHub state, or touch other open-problem
pipelines.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import tempfile


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
PIPELINE = ROOT / "targets" / "sair-eqt2" / "pipeline.json"
CLAIM_STATE = ROOT / "artifacts" / "sair-eqt2" / "claim_state.jsonl"

PROPOSAL_ID = (
    "omega-sair-eqt2/SAIR-EQT2/"
    "prepare-sair-equational-theories-stage-2-solver-v4"
)
DEDUP_KEY = f"consensus:{PROPOSAL_ID}/v1"


def load_pipeline() -> dict:
    try:
        data = json.loads(PIPELINE.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{PIPELINE.relative_to(REPO)}: invalid JSON: {exc}") from exc
    if data.get("schema") != "omega.sair_eqt2.pipeline.v1":
        raise SystemExit(f"{PIPELINE.relative_to(REPO)}: bad schema")
    if data.get("target") != "SAIR-EQT2":
        raise SystemExit(f"{PIPELINE.relative_to(REPO)}: target must be SAIR-EQT2")
    if data.get("github_write_enabled") is not False:
        raise SystemExit("GitHub write automation must remain disabled for dry-run")
    allowed = data.get("allowed_outputs")
    if not isinstance(allowed, list) or not allowed:
        raise SystemExit("dry-run must declare allowed outputs")
    expected_claim_state = "tools/fkst-open-problem/artifacts/sair-eqt2/claim_state.jsonl"
    if expected_claim_state not in allowed:
        raise SystemExit("dry-run must include the committed claim-state output")
    for item in allowed:
        if not isinstance(item, str) or not item.startswith(
            "tools/fkst-open-problem/artifacts/sair-eqt2/"
        ):
            raise SystemExit(f"out-of-scope allowed output: {item!r}")
    executable_surface = {
        "allowed_outputs": data.get("allowed_outputs"),
        "source_anchors": data.get("source_anchors"),
        "dry_run": data.get("dry_run"),
    }
    blocked_terms = ("Israel", "Tolmetes", "T-43", "T-44", "T-32")
    encoded = json.dumps(executable_surface, sort_keys=True)
    for term in blocked_terms:
        if term in encoded:
            raise SystemExit(f"pipeline must not include out-of-scope term: {term}")
    return data


def validate_ref(raw_ref: str) -> None:
    ref_path, _, anchor = raw_ref.partition("#")
    path = REPO / ref_path
    if not path.exists():
        raise SystemExit(f"missing referenced path: {ref_path}")
    if anchor and anchor not in path.read_text(encoding="utf-8"):
        raise SystemExit(f"missing anchor {anchor!r} in {ref_path}")


def validate_sources(pipeline: dict) -> None:
    anchors = pipeline.get("source_anchors", {})
    for category in ("lean", "scripts"):
        refs = anchors.get(category)
        if not isinstance(refs, list) or not refs:
            raise SystemExit(f"missing source_anchors.{category}")
        for ref in refs:
            if not isinstance(ref, str) or not ref:
                raise SystemExit(f"bad source reference in {category}")
            validate_ref(ref)


def claim_rows() -> list[dict]:
    return [
        {
            "schema": "omega.claim_state.v1",
            "target": "SAIR-EQT2",
            "claim_id": "sair-eqt2-window6-fin21-certificate",
            "state": "lean-anchor-present",
            "public_impact": True,
            "summary": (
                "Window-6 Fin 21 rectangular-band certificate gives "
                "deterministic satisfied/refuted ETP facts and spectrum counts; "
                "this is a certificate-layer contribution, not a "
                "solved-conjecture claim."
            ),
            "must_not_claim": [
                "general Equational Theories solved",
                "new theorem beyond cited Lean/checker/source artifacts",
                "FKST consensus as mathematical proof",
                "SAIR-EQT2 submission accepted",
            ],
            "lean_refs": [
                "lean4/Omega/EA/Window6CountermodelCertificate.lean#paper_window6_fin21_facts_certificate",
                "lean4/Omega/EA/Window6CountermodelCertificate.lean#paper_window6_equational_spectrum",
                "lean4/Omega/Folding/Window6EquationalSpectrum.lean#paper_window6_equational_spectrum",
            ],
            "script_refs": [
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/audit_window6_current.py",
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/coefficient_analysis.py",
            ],
            "fkst_proposal_id": PROPOSAL_ID,
            "fkst_dedup_key": DEDUP_KEY,
        },
        {
            "schema": "omega.claim_state.v1",
            "target": "SAIR-EQT2",
            "claim_id": "sair-eqt2-submission-boundary",
            "state": "submission-prep",
            "public_impact": True,
            "summary": (
                "Use Omega/Automath finite-magma and Lean certificate "
                "artifacts as a deterministic checker layer before LLM "
                "escalation for SAIR Stage 2 participation."
            ),
            "must_not_claim": [
                "general Equational Theories solved",
                "new theorem beyond cited Lean anchors",
                "FKST consensus as mathematical proof",
            ],
            "next_artifact": (
                "solver submission shard plus public Contributor Network "
                "description"
            ),
            "fkst_proposal_id": PROPOSAL_ID,
            "fkst_dedup_key": DEDUP_KEY,
        },
    ]


def render_claim_state() -> str:
    return "\n".join(
        json.dumps(row, separators=(",", ":"), ensure_ascii=False)
        for row in claim_rows()
    ) + "\n"


def validate_claim_state(text: str) -> None:
    rows = []
    for index, line in enumerate(text.splitlines(), start=1):
        row = json.loads(line)
        rows.append(row)
        if row.get("target") != "SAIR-EQT2":
            raise SystemExit(f"generated row {index}: target must be SAIR-EQT2")
        if row.get("schema") != "omega.claim_state.v1":
            raise SystemExit(f"generated row {index}: bad schema")
        if row.get("fkst_dedup_key") != DEDUP_KEY:
            raise SystemExit(f"generated row {index}: bad FKST dedup key")
    if len(rows) != 2:
        raise SystemExit("generated claim-state must contain exactly two rows")


def write_output(text: str, output: Path | None) -> Path:
    if output is None:
        temp = Path(tempfile.mkdtemp(prefix="sair-eqt2-dry-run-"))
        output = temp / "claim_state.jsonl"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text, encoding="utf-8")
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional output path for the generated claim_state.jsonl.",
    )
    parser.add_argument(
        "--no-compare",
        action="store_true",
        help="Generate output without comparing it to the committed artifact.",
    )
    args = parser.parse_args()

    pipeline = load_pipeline()
    validate_sources(pipeline)
    generated = render_claim_state()
    validate_claim_state(generated)
    output = write_output(generated, args.output)

    if not args.no_compare:
        committed = CLAIM_STATE.read_text(encoding="utf-8")
        if generated != committed:
            raise SystemExit(
                "generated claim-state does not match "
                f"{CLAIM_STATE.relative_to(REPO)}"
            )

    print(f"target: SAIR-EQT2")
    print(f"pipeline: {PIPELINE.relative_to(REPO)}")
    print(f"generated: {output}")
    if args.no_compare:
        print("compare: skipped")
    else:
        print(f"compare: matched {CLAIM_STATE.relative_to(REPO)}")
    print("github_write: disabled")


if __name__ == "__main__":
    main()
