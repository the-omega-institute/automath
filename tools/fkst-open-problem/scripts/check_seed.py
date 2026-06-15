#!/usr/bin/env python3
"""Static checks for the FKST open-problem pilot skeleton."""

from __future__ import annotations

from pathlib import Path
import json


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
PACKAGE = ROOT / "packages" / "omega-open-problem"


def require(path: str, needle: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    if needle not in text:
        raise SystemExit(f"{path}: missing {needle!r}")


def check_text_file(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    for index, line in enumerate(text.splitlines(), start=1):
        if line.rstrip() != line:
            raise SystemExit(f"{path.relative_to(ROOT)}:{index}: trailing whitespace")
    if text.endswith("\n\n"):
        raise SystemExit(f"{path.relative_to(ROOT)}: new blank line at EOF")


def check_lua_files() -> None:
    lua_files = sorted(PACKAGE.rglob("*.lua"))
    if not lua_files:
        raise SystemExit("no Lua files found")
    for path in lua_files:
        check_text_file(path)
        line_count = len(path.read_text(encoding="utf-8").splitlines())
        if line_count > 1000:
            raise SystemExit(f"{path.relative_to(ROOT)}: exceeds FKST 1000-line guard")

def check_claim_state() -> None:
    path = ROOT / "artifacts" / "sair-eqt2" / "claim_state.jsonl"
    if not path.exists():
        raise SystemExit(f"missing {path.relative_to(ROOT)}")
    rows = []
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line:
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{path.relative_to(ROOT)}:{index}: invalid JSON: {exc}") from exc
        rows.append(row)
        if row.get("schema") != "omega.claim_state.v1":
            raise SystemExit(f"{path.relative_to(ROOT)}:{index}: bad schema")
        for field in ("target", "claim_id", "state", "summary"):
            if not isinstance(row.get(field), str) or not row[field]:
                raise SystemExit(f"{path.relative_to(ROOT)}:{index}: missing {field}")
        for ref_field in ("lean_refs", "script_refs"):
            for ref in row.get(ref_field, []):
                raw_ref = str(ref)
                ref_path, _, anchor = raw_ref.partition("#")
                full_path = REPO / ref_path
                if not full_path.exists():
                    raise SystemExit(
                        f"{path.relative_to(ROOT)}:{index}: missing referenced path {ref_path}"
                    )
                if anchor and anchor not in full_path.read_text(encoding="utf-8"):
                    raise SystemExit(
                        f"{path.relative_to(ROOT)}:{index}: missing anchor {anchor} in {ref_path}"
                    )
    if len(rows) < 2:
        raise SystemExit(f"{path.relative_to(ROOT)}: expected at least two claim rows")


def main() -> None:
    for relative in [
        "packages/omega-open-problem/core.lua",
        "packages/omega-open-problem/departments/proposal_intake/main.lua",
        "packages/omega-open-problem/departments/artifact_task/main.lua",
        "packages/omega-open-problem/departments/artifact_writer/main.lua",
        "packages/omega-open-problem/departments/seed_t43/main.lua",
        "packages/omega-open-problem/departments/seed_sair_stage2/main.lua",
        "packages/omega-open-problem/raisers/seed.lua",
        "packages/omega-open-problem/raisers/sair_stage2.lua",
        "packages/omega-open-problem/tests/core_test.lua",
        "packages/omega-open-problem/tests/integration_test.lua",
    ]:
        if not (ROOT / relative).exists():
            raise SystemExit(f"missing {relative}")

    require("README.md", "Agent consensus alone is never an accepted mathematical fact.")
    require("pilot.md", "Start with T-43")
    require("packages/omega-open-problem/core.lua", "T-43")
    require("packages/omega-open-problem/core.lua", "SAIR-EQT2")
    require("packages/omega-open-problem/core.lua", "validate_consensus_reached")
    require("packages/omega-open-problem/core.lua", "validate_artifact_task")
    require("packages/omega-open-problem/core.lua", "consensus.proposal.v1")
    require("packages/omega-open-problem/departments/proposal_intake/main.lua", "consensus.proposal")
    require("packages/omega-open-problem/departments/artifact_task/main.lua", "omega_artifact_task")
    require("packages/omega-open-problem/departments/artifact_writer/main.lua", "omega_repo_artifact")
    require("artifacts/sair-eqt2/claim_state.jsonl", "sair-eqt2-window6-fin21-certificate")
    require("packages/omega-open-problem/departments/seed_t43/main.lua", "Source-replay A5 same-W")
    require("packages/omega-open-problem/departments/seed_sair_stage2/main.lua", "SAIR Equational Theories Stage 2 solver v4")
    require("packages/omega-open-problem/raisers/seed.lua", "omega_seed_tick")
    require("packages/omega-open-problem/raisers/sair_stage2.lua", "omega_sair_stage2_tick")
    require("packages/omega-open-problem/tests/core_test.lua", "test_validate_proposal_accepts_sair_public_impact_target")
    require("packages/omega-open-problem/tests/integration_test.lua", "test_artifact_writer_raises_repo_artifact_payload")
    check_lua_files()
    check_claim_state()


if __name__ == "__main__":
    main()
