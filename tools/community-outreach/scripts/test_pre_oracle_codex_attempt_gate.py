#!/usr/bin/env python3
"""Regression test for the pre-Oracle local-attempt gate.

Oracle prompts must not be allowed through merely because Codex wrote target
metadata, a file manifest, and a nicer question.  The handoff must include an
actual Codex attempt on the current mathematical gap.
"""

from __future__ import annotations

import importlib.util
import json
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_local_repair.py"


def _load_local_repair():
    spec = importlib.util.spec_from_file_location("outreach_local_repair_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _workup(*, include_attempt: bool) -> str:
    attempt = ""
    if include_attempt:
        attempt = """
## Codex attempt before Oracle

I attempted a local proof/replay step before asking Oracle: ran `python3 tools/community-outreach/targets/demo/scripts/check_slice.py --case finite --json`, which checked the finite certificate case split against `results.json`. The result was fail: the construction proof is blocked by a missing lemma for case 3, so the next Oracle turn must supply that lemma or a checkable obstruction.
"""
    return f"""
# Codex Workup

## Target claim now

The target claim is a finite certificate theorem whose current verifier should
establish one exact bound from a local `results.json` artifact.

## Local evidence checked

I inspected the target directory, found `tools/community-outreach/targets/demo/results.json`, and confirmed that the current artifact is missing the case-3 proof certificate needed for the theorem. This is a concrete local fact, not board metadata.

## Commands run

```bash
python3 tools/community-outreach/targets/demo/scripts/check_slice.py --case finite --json
python3 -m json.tool tools/community-outreach/targets/demo/results.json
```
{attempt}

## Verifier/artifact status

The verifier script and `results.json` are present, but the proof certificate for
case 3 is missing. The local check therefore cannot certify the construction yet.

## Proof obligations still open

Prove the missing case-3 lemma or produce a counterexample/obstruction explaining
why the finite certificate route cannot close.

## Next Oracle question

The local check found that `results.json` is present but the case-3 proof certificate is missing after running `python3 tools/community-outreach/targets/demo/scripts/check_slice.py --case finite --json`. Prove the exact case-3 lemma needed by the finite certificate verifier, or give a checkable obstruction that shows this certificate route cannot close.

## Publication value / re-scope judgment

If closed, this becomes a bounded certificate note with reproducible verifier
commands; otherwise the failure analysis is still useful.
"""


def main() -> int:
    local_repair = _load_local_repair()
    ok, reason = local_repair._workup_has_local_execution_trace(_workup(include_attempt=False))
    if ok or "codex attempt before oracle" not in reason.lower():
        raise AssertionError(f"metadata-only handoff was not rejected correctly: ok={ok} reason={reason!r}")

    ok, reason = local_repair._workup_has_local_execution_trace(_workup(include_attempt=True))
    if not ok:
        raise AssertionError(f"handoff with a real Codex attempt was rejected: {reason}")

    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        target_dir = Path(tmp) / "demo"
        target_dir.mkdir()
        stdout_path = target_dir / "codex.jsonl"
        rel_target = str(target_dir.relative_to(local_repair.REPO_ROOT))
        shallow_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'python3 -m json.tool {rel_target}/results.json >/dev/null'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "",
            }
        }
        stdout_path.write_text(json.dumps(shallow_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("inspection_command_count") or 0) <= 0:
            raise AssertionError(f"json.tool sanity check was not counted as inspection: {trace}")
        if int(trace.get("replay_command_count") or 0) != 0:
            raise AssertionError(f"json.tool sanity check was incorrectly counted as replay: {trace}")
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            "The local `results.json` exists but the case-3 certificate is missing.",
            "Ran a target inspection command.",
            codex_trace=trace,
        )
        if substantive.get("ok"):
            raise AssertionError(f"inspection-only command trace should not pass substantive gate: {substantive}")

        negative_search_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'find {rel_target} -name \"*.lrat\" -o -name \"*.drat\"'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "",
            }
        }
        stdout_path.write_text(json.dumps(negative_search_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("negative_artifact_search_count") or 0) <= 0:
            raise AssertionError(f"negative artifact search was not counted: {trace}")
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            "The local `.lrat` certificate search found no proof file.",
            "Ran a target artifact search and found no LRAT/DRAT certificate.",
            codex_trace=trace,
        )
        if substantive.get("ok"):
            raise AssertionError(f"negative artifact search alone should not pass substantive gate: {substantive}")

        replay_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'python3 {rel_target}/scripts/check_slice.py --case finite --json'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "checked certificate: passed sha256=abc123\n",
            }
        }
        stdout_path.write_text(json.dumps(replay_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("replay_command_count") or 0) <= 0 or not trace.get("has_evidence_output"):
            raise AssertionError(f"real target-local check was not counted as replay/evidence: {trace}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
