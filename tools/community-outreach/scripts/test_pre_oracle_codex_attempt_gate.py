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


def _proof_decomposition_workup() -> str:
    return """
# Codex Workup

## Target claim now

The target claim is a proof-only open problem where no local certificate has
been supplied yet.  The current workup must reduce the claim to a checkable
Oracle obligation before any external reasoning turn.

## Local evidence checked

I inspected `tools/community-outreach/targets/demo/research.md` and found no
certificate, no verifier script, and no `results.json`; this target currently
has only a proof strategy sketch and the local directory fact must be respected.

## Commands run

```bash
rg -n "certificate|verifier|results.json|lemma" tools/community-outreach/targets/demo
sed -n '1,180p' tools/community-outreach/targets/demo/research.md
```

## Codex attempt before Oracle

No local replay is available yet, so I did a proof decomposition instead of
only forwarding metadata.  I split the theorem into Claim 1 (normal-form
reduction), Lemma 2 (finite obstruction for the reduced form), and Lemma 3
(lifting the obstruction back to the original statement).  Claim 1 follows
from the written normal-form argument in `research.md`, but the first blocker
is Lemma 2: the finite obstruction is named but unproved, and no local
certificate exists to test it.  The next Oracle turn must prove Lemma 2 or
produce a checkable obstruction showing the reduction route cannot close.

## Verifier/artifact status

The local artifact status is negative: no verifier script, no certificate, and
no `results.json` are present under `tools/community-outreach/targets/demo`.

## Proof obligations still open

Lemma 2 is the first unproved case.  If Oracle proves Lemma 2, Codex can next
try to turn the finite obstruction into a verifier/certificate; if Oracle
refutes it, the target should be re-scoped.

## Next Oracle question

`tools/community-outreach/targets/demo/research.md` has no local verifier or certificate, and Codex reduced the proof route to Lemma 2 as the first blocker. Prove Lemma 2, the finite obstruction for the reduced normal form, or give a checkable obstruction showing this reduction route cannot close.

## Publication value / re-scope judgment

A proof of Lemma 2 would be publishable as a short note only if the lifting
Lemma 3 can then be made checkable.
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

        proof_decomposition_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'rg -n \"certificate|verifier|results.json|lemma\" {rel_target}'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "research.md:17:Lemma 2 is currently unproved\n",
            }
        }
        stdout_path.write_text(json.dumps(proof_decomposition_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        proof_decomposition = _proof_decomposition_workup()
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            proof_decomposition,
            (
                "Codex found no local verifier or certificate under "
                "`tools/community-outreach/targets/demo/research.md`, and reduced the proof route to "
                "Lemma 2 as the first blocker. Prove Lemma 2."
            ),
            "Ran target inspection and decomposed the proof into Claim 1, Lemma 2, and Lemma 3; Lemma 2 is the first blocker.",
            codex_trace=trace,
        )
        if not substantive.get("ok") or not substantive.get("workup_has_proof_decomposition_attempt"):
            raise AssertionError(f"named proof decomposition should pass substantive gate: {substantive}")

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
        ungrounded = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            (
                "Prove the exact theorem by finding a new certificate and explain the "
                "remaining obstruction in a complete publishable argument."
            ),
            (
                "Ran command `python3 demo/scripts/check_slice.py --case finite --json`; "
                "the finite certificate replay passed with sha256=abc123, but case 3 still "
                "needs an Oracle-supplied lemma."
            ),
            codex_trace=trace,
        )
        if ungrounded.get("ok") or ungrounded.get("question_grounded_in_local_work"):
            raise AssertionError(f"ungrounded concrete Oracle question should fail: {ungrounded}")

        reserved_before = local_repair._snapshot_reserved_harness_files(target_dir)
        (target_dir / "local_repair_last.json").write_text(
            json.dumps({"status": "worker_overwrite"}) + "\n",
            encoding="utf-8",
        )
        substantive_workup = _workup(include_attempt=True)
        for name, text in {
            "codex_workup.md": substantive_workup,
            "next_oracle_question.md": (
                "The local check produced sha256=abc123 for the finite certificate replay. "
                "Prove the missing case-3 lemma or provide a checkable obstruction."
            ),
            "local_repair_report.md": (
                "Ran command `python3 demo/scripts/check_slice.py --case finite --json`; "
                "the finite certificate replay passed with sha256=abc123, but case 3 still "
                "needs an Oracle-supplied lemma."
            ),
        }.items():
            (target_dir / name).write_text(text, encoding="utf-8")
        postcheck = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=reserved_before,
        )
        if postcheck.get("ok") or "local_repair_last.json" not in " ".join(postcheck.get("diagnostics", [])):
            raise AssertionError(f"reserved harness overwrite was not rejected: {postcheck}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
