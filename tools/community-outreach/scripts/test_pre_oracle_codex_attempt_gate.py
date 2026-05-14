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
        if int(trace.get("mathematical_action_command_count") or 0) != 0:
            raise AssertionError(f"json.tool sanity check was incorrectly counted as mathematical action: {trace}")
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            "The local `results.json` exists but the case-3 certificate is missing.",
            "Ran a target inspection command.",
            codex_trace=trace,
        )
        if substantive.get("ok"):
            raise AssertionError(f"inspection-only command trace should not pass substantive gate: {substantive}")

        py_compile_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'python3 -m py_compile {rel_target}/scripts/check_slice.py'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "",
            }
        }
        stdout_path.write_text(json.dumps(py_compile_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("replay_command_count") or 0) != 0:
            raise AssertionError(f"py_compile was incorrectly counted as replay: {trace}")
        if int(trace.get("mathematical_action_command_count") or 0) != 0:
            raise AssertionError(f"py_compile was incorrectly counted as mathematical action: {trace}")
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            "The local `results.json` exists but the case-3 certificate is missing.",
            "Ran only py_compile on a local script.",
            codex_trace=trace,
        )
        if substantive.get("ok"):
            raise AssertionError(f"py_compile-only command trace should not pass substantive gate: {substantive}")

        metadata_update_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'python3 {rel_target}/scripts/update_profile_metadata.py --board-status RUN'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "updated profile metadata for graph bound target\n",
            }
        }
        stdout_path.write_text(json.dumps(metadata_update_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("target_command_count") or 0) <= 0:
            raise AssertionError(f"metadata update should still count as a target-local command: {trace}")
        if int(trace.get("mathematical_action_command_count") or 0) != 0:
            raise AssertionError(f"metadata/profile update was incorrectly counted as mathematical action: {trace}")
        substantive = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            "The local `results.json` exists but the case-3 certificate is missing.",
            "Updated only target metadata/profile state before asking Oracle.",
            codex_trace=trace,
        )
        if substantive.get("ok"):
            raise AssertionError(f"metadata/profile update should not pass substantive gate: {substantive}")

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
            (
                "Pre-Oracle mathematical action: ran target inspection and decomposed the proof "
                "into Claim 1, Lemma 2, and Lemma 3 before asking Oracle; Lemma 2 is the first "
                "proof blocker."
            ),
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
        duplicate_skip = local_repair._post_codex_duplicate_replay_skip(trace)
        if not duplicate_skip or duplicate_skip.get("reason") != "post_codex_replay_trace_present_skip_duplicate_replay":
            raise AssertionError(f"post-Codex duplicate replay was not skipped from trace evidence: {duplicate_skip}")

        pcurvature_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'python3 {rel_target}/rank_one_log_pcurvature.py'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": (
                    "D = d/dt + a/t: p-curvature coefficient is a(a-1)...(a-p+1)=a^p-a\n"
                    "zero coefficients for p=[7, 17]\n"
                    "nonzero coefficients for p=[3, 5]\n"
                ),
            }
        }
        stdout_path.write_text(json.dumps(pcurvature_event) + "\n", encoding="utf-8")
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)
        if int(trace.get("mathematical_action_command_count") or 0) <= 0:
            raise AssertionError(f"p-curvature checker should count as mathematical action: {trace}")

        missing_pre_oracle_report = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            (
                "The local check found `results.json` and sha256=abc123 but the case-3 proof "
                "certificate is missing. Prove the exact case-3 lemma."
            ),
            (
                "Ran command `python3 demo/scripts/check_slice.py --case finite --json`; "
                "the finite certificate replay passed with sha256=abc123, but case 3 still "
                "needs an Oracle-supplied lemma."
            ),
            codex_trace=trace,
        )
        if missing_pre_oracle_report.get("ok") or missing_pre_oracle_report.get("report_declares_pre_oracle_processing"):
            raise AssertionError(
                "report without explicit pre-Oracle mathematical action should fail: "
                f"{missing_pre_oracle_report}"
            )
        shallow_replay_skip = local_repair._post_codex_duplicate_replay_skip(
            {"replay_command_count": 1, "mathematical_action_command_count": 0, "has_evidence_output": True}
        )
        if shallow_replay_skip is not None:
            raise AssertionError(f"non-mathematical replay trace should not skip verifier replay: {shallow_replay_skip}")
        shallow_skip = local_repair._post_codex_duplicate_replay_skip({"replay_command_count": 0, "has_evidence_output": True})
        if shallow_skip is not None:
            raise AssertionError(f"inspection-only trace should not skip verifier replay: {shallow_skip}")

        inspection_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'find {rel_target} -maxdepth 2 -type f | sort'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": f"{rel_target}/results.json\n{rel_target}/scripts/check_slice.py\n",
            }
        }
        stdout_path.write_text(
            json.dumps(inspection_event) + "\n" + json.dumps(replay_event) + "\n",
            encoding="utf-8",
        )
        trace = local_repair._codex_jsonl_local_command_trace(stdout_path, target_dir)

        artifact_results = target_dir / "results.json"
        artifact_results.write_text(
            json.dumps(
                {
                    "commands": [
                        {
                            "command": (
                                f"python3 {rel_target}/scripts/expensive_batch.py "
                                f"--json-out {rel_target}/expensive_batch.json"
                            )
                        }
                    ]
                }
            )
            + "\n",
            encoding="utf-8",
        )
        no_artifact_pre_audit = local_repair._record_target_verifier_audit(
            "T-DEMO",
            target_dir,
            include_results_artifact_commands=False,
        )
        if no_artifact_pre_audit.get("ran"):
            raise AssertionError(
                "pre-Codex verifier audit must not run results.json artifact commands: "
                f"{no_artifact_pre_audit}"
            )

        ungrounded = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            (
                "Prove the exact theorem by finding a new certificate and explain the "
                "remaining obstruction in a complete publishable argument."
            ),
            (
                "Pre-Oracle mathematical action: ran command `python3 demo/scripts/check_slice.py "
                "--case finite --json` before asking Oracle; the finite certificate replay passed "
                "with sha256=abc123, but case 3 still needs an Oracle-supplied lemma."
            ),
            codex_trace=trace,
        )
        if ungrounded.get("ok") or ungrounded.get("question_grounded_in_local_work"):
            raise AssertionError(f"ungrounded concrete Oracle question should fail: {ungrounded}")

        slug_only = local_repair._substantive_local_workup_check(
            target_dir,
            _workup(include_attempt=True),
            (
                "For demo, prove the exact theorem by finding a new certificate and "
                "explain the remaining obstruction in a complete publishable argument."
            ),
            (
                "Pre-Oracle mathematical action: ran command `python3 demo/scripts/check_slice.py "
                "--case finite --json` before asking Oracle; the finite certificate replay passed "
                "with sha256=abc123, but case 3 still needs an Oracle-supplied lemma."
            ),
            codex_trace=trace,
        )
        if slug_only.get("ok") or slug_only.get("question_grounded_in_local_work"):
            raise AssertionError(f"slug-only Oracle question should not count as locally grounded: {slug_only}")

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
                "Pre-Oracle mathematical action: ran command `python3 demo/scripts/check_slice.py "
                "--case finite --json` before writing `next_oracle_question.md`; the finite "
                "certificate replay passed with sha256=abc123, but case 3 still needs an "
                "Oracle-supplied lemma."
            ),
        }.items():
            (target_dir / name).write_text(text, encoding="utf-8")
        postcheck = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=reserved_before,
        )
        if not postcheck.get("ok"):
            raise AssertionError(
                "local_repair_last.json is harness-overwritten final state and should be warn-only: "
                f"{postcheck}"
            )
        if "local_repair_last.json" not in " ".join(postcheck.get("warnings", [])):
            raise AssertionError(f"warn-only local_repair_last.json mutation was not recorded: {postcheck}")
        if postcheck.get("reserved_harness_file_blocking_mutations"):
            raise AssertionError(f"local_repair_last.json should not be a blocking mutation: {postcheck}")

        postcheck = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=local_repair._snapshot_reserved_harness_files(target_dir),
            run_started_at="2999-01-01T00:00:00+00:00",
        )
        stale_diagnostics = " ".join(postcheck.get("diagnostics", []))
        if postcheck.get("ok") or "was not refreshed by this local repair run" not in stale_diagnostics:
            raise AssertionError(f"stale handoff should be rejected: {postcheck}")

        reserved_before = local_repair._snapshot_reserved_harness_files(target_dir)
        (target_dir / "science_gate.json").write_text(
            json.dumps({"status": "harness_refreshed"}) + "\n",
            encoding="utf-8",
        )
        (target_dir / "outreach_impact_gate.json").write_text(
            json.dumps({"status": "harness_refreshed"}) + "\n",
            encoding="utf-8",
        )
        postcheck = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=reserved_before,
            ignore_reserved_names={"science_gate.json", "outreach_impact_gate.json"},
        )
        diagnostics = " ".join(postcheck.get("diagnostics", []))
        if "science_gate.json" in diagnostics or "outreach_impact_gate.json" in diagnostics:
            raise AssertionError(f"harness-refreshed ledgers should be ignored: {postcheck}")

        reserved_before = local_repair._snapshot_reserved_harness_files(target_dir)
        (target_dir / "science_gate.json").write_text(
            json.dumps({"status": "worker_overwrite"}) + "\n",
            encoding="utf-8",
        )
        postcheck = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=reserved_before,
        )
        diagnostics = " ".join(postcheck.get("diagnostics", []))
        if postcheck.get("ok") or "science_gate.json" not in diagnostics:
            raise AssertionError(f"non-ignored science_gate.json mutation should remain blocking: {postcheck}")

        old_handoff = {
            "codex_workup.md": (target_dir / "codex_workup.md").read_text(encoding="utf-8"),
            "next_oracle_question.md": (target_dir / "next_oracle_question.md").read_text(encoding="utf-8"),
            "local_repair_report.md": (target_dir / "local_repair_report.md").read_text(encoding="utf-8"),
        }
        handoff_before = local_repair._snapshot_handoff_files(target_dir)
        (target_dir / "codex_workup.md").write_text("", encoding="utf-8")
        (target_dir / "next_oracle_question.md").unlink()
        (target_dir / "local_repair_report.md").write_text("truncated\n", encoding="utf-8")
        restore = local_repair._restore_handoff_files(target_dir, handoff_before)
        if not restore.get("triggered") or restore.get("errors"):
            raise AssertionError(f"handoff restore failed: {restore}")
        for name, expected in old_handoff.items():
            actual = (target_dir / name).read_text(encoding="utf-8")
            if actual != expected:
                raise AssertionError(f"{name} was not restored byte-for-byte")
        stale_after_restore = local_repair._postcheck_local_repair_artifacts(
            target_dir,
            codex_trace=trace,
            reserved_before=local_repair._snapshot_reserved_harness_files(target_dir),
            run_started_at="2999-01-01T00:00:00+00:00",
        )
        stale_after_restore_diagnostics = " ".join(stale_after_restore.get("diagnostics", []))
        if stale_after_restore.get("ok") or "was not refreshed by this local repair run" not in stale_after_restore_diagnostics:
            raise AssertionError(
                "restored old handoff should preserve context but fail current-run freshness gate: "
                f"{stale_after_restore}"
            )

        no_previous_dir = target_dir / "no_previous_handoff"
        no_previous_dir.mkdir()
        no_previous_before = local_repair._snapshot_handoff_files(no_previous_dir)
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            (no_previous_dir / name).write_text("new failed partial\n", encoding="utf-8")
        restore = local_repair._restore_handoff_files(no_previous_dir, no_previous_before)
        if sorted(restore.get("removed", [])) != sorted(
            ["codex_workup.md", "next_oracle_question.md", "local_repair_report.md"]
        ):
            raise AssertionError(f"new failed handoffs should be removed when no prior snapshot existed: {restore}")
        if any((no_previous_dir / name).exists() for name in local_repair.HANDOFF_FILES):
            raise AssertionError("restore left failed new handoff files behind")

        watchdog_stdout = target_dir / "watchdog.jsonl"
        inspection_event = {
            "item": {
                "type": "command_execution",
                "command": f"/bin/zsh -lc 'find {rel_target} -maxdepth 2 -type f | sort'",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": f"{rel_target}/results.json\n{rel_target}/scripts/check_slice.py\n",
            }
        }
        watchdog_stdout.write_text(
            json.dumps(inspection_event) + "\n" + json.dumps(replay_event) + "\n",
            encoding="utf-8",
        )
        (target_dir / "local_repair_report.md").write_text(
            "Pre-Oracle mathematical action: ran command "
            "`python3 {rel_target}/scripts/check_slice.py --case finite --json` before "
            "writing `next_oracle_question.md`; the finite certificate replay passed "
            "with sha256=abc123, but case 3 still needs an Oracle-supplied lemma. "
            "Also ran command `find {rel_target} -maxdepth 2 -type f | sort` and "
            "confirmed `results.json` plus `scripts/check_slice.py` are present.\n".format(
                rel_target=rel_target
            ),
            encoding="utf-8",
        )
        complete, details = local_repair._codex_artifacts_complete_while_process_alive(
            target_dir,
            watchdog_stdout,
            reserved_before=local_repair._snapshot_reserved_harness_files(target_dir),
            ignore_reserved_names={"science_gate.json", "outreach_impact_gate.json"},
            run_started_at="2000-01-01T00:00:00+00:00",
            idle_seconds=0,
        )
        if not complete or not details.get("postcheck", {}).get("ok"):
            raise AssertionError(f"artifact-complete watchdog did not accept valid handoff: {complete} {details}")

        stale_workup = target_dir / "codex_workup.md"
        stale_question = target_dir / "next_oracle_question.md"
        stale_report = target_dir / "local_repair_report.md"
        for path in (stale_workup, stale_question, stale_report):
            path.write_text(path.read_text(encoding="utf-8") + "\nolder handoff\n", encoding="utf-8")
        incomplete_stdout = target_dir / "incomplete_handoff.jsonl"
        incomplete_stdout.write_text(json.dumps(replay_event) + "\n", encoding="utf-8")
        incomplete, incomplete_details = local_repair._codex_handoff_incomplete_after_local_work(
            target_dir,
            incomplete_stdout,
            reserved_before=local_repair._snapshot_reserved_harness_files(target_dir),
            ignore_reserved_names={"science_gate.json", "outreach_impact_gate.json"},
            run_started_at="2999-01-01T00:00:00+00:00",
            idle_seconds=0,
        )
        if not incomplete:
            raise AssertionError(
                "incomplete-handoff watchdog should reject completed local math without refreshed handoff: "
                f"{incomplete_details}"
            )
        if not incomplete_details.get("postcheck") or incomplete_details["postcheck"].get("ok"):
            raise AssertionError(f"incomplete-handoff watchdog did not preserve failing postcheck: {incomplete_details}")
        if int(incomplete_details.get("codex_command_trace", {}).get("mathematical_action_command_count") or 0) <= 0:
            raise AssertionError(f"incomplete-handoff watchdog lost math command trace: {incomplete_details}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
