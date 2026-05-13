#!/usr/bin/env python3
"""Codex local workup/follow-up/replay for outreach math targets.

Oracle/ChatGPT is used for search and deep mathematical reasoning.  It should
not be asked to pretend that repository-local replay scripts exist, and it
should not receive a bare board card when Codex can first inspect the local
workspace.  Before each Oracle batch, and again after any substantive Oracle
claim, this script invokes Codex on the local workspace to produce a target
workup, run feasible checks, and create or repair verifier/replay packets.

Hard boundaries:
  - never sends/posts/emails anything externally;
  - never commits or pushes;
  - does not ask Oracle;
  - if a referenced claim cannot honestly be reproduced, writes a target-local
    failure_analysis.md when the claim is invalid, or records a precise
    local_repair_report.md and codex_workup.md handoff when the remaining gap
    is a proof/Oracle question rather than a local-computation question.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
TARGETS_DIR = SCRIPT_DIR / "targets"
STATE_DIR = SCRIPT_DIR / "outreach_state"
LOG_DIR = STATE_DIR / "local_repair_logs"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"

CODEX_BIN = shutil.which("codex") or "/opt/homebrew/bin/codex"

sys_path_added = False
try:
    import sys

    sys.path.insert(0, str(SCRIPT_DIR))
    sys_path_added = True
    from outreach_board_parser import parse_board  # noqa: E402
    from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: E402
except Exception as exc:  # noqa: BLE001
    parse_board = None  # type: ignore[assignment]
    science_gate_evaluate = None  # type: ignore[assignment]
    IMPORT_ERROR = str(exc)
else:
    IMPORT_ERROR = ""


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _read_text(path: Path, *, limit: int = 16000) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    if len(text) <= limit:
        return text
    return text[: limit // 2] + "\n\n...[middle truncated]...\n\n" + text[-limit // 2 :]


def _coerce_text(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _terminate_process_group(proc: subprocess.Popen, *, grace_seconds: float = 5.0) -> None:
    """Terminate a spawned worker and its children.

    The Codex CLI is a node wrapper around a native child.  Plain
    subprocess.run(..., timeout=...) can leave the native child alive after the
    Python parent times out, which makes outreach_local_repair appear active
    for hours and blocks the research loop.  Spawn workers in their own process
    group and kill the whole group on timeout.
    """
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except (ProcessLookupError, OSError):
        return
    try:
        proc.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, OSError):
        pass


def _target_file_manifest(target_dir: Path) -> str:
    if not target_dir.exists():
        return "(target directory missing)"
    rows: list[str] = []
    for path in sorted(target_dir.glob("*")):
        if not path.is_file():
            continue
        try:
            stat = path.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime, timezone.utc).isoformat(timespec="seconds")
        except OSError:
            size = -1
            mtime = "unknown"
        rows.append(f"- {path.relative_to(REPO_ROOT)} ({size} bytes, mtime={mtime})")
    return "\n".join(rows) or "(no target-local files)"


def _is_transport_stub_response(text: str) -> bool:
    stripped = (text or "").strip()
    if not stripped:
        return True
    lowered = stripped.lower()
    markers = (
        "error: task cancelled by server",
        "error (re-extract):",
        "error: empty response",
        "empty response (timeout or extraction failure)",
        "no assistant output after",
        "re-extract: nothing meaningful",
        "re-extract: empty response",
        "server unreachable",
    )
    if any(lowered.startswith(marker) for marker in markers):
        return True
    return len(stripped) < 80 and "cancelled" in lowered and "server" in lowered


def _claim_packet_oracle_response(text: str) -> str:
    marker = "## Oracle Response"
    idx = text.find(marker)
    if idx < 0:
        return text
    response = text[idx + len(marker) :].strip()
    return response


def _latest_claim_packets(target_dir: Path, *, count: int = 3, limit_each: int = 12000) -> str:
    if not target_dir.exists():
        return "(target directory missing)"
    all_packets = sorted(
        target_dir.glob("oracle_claim_packet_*.md"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    packets: list[Path] = []
    skipped_transport = 0
    for path in all_packets:
        text = _read_text(path, limit=limit_each)
        if _is_transport_stub_response(_claim_packet_oracle_response(text)):
            skipped_transport += 1
            continue
        packets.append(path)
        if len(packets) >= count:
            break
    if not packets:
        if skipped_transport:
            return f"(no substantive Oracle claim packets; ignored {skipped_transport} transport/error packet(s))"
        return "(no Oracle claim packets yet)"
    chunks: list[str] = []
    if skipped_transport:
        chunks.append(f"(ignored {skipped_transport} newer transport/error packet(s))")
    for path in packets:
        chunks.append(f"## {path.name}\n\n{_read_text(path, limit=limit_each) or '(unreadable)'}")
    return "\n\n---\n\n".join(chunks)


def _compact_gate(gate: dict) -> str:
    fields = {
        "status": gate.get("status", ""),
        "next_action": gate.get("next_action", ""),
        "failure_kind": gate.get("failure_kind", ""),
        "contribution_type": gate.get("contribution_type", ""),
        "verification_status": gate.get("verification_status", ""),
        "closure_status": gate.get("closure_status", ""),
        "missing": gate.get("missing", []) or [],
        "reasons": gate.get("reasons", []) or [],
        "terminal_artifact": gate.get("terminal_artifact", ""),
        "verifier": gate.get("verifier", ""),
        "progress_metric": gate.get("progress_metric", ""),
    }
    return json.dumps(fields, ensure_ascii=False, indent=2)


def _json_from_stdout(text: str) -> dict:
    """Parse the first JSON object emitted by a target-local verifier."""
    stripped = (text or "").strip()
    if not stripped:
        return {}
    try:
        payload = json.loads(stripped)
        return payload if isinstance(payload, dict) else {}
    except json.JSONDecodeError:
        pass
    match = re.search(r"\{.*\}", stripped, flags=re.S)
    if not match:
        return {}
    try:
        payload = json.loads(match.group(0))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _verifier_stdout_passed(payload: dict, raw_stdout: str = "") -> bool:
    if not isinstance(payload, dict):
        payload = {}
    if str(payload.get("result") or "").strip().lower() in {"pass", "passed", "ok", "verified"}:
        return True
    if str(payload.get("verify_status") or "").upper() == "OK":
        mismatches = payload.get("verify_mismatches")
        return isinstance(mismatches, list) and not mismatches
    raw_lower = (raw_stdout or "").strip().lower()
    if raw_lower and (
        "certificate checks passed" in raw_lower
        or "verifier checks passed" in raw_lower
        or "checks passed" in raw_lower
        or "all_records_pass=true" in raw_lower
        or "status=unsat" in raw_lower
    ):
        return True
    return False


def _codex_jsonl_local_command_trace(stdout_path: Path, target_dir: Path) -> dict:
    """Summarize target-specific command executions from the Codex JSONL log.

    The markdown handoff is useful, but it is still prose.  The pre-Oracle
    harness also needs a machine-observed trace that Codex actually touched the
    target-local workspace during this run.
    """
    stdout_path = stdout_path.resolve()
    target_dir = target_dir.resolve()
    target_rel = str(target_dir.relative_to(REPO_ROOT))
    interesting_commands: list[dict] = []
    command_count = 0
    target_command_count = 0
    completed_target_command_count = 0
    inspection_command_count = 0
    replay_command_count = 0
    negative_artifact_search_count = 0
    output_markers = (
        "self-tests passed",
        "all_records_pass",
        "unique_canonical_hashes",
        "checked ",
        "passed",
        "failed",
        "sha256",
        "no such file",
        "unsat",
        "sat",
        "vertices",
        "edges",
        "clauses",
    )
    inspection_command_markers = (
        "find ",
        "rg ",
        "ls ",
        "stat ",
        "sed -n",
        "cat ",
        "wc ",
        "python3 -m json.tool",
        "git status",
    )
    replay_command_markers = (
        "python3 ",
        "python ",
        "pytest",
        "lean ",
        "lake ",
        "sage ",
        "magma ",
        "gap ",
        "node ",
        "npm ",
        "unzip ",
        "sha256sum",
        "shasum",
        "drat",
        "lrat",
        "kissat",
        "cadical",
        "glucose",
    )
    negative_search_markers = (
        "-iname ",
        "-name ",
        "*.cnf",
        "*.drat",
        "*.lrat",
        "*.rup",
        "*.zip",
        "*.g6",
        "*.edge",
        "*.vtx",
        "manifest.json",
        "sha256sums",
    )
    try:
        lines = stdout_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError as exc:
        return {
            "ok": False,
            "reason": f"missing Codex stdout JSONL log: {exc}",
            "stdout_log": str(stdout_path.relative_to(REPO_ROOT)) if stdout_path.exists() else str(stdout_path),
            "command_count": 0,
            "target_command_count": 0,
            "commands": [],
        }
    for line in lines:
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        item = event.get("item") if isinstance(event, dict) else None
        if not isinstance(item, dict):
            continue
        if item.get("type") != "command_execution":
            continue
        command = str(item.get("command") or "")
        command_count += 1
        output = str(item.get("aggregated_output") or "")
        mentions_target = target_rel in command or target_rel in output or target_dir.name in command
        if not mentions_target:
            continue
        target_command_count += 1
        if len(interesting_commands) < 12:
            interesting_commands.append(
                {
                    "command": command,
                    "exit_code": item.get("exit_code"),
                    "status": item.get("status"),
                    "output_head": output[:500],
                }
            )
        command_lower = command.lower()
        output_lower = output.lower()
        if item.get("status") == "completed":
            completed_target_command_count += 1
        if any(marker in command_lower for marker in inspection_command_markers):
            inspection_command_count += 1
        if any(marker in command_lower for marker in replay_command_markers):
            replay_command_count += 1
        if any(marker in command_lower for marker in negative_search_markers) and not output.strip():
            negative_artifact_search_count += 1
        elif (
            any(marker in command_lower for marker in negative_search_markers)
            and ("no such file" in output_lower or "not found" in output_lower or "missing" in output_lower)
        ):
            negative_artifact_search_count += 1
    if target_command_count <= 0:
        return {
            "ok": False,
            "reason": "Codex JSONL log contains no command_execution for this target directory",
            "stdout_log": str(stdout_path.relative_to(REPO_ROOT)),
            "command_count": command_count,
            "target_command_count": target_command_count,
            "commands": interesting_commands,
        }
    has_completed_target_command = any(cmd.get("status") == "completed" for cmd in interesting_commands)
    if not has_completed_target_command:
        return {
            "ok": False,
            "reason": "Codex target command trace has no completed command",
            "stdout_log": str(stdout_path.relative_to(REPO_ROOT)),
            "command_count": command_count,
            "target_command_count": target_command_count,
            "completed_target_command_count": completed_target_command_count,
            "commands": interesting_commands,
        }
    has_evidence_output = any(
        any(marker in str(cmd.get("output_head") or "").lower() for marker in output_markers)
        for cmd in interesting_commands
    )
    return {
        "ok": True,
        "stdout_log": str(stdout_path.relative_to(REPO_ROOT)),
        "command_count": command_count,
        "target_command_count": target_command_count,
        "completed_target_command_count": completed_target_command_count,
        "inspection_command_count": inspection_command_count,
        "replay_command_count": replay_command_count,
        "negative_artifact_search_count": negative_artifact_search_count,
        "has_evidence_output": has_evidence_output,
        "commands": interesting_commands,
    }


def _extract_next_oracle_question_from_workup(text: str) -> str:
    if not text:
        return ""
    match = re.search(r"(?ims)^##\s+Next\s+Oracle\s+question\s*$\s*(.*?)(?=^##\s+|\Z)", text)
    if not match:
        return ""
    return match.group(1).strip()


def _extract_workup_section(text: str, heading: str) -> str:
    if not text:
        return ""
    pattern = re.compile(
        r"(?ims)^##\s+"
        + re.escape(heading).replace(r"\ ", r"\s+")
        + r"\s*$"
        + r"(.*?)"
        + r"(?=^##\s+|\Z)"
    )
    match = pattern.search(text)
    return match.group(1).strip() if match else ""


def _is_concrete_next_oracle_question(question: str) -> bool:
    q = (question or "").strip()
    if len(q) < 120:
        return False
    lowered = q.lower()
    generic_markers = (
        "continue research",
        "继续研究",
        "do the next step",
        "lower the progress metric",
        "provide metadata",
        "review the board",
        "look into this problem",
        "make progress",
        "find something useful",
    )
    if any(marker in lowered for marker in generic_markers):
        return False
    concrete_markers = (
        "prove",
        "disprove",
        "certificate",
        "construction",
        "counterexample",
        "verifier",
        "exact",
        "bound",
        "obstruction",
        "cnf",
        "lrat",
        "drat",
        "graph",
        "lemma",
        "theorem",
        "compute",
        "enumerate",
        "check",
    )
    return any(marker in lowered for marker in concrete_markers)


def _workup_has_local_execution_trace(text: str) -> tuple[bool, str]:
    """Check that Codex actually processed the target before Oracle.

    This mirrors the research-loop pre-Oracle gate, but runs immediately after
    the Codex local worker returns.  The harness must not trust the worker's
    final prose unless the target-local files exist and contain a replay/check
    trace.
    """
    stripped = (text or "").strip()
    if len(stripped) < 500:
        return False, "codex_workup.md too short to show local processing"
    lowered = stripped.lower()
    required_sections = (
        "## local evidence checked",
        "## commands run",
        "## verifier/artifact status",
        "## proof obligations still open",
        "## next oracle question",
    )
    missing_sections = [section for section in required_sections if section not in lowered]
    if missing_sections:
        return False, "codex_workup.md missing sections: " + ", ".join(missing_sections)
    local_body = _extract_workup_section(stripped, "Local evidence checked")
    commands_body = _extract_workup_section(stripped, "Commands run")
    artifact_body = _extract_workup_section(stripped, "Verifier/artifact status")
    if len(local_body) < 80:
        return False, "Local evidence checked section too thin to prove target inspection"
    if len(commands_body) < 80:
        return False, "Commands run section too thin to prove local execution"
    if len(artifact_body) < 80:
        return False, "Verifier/artifact status section too thin to prove artifact review"
    command_markers = (
        "```",
        "$ ",
        "python3 ",
        "python ",
        "rg ",
        "find ",
        "git status",
        "sed -n",
        "cat ",
        "ls ",
        "date ",
        "lean ",
        "lake ",
        "sage ",
        "magma ",
        "gap ",
        "node ",
        "npm ",
        "pytest",
        "curl ",
        "unzip ",
        "sha256sum",
    )
    commands_lower = commands_body.lower()
    if not any(marker in commands_lower for marker in command_markers):
        return False, "Commands run section lacks concrete shell/tool commands"
    inspection_markers = (
        "inspected",
        "searched",
        "found",
        "confirmed",
        "checked",
        "ran",
        "replayed",
        "no oracle claim",
        "missing",
        "absent",
    )
    local_artifact_text = f"{local_body}\n{artifact_body}".lower()
    if not any(marker in local_artifact_text for marker in inspection_markers):
        return False, "local evidence/artifact sections do not describe an actual inspection result"
    trace_markers = (
        "command",
        "ran",
        "checked",
        "verified",
        "passed",
        "failed",
        "missing",
        "not run",
        "no local",
        "no oracle claim",
        "results.json",
        "verifier",
        "artifact",
        "python",
    )
    if not any(marker in lowered for marker in trace_markers):
        return False, "codex_workup.md lacks local command/check/artifact trace"
    return True, ""


def _text_has_concrete_local_fact(text: str) -> bool:
    lowered = (text or "").lower()
    fact_markers = (
        "sha-256",
        "sha256",
        "unsat",
        " sat",
        "exit 0",
        "exited 0",
        "vertices",
        "edges",
        "clauses",
        "variables",
        "witness",
        "counterexample",
        "hash",
        "cnf",
        "drat",
        "lrat",
        "rup",
        "graph6",
        ".g6",
        ".cnf",
        ".drat",
        ".lrat",
        ".rup",
        ".zip",
        ".edge",
        ".vtx",
        ".json",
        ".py",
        "found no",
        "no `",
        "not present",
        "absent",
        "missing",
        "failed at the first local check",
        "verified",
        "replayed",
        "checked",
    )
    return any(marker in lowered for marker in fact_markers)


def _substantive_local_workup_check(
    target_dir: Path,
    workup: str,
    question: str,
    report: str,
    *,
    codex_trace: dict | None,
) -> dict:
    """Decide whether the handoff contains real target work, not metadata only."""
    local_body = _extract_workup_section(workup, "Local evidence checked")
    commands_body = _extract_workup_section(workup, "Commands run")
    artifact_body = _extract_workup_section(workup, "Verifier/artifact status")
    obligations_body = _extract_workup_section(workup, "Proof obligations still open")
    publication_body = _extract_workup_section(workup, "Publication value / re-scope judgment")
    evidence_blob = "\n".join(
        [local_body, commands_body, artifact_body, obligations_body, publication_body, report]
    )
    target_name = target_dir.name.lower()
    diagnostics: list[str] = []

    if target_name not in commands_body.lower() and target_name not in report.lower():
        diagnostics.append("commands/report do not mention the target directory")
    if not _text_has_concrete_local_fact(evidence_blob):
        diagnostics.append("workup/report lacks concrete local facts from replay, search, hashes, SAT/CNF, paths, or failures")
    if not _text_has_concrete_local_fact(question):
        diagnostics.append("next_oracle_question.md does not cite a concrete local fact Oracle must respect")

    if codex_trace is not None:
        replay_count = int(codex_trace.get("replay_command_count") or 0)
        inspection_count = int(codex_trace.get("inspection_command_count") or 0)
        negative_count = int(codex_trace.get("negative_artifact_search_count") or 0)
        evidence_output = bool(codex_trace.get("has_evidence_output"))
        if inspection_count <= 0:
            diagnostics.append("Codex command trace lacks target inspection commands")
        if replay_count <= 0 and negative_count <= 0 and not evidence_output:
            diagnostics.append(
                "Codex command trace lacks replay/check commands, negative artifact searches, or evidence output"
            )

    return {
        "ok": not diagnostics,
        "diagnostics": diagnostics,
        "question_cites_local_fact": _text_has_concrete_local_fact(question),
        "workup_has_concrete_local_fact": _text_has_concrete_local_fact(evidence_blob),
    }


def _collect_missing_referenced_local_paths(value: object) -> list[str]:
    """Find target-local artifact references in JSON that do not exist."""
    missing: list[str] = []
    if isinstance(value, dict):
        for key, child in value.items():
            key_lower = str(key).lower()
            if (
                key_lower.startswith("claimed_")
                or key_lower.startswith("missing_")
                or "not_replayed" in key_lower
                or "unverified" in key_lower
                or "failed" in key_lower
            ):
                continue
            missing.extend(_collect_missing_referenced_local_paths(child))
        return missing
    if isinstance(value, list):
        for child in value:
            missing.extend(_collect_missing_referenced_local_paths(child))
        return missing
    if not isinstance(value, str):
        return missing
    text = value.strip()
    if not text.startswith("tools/community-outreach/"):
        return missing
    if any(ch in text for ch in "*?[]"):
        return missing
    path = REPO_ROOT / text
    if not path.exists():
        missing.append(text)
    return missing


def _postcheck_local_repair_artifacts(target_dir: Path, *, codex_trace: dict | None = None) -> dict:
    target_dir = target_dir.resolve()
    diagnostics: list[str] = []

    workup_path = target_dir / "codex_workup.md"
    workup = _read_text(workup_path, limit=40000)
    if not workup:
        diagnostics.append("missing codex_workup.md")
    else:
        ok, reason = _workup_has_local_execution_trace(workup)
        if not ok:
            diagnostics.append(reason)

    question_path = target_dir / "next_oracle_question.md"
    question = _read_text(question_path, limit=10000).strip()
    if not question:
        question = _extract_next_oracle_question_from_workup(workup)
    if not _is_concrete_next_oracle_question(question):
        diagnostics.append("missing concrete next_oracle_question.md")

    report_path = target_dir / "local_repair_report.md"
    report = _read_text(report_path, limit=12000)
    if len(report.strip()) < 200:
        diagnostics.append("missing or too-short local_repair_report.md")
    else:
        report_lower = report.lower()
        if "command" not in report_lower and "ran" not in report_lower and "checked" not in report_lower:
            diagnostics.append("local_repair_report.md lacks command/check summary")

    results_path = target_dir / "results.json"
    if results_path.exists():
        try:
            results_payload = json.loads(results_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            diagnostics.append(f"invalid results.json: {exc}")
        else:
            missing_refs = sorted(set(_collect_missing_referenced_local_paths(results_payload)))
            if missing_refs:
                diagnostics.append(
                    "results.json references missing local artifacts: " + ", ".join(missing_refs[:8])
                )

    if codex_trace is not None and not codex_trace.get("ok"):
        diagnostics.append(str(codex_trace.get("reason") or "Codex command trace missing"))
    substantive = _substantive_local_workup_check(
        target_dir,
        workup,
        question,
        report,
        codex_trace=codex_trace,
    )
    if not substantive.get("ok"):
        diagnostics.extend(str(item) for item in substantive.get("diagnostics", []))

    return {
        "ok": not diagnostics,
        "diagnostics": diagnostics,
        "workup_path": str(workup_path.relative_to(REPO_ROOT)),
        "next_oracle_question_path": str(question_path.relative_to(REPO_ROOT)),
        "local_repair_report_path": str(report_path.relative_to(REPO_ROOT)),
        "codex_command_trace": codex_trace or {},
        "substantive_local_work": substantive,
    }


def _candidate_verifier_scripts(target_dir: Path) -> list[Path]:
    candidates: list[Path] = []
    standard = target_dir / "verify_results.py"
    if standard.exists():
        candidates.append(standard)
    for path in sorted(target_dir.glob("verify*_results.py")):
        if path not in candidates:
            candidates.append(path)
    for path in sorted(target_dir.glob("verify*.py")):
        if path not in candidates:
            candidates.append(path)
    return candidates


def _candidate_verifier_commands(verifier: Path, results_path: Path) -> list[list[str]]:
    rel_verifier = str(verifier.relative_to(REPO_ROOT))
    rel_results = str(results_path.relative_to(REPO_ROOT))
    if verifier.name == "verify_results.py":
        return [
            ["python3", rel_verifier, "--json"],
            ["python3", rel_verifier, rel_results],
            ["python3", rel_verifier],
        ]
    return [
        ["python3", rel_verifier, rel_results],
        ["python3", rel_verifier, "--json"],
        ["python3", rel_verifier],
    ]


def _results_artifact_replay_commands(target_dir: Path, results_path: Path) -> list[list[str]]:
    """Build replay commands from artifact commands already recorded in results.

    Target-specific Codex workers often create generators/checkers whose names
    are not `verify*.py`.  If their command is recorded in `results.json`, the
    harness should replay that exact target-local artifact before falling back
    to generic verifier guessing.
    """
    try:
        payload = json.loads(results_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    if not isinstance(payload, dict):
        return []
    raw_commands = payload.get("commands")
    if not isinstance(raw_commands, list):
        return []
    target_rel = str(target_dir.relative_to(REPO_ROOT))
    commands: list[list[str]] = []
    for item in raw_commands:
        if not isinstance(item, dict):
            continue
        command = str(item.get("command") or "").strip()
        if not command.startswith("python3 "):
            continue
        if target_rel not in command:
            continue
        # These commands are written by target-local Codex workers.  Run them
        # through the shell so quoted graph6/path arguments are preserved.
        commands.append(["/bin/zsh", "-lc", command])
    # Prefer newer, more specific artifact checks such as generated slices over
    # older bulk replays.  Bulk lower-bound audits can be expensive and may
    # rewrite results.json before the newer artifact is audited.
    commands.reverse()
    return commands


def _record_target_verifier_audit(todo_id: str, target_dir: Path) -> dict:
    """Run a target-local verifier, if present, and record its result.

    Codex workers can create good replay scripts while forgetting to update the
    exact `verifier_audit` schema the deterministic science gate reads.  This
    harness-level pass bridges that gap without trusting prose: it runs the
    target-local verifier itself and appends the parsed machine result to
    results.json.
    """
    results_path = target_dir / "results.json"
    verifiers = _candidate_verifier_scripts(target_dir)
    if not verifiers or not results_path.exists():
        artifact_commands = _results_artifact_replay_commands(target_dir, results_path) if results_path.exists() else []
        if not artifact_commands:
            return {"ran": False, "reason": "missing verify*_results.py/results artifact commands or results.json"}
    else:
        artifact_commands = _results_artifact_replay_commands(target_dir, results_path)

    run: dict | None = None
    passed = False
    attempted: list[dict] = []
    replay_queue: list[tuple[str, list[str]]] = []
    for idx, cmd in enumerate(artifact_commands):
        replay_queue.append((f"{todo_id}:{target_dir.name}:results_command_{idx}", cmd))
    for verifier in verifiers:
        for cmd in _candidate_verifier_commands(verifier, results_path):
            replay_queue.append((f"{todo_id}:{target_dir.name}:{verifier.name}", cmd))
    for label, cmd in replay_queue:
        started = _now_iso()
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=900,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        stdout_payload = _json_from_stdout(proc.stdout)
        candidate_run = {
            "label": label,
            "command": " ".join(cmd),
            "started_at": started,
            "finished_at": _now_iso(),
            "exit_status": proc.returncode,
            "stdout": stdout_payload if stdout_payload else {"raw": (proc.stdout or "")[:4000]},
            "stderr": (proc.stderr or "")[:4000],
        }
        attempted.append(candidate_run)
        if proc.returncode == 0 and _verifier_stdout_passed(stdout_payload, proc.stdout):
            run = candidate_run
            passed = True
            break
    if run is None:
        run = attempted[-1]
    try:
        data = json.loads(results_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"ran": True, "recorded": False, "run": run, "reason": "invalid results.json"}
    if not isinstance(data, dict):
        return {"ran": True, "recorded": False, "run": run, "reason": "results.json is not an object"}
    audit = data.setdefault("verifier_audit", {})
    if not isinstance(audit, dict):
        audit = {}
        data["verifier_audit"] = audit
    runs = audit.setdefault("runs", [])
    if not isinstance(runs, list):
        runs = []
        audit["runs"] = runs
    # Replace the prior harness run for this verifier so results.json does not
    # grow unboundedly during a long autonomous loop.
    runs[:] = [
        existing
        for existing in runs
        if not (
            isinstance(existing, dict)
            and existing.get("label") == run["label"]
        )
    ]
    runs.append(run)
    audit["updated_at"] = _now_iso()
    audit["latest_passed"] = passed
    results_path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return {"ran": True, "recorded": True, "passed": passed, "run": run, "attempted": attempted}


def build_prompt(todo_id: str, *, gate: dict, target_dir: Path) -> str:
    if parse_board is None:
        title = ""
        statement = ""
        source = ""
    else:
        todos = parse_board(BOARD_PATH)
        todo = todos[todo_id]
        title = todo.title
        statement = todo.statement
        source = todo.source
    research_md = _read_text(target_dir / "research.md", limit=12000)
    codex_workup = _read_text(target_dir / "codex_workup.md", limit=12000)
    results_json = _read_text(target_dir / "results.json", limit=18000)
    profile_json = _read_text(target_dir / "profile.json", limit=8000)
    return f"""You are Codex running as the LOCAL_CODEX_WORKUP worker for the Omega outreach open-problem pipeline.

Target: {todo_id} — {title}
Source: {source}

The Oracle/ChatGPT stage supplies mathematical ideas, search, and deep proof attempts. Your job is the local counterpart before and after Oracle: inspect the target on disk, run any feasible local computation/replay, create or repair verifier scripts when honest, and write a compact `codex_workup.md` that tells Oracle exactly what remains to prove or compute.

Do not ask the user for clarification. Do not contact Oracle. Do not send email, post comments, call gh, commit, or push. Keep edits inside `tools/community-outreach/targets/{target_dir.name}/` unless a tiny pipeline-local support change is absolutely required.

Scientific honesty rule:
- Always create or refresh `tools/community-outreach/targets/{target_dir.name}/codex_workup.md`; this is the main handoff Oracle will read next.
- Always create or refresh `tools/community-outreach/targets/{target_dir.name}/next_oracle_question.md`; this must be the exact concise prompt that should be sent to Oracle next, based on your local workup.
- It is not enough to append board metadata or draft a better question. Before writing the next Oracle question, actually process the target: inspect the target files, identify the newest testable claim if present, run a feasible replay/check or explicitly record why no local replay is possible yet.
- Do not mechanically repeat an expensive verifier if a fresh `results.json` or prior command log in this same target already records the exact replay result you need. In that case, inspect and cite the fresh artifact, run only a cheap sanity check such as JSON parsing or script self-tests if useful, then write the next Oracle handoff.
- If the only honest local computation would exceed the current timeout, write a bounded-progress `local_repair_report.md` explaining the partial computation, the command that would continue it, and the exact Oracle question. Do not leave the pipeline silent while waiting for an unbounded local run.
- If the target-local data is enough to implement the missing verifier/replay artifact, implement it and run it.
- If the latest Oracle packet contains a concrete construction, finite certificate, recurrence, SAT/ILP formulation, exhaustive finite case, or numerical claim, try to replay it locally and record the exact command/result.
- If a testable Oracle claim is false or incomplete, write `tools/community-outreach/targets/{target_dir.name}/failure_analysis.md` explaining the first failed check, and repair `results.json` so unsupported local artifact references are removed or marked as planned/unverified.
- If the remaining gap is a pure proof/strategy gap and there is no honest local computation to run, do not fabricate work. Write `tools/community-outreach/targets/{target_dir.name}/local_repair_report.md` with a concise "no local replay available yet" note and the exact next question that should go back to Oracle.
- The goal is not to make the gate pass by weakening standards. The goal is to make the next gate decision truthful and actionable.
- For non-collaboration targets, keep asking: would this become a publicly reviewable result, note, certificate, verifier, construction, obstruction, or useful failure analysis? If not, recommend re-scope or deprioritization in the workup.

Science gate snapshot:
```json
{_compact_gate(gate)}
```

Target file manifest:
{_target_file_manifest(target_dir)}

Problem statement:
{statement}

Existing profile.json excerpt:
```json
{profile_json or "{}"}
```

Existing results.json excerpt:
```json
{results_json or "{}"}
```

Existing research.md excerpt:
```markdown
{research_md or "(missing)"}
```

Existing codex_workup.md excerpt:
```markdown
{codex_workup or "(missing)"}
```

Latest Oracle claim packets:
```markdown
{_latest_claim_packets(target_dir)}
```

Required output actions:
1. Refresh `codex_workup.md` with these exact sections:
   - `# Codex Workup`
   - `## Target claim now`
   - `## Local evidence checked`
   - `## Commands run`
   - `## Verifier/artifact status`
   - `## Proof obligations still open`
   - `## Next Oracle question`
   - `## Publication value / re-scope judgment`
2. Create `next_oracle_question.md` as a short, direct Oracle prompt:
   - no board metadata dump;
   - no generic "continue research";
   - must cite at least one local fact from `Local evidence checked`, `Commands run`, or `Verifier/artifact status`;
   - include only the exact theorem/certificate/proof gap to attack next;
   - include local computation results Oracle must respect;
   - ask for one concrete artifact/proof move/checkable obstruction.
3. Identify the newest testable Oracle claim, if any; if there is no Oracle claim yet, build the initial local proof/computation plan from the board/profile artifacts.
4. Edit or create target-local scripts/data only when they are needed for an honest replay/check.
5. Run the relevant scripts locally when feasible.
6. Update `results.json` only to reflect actually reproducible evidence.
7. Leave a short `local_repair_report.md` in the target directory summarizing what you changed, what command you ran, what was confirmed/refuted, and what exact question should go back to Oracle.
8. Stop. Do not commit.
"""


def _run_science_gate(todo_id: str, *, write_ledger: bool = True) -> dict:
    if science_gate_evaluate is not None and parse_board is not None:
        todos = parse_board(BOARD_PATH)
        gate = science_gate_evaluate(todos[todo_id])
        if write_ledger:
            out = TARGETS_DIR / todos[todo_id].slug() / "science_gate.json"
            out.write_text(json.dumps(gate.to_dict(), ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return gate.to_dict()
    cmd = ["python3", str(SCRIPT_DIR / "outreach_science_gate.py"), "--todo-id", todo_id, "--json"]
    if write_ledger:
        cmd.insert(-1, "--write-ledger")
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=180, check=False)
    if proc.returncode != 0:
        return {"error": proc.stderr or proc.stdout, "returncode": proc.returncode}
    payload = json.loads(proc.stdout or "{}")
    if isinstance(payload, list):
        return payload[0] if payload else {}
    return payload


def run_local_repair(todo_id: str, *, timeout: int) -> dict:
    if IMPORT_ERROR:
        return {"ok": False, "error": f"import failed: {IMPORT_ERROR}"}
    if parse_board is None:
        return {"ok": False, "error": "parse_board unavailable"}
    todos = parse_board(BOARD_PATH)
    if todo_id not in todos:
        return {"ok": False, "error": f"{todo_id} not found"}
    todo = todos[todo_id]
    target_dir = TARGETS_DIR / todo.slug()
    target_dir.mkdir(parents=True, exist_ok=True)
    gate_before = _run_science_gate(todo_id, write_ledger=True)
    if str(gate_before.get("status") or "") in {"WRITEBACK_READY", "CLOSE_TARGET"}:
        report = {
            "ok": True,
            "todo_id": todo_id,
            "slug": todo.slug(),
            "started_at": _now_iso(),
            "finished_at": _now_iso(),
            "returncode": 0,
            "gate_before": gate_before,
            "gate_after": gate_before,
            "shortcut": "science_gate_already_terminal",
        }
        state_path = target_dir / "local_repair_last.json"
        state_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return report
    verifier_audit_before = _record_target_verifier_audit(todo_id, target_dir)
    if verifier_audit_before.get("passed"):
        gate_after_audit = _run_science_gate(todo_id, write_ledger=True)
        if str(gate_after_audit.get("status") or "") in {"WRITEBACK_READY", "CLOSE_TARGET"}:
            report = {
                "ok": True,
                "todo_id": todo_id,
                "slug": todo.slug(),
                "started_at": _now_iso(),
                "finished_at": _now_iso(),
                "returncode": 0,
                "verifier_audit": verifier_audit_before,
                "gate_before": gate_before,
                "gate_after": gate_after_audit,
                "shortcut": "preexisting_verifier_audit_reached_terminal_gate",
            }
            state_path = target_dir / "local_repair_last.json"
            state_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            return report
        if gate_after_audit.get("status") != gate_before.get("status") or gate_after_audit.get(
            "verification_status"
        ) != gate_before.get("verification_status"):
            # Verifier replay is real local work, but a non-terminal gate still
            # needs a fresh Codex handoff before Oracle is asked anything.
            gate_before = gate_after_audit
    prompt = build_prompt(todo_id, gate=gate_before, target_dir=target_dir)

    if not CODEX_BIN or not Path(CODEX_BIN).exists():
        return {"ok": False, "error": f"codex CLI not found at {CODEX_BIN}", "gate_before": gate_before}

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    tag = f"local_repair_{todo_id}_{_now_tag()}"
    prompt_path = LOG_DIR / f"{tag}.prompt.txt"
    stdout_path = LOG_DIR / f"{tag}.stdout.jsonl"
    stderr_path = LOG_DIR / f"{tag}.stderr.txt"
    output_path = LOG_DIR / f"{tag}.out.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, suffix=".txt") as tmp:
        codex_out = Path(tmp.name)
    cmd = [
        CODEX_BIN,
        "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "--json",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(codex_out),
        "-",
    ]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    started = _now_iso()
    try:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=str(REPO_ROOT),
            env=env,
            text=True,
            encoding="utf-8",
            errors="replace",
            start_new_session=True,
        )
        try:
            stdout, stderr = proc.communicate(input=prompt, timeout=timeout)
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            _terminate_process_group(proc)
            stdout, stderr = proc.communicate()
            rc = 124
            stderr = (stderr or "") + f"\nTIMEOUT after {timeout}s; terminated Codex process group\n"
        stdout_path.write_text(stdout or "", encoding="utf-8")
        stderr_path.write_text(stderr or "", encoding="utf-8")
    except subprocess.TimeoutExpired as exc:
        rc = 124
        stdout_path.write_text(_coerce_text(exc.stdout), encoding="utf-8")
        stderr_path.write_text(
            _coerce_text(exc.stderr) + f"\nTIMEOUT after {timeout}s\n",
            encoding="utf-8",
        )
    raw = ""
    try:
        if codex_out.exists():
            raw = codex_out.read_text(encoding="utf-8", errors="replace")
    finally:
        try:
            codex_out.unlink()
        except OSError:
            pass
    output_path.write_text(raw or "", encoding="utf-8")
    verifier_audit = _record_target_verifier_audit(todo_id, target_dir)
    gate_after = _run_science_gate(todo_id, write_ledger=True)
    codex_command_trace = _codex_jsonl_local_command_trace(stdout_path, target_dir)
    postcheck = _postcheck_local_repair_artifacts(target_dir, codex_trace=codex_command_trace)
    ok = rc == 0 and bool(postcheck.get("ok"))
    report = {
        "ok": ok,
        "todo_id": todo_id,
        "slug": todo.slug(),
        "started_at": started,
        "finished_at": _now_iso(),
        "returncode": rc,
        "prompt_log": str(prompt_path.relative_to(REPO_ROOT)),
        "stdout_log": str(stdout_path.relative_to(REPO_ROOT)),
        "stderr_log": str(stderr_path.relative_to(REPO_ROOT)),
        "output_log": str(output_path.relative_to(REPO_ROOT)),
        "verifier_audit": verifier_audit,
        "postcheck": postcheck,
        "gate_before": gate_before,
        "gate_after": gate_after,
    }
    state_path = target_dir / "local_repair_last.json"
    state_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return report


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--todo-id", required=True)
    p.add_argument("--timeout", type=int, default=int(os.environ.get("OUTREACH_LOCAL_REPAIR_TIMEOUT", "1800") or "1800"))
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    result = run_local_repair(args.todo_id, timeout=args.timeout)
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(f"{args.todo_id}: ok={result.get('ok')} rc={result.get('returncode')} gate_after={result.get('gate_after', {}).get('status')}")
    return 0 if result.get("ok") else int(result.get("returncode") or 1)


if __name__ == "__main__":
    raise SystemExit(main())
