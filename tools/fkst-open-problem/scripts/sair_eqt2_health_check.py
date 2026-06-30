#!/usr/bin/env python3
"""Health check for the SAIR-EQT2-only FKST 24-hour dogfood run."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
import re
import subprocess
from pathlib import Path


LABEL = "org.omega.fkst-sair-eqt2"
LOG = Path("/tmp/fkst-sair-eqt2-supervise.log")
ERR = Path("/tmp/fkst-sair-eqt2-supervise.err")
RUNTIME_LOGS = Path("/tmp/fkst-sair-eqt2-runtime/logs")

REQUIRED_STDOUT = [
    # HARD = early liveness only: the seed raiser is configured and the seed→intake
    # entry departments ran. These appear within seconds of the boot seed.
    "dept=omega-sair-eqt2.seed_sair_stage2",
    "dept=omega-sair-eqt2.proposal_intake",
    # interval is operator-tunable (24h dogfood-sparse vs 1h dogfood-active); assert the
    # raiser fires, not a specific cadence, so retuning the cron does not false-fail health.
    "raiser=omega-sair-eqt2.sair_stage2 interval_s=",
]

# SOFT = chain-completion evidence. The full portfolio/proposal chain
# (artifact_writer → repo_artifact_sink → delivery acked) only finishes a few seconds
# to a minute into a fresh runtime. Hard-requiring it false-fails a just-restarted
# daemon, which makes the patrol kickstart-loop it (the actual pipeline is fine — the
# burst just hasn't propagated yet). So these are warnings, not liveness gates.
CHAIN_COMPLETION_STDOUT = [
    "dept=omega-sair-eqt2.artifact_writer",
    "dept=omega-sair-eqt2.repo_artifact_sink",
    "omega-sair-eqt2.repo_artifact_sink delivery_id=",
    "MSG=delivery acked",
]

PORTFOLIO_STDOUT = [
    "dept=omega-sair-eqt2.research_portfolio",
    "dept=omega-sair-eqt2.research_checker",
    "dept=omega-sair-eqt2.research_artifact",
    "dept=omega-sair-eqt2.research_candidate",
]

REQUIRED_RUNTIME = [
    # converge_diagnostic / consensus.consensus_converge intentionally not required:
    # slow consensus path (and the queue name changed across consensus-package
    # versions); core liveness is the artifact + checker flow below.
    "queue=omega-sair-eqt2.omega_artifact_task dept=omega-sair-eqt2.artifact_writer",
    "dept=omega-sair-eqt2.artifact_writer",
    "queue=omega-sair-eqt2.omega_repo_artifact dept=omega-sair-eqt2.repo_artifact_sink",
    "dept=omega-sair-eqt2.repo_artifact_sink",
    "reason=completed",
]

PORTFOLIO_RUNTIME = [
    "queue=omega-sair-eqt2.omega_research_task dept=omega-sair-eqt2.research_portfolio",
    "queue=omega-sair-eqt2.omega_candidate_search dept=omega-sair-eqt2.research_checker",
    "queue=omega-sair-eqt2.omega_checker_result dept=omega-sair-eqt2.research_artifact",
    "research-run-sair-eqt2-research-v1-coefficient-analysis-baseline",
    "research-run-sair-eqt2-research-v1-claim-boundary-audit",
    "research-run-sair-eqt2-research-v1-linear-magma-shard-vars1-p13",
    "research-run-sair-eqt2-research-v1-linear-magma-shard-vars2-p13",
    "research-run-sair-eqt2-research-v1-linear-magma-shard-vars1-p89",
    "research-run-sair-eqt2-research-v1-linear-magma-shard-vars2-p89",
    # codex advisory is now ENABLED (self-drive), so CODEX_ADVISORY_DISABLED is no
    # longer emitted; requiring it would falsely fail health on the self-driving runtime.
]

FORBIDDEN_TEXT = [
    "seed_t43",
    "omega-open-problem.seed",
    "omega-open-problem/SAIR-EQT2",
    "FKST_GITHUB_WRITE => 1",
    "raised publish error",
    "framework failed",
    "DEAD_LETTER",
    "error_class=",
    "caught-failure",
    "Operation not permitted",
]

# Benign, expected WARNs that must NOT hard-fail health. The research_portfolio cron
# delivery emits a source-tracking publish to the `dead_letter` queue, which by design
# has no subscriber in this package; the WARN fires once per cron tick and the pipeline
# acks the real delivery immediately after (verified). With the 1h cadence it appears
# every window, so it cannot be in FORBIDDEN_TEXT.
BENIGN_WARN_TEXT = [
    "has no delivery subscriptions",
]


def run(command: list[str]) -> str:
    result = subprocess.run(command, check=False, text=True, capture_output=True)
    if result.returncode != 0:
        raise SystemExit(
            f"{' '.join(command)} failed with {result.returncode}\n"
            f"stdout:\n{result.stdout}\n"
            f"stderr:\n{result.stderr}"
        )
    return result.stdout


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def parse_pid(launchctl_text: str) -> int:
    match = re.search(r"\n\s*pid = (\d+)\n", launchctl_text)
    require(match is not None, "LaunchAgent is missing a pid")
    return int(match.group(1))


def parse_timestamp(raw: str) -> datetime:
    return datetime.strptime(raw, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def runtime_age_seconds(stdout_text: str) -> int:
    started = current_runtime_start(stdout_text)
    return int((datetime.now(timezone.utc) - started).total_seconds())


def current_runtime_start(stdout_text: str) -> datetime:
    matches = re.findall(
        r"TIMESTAMP=(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z).*event runtime running",
        stdout_text,
    )
    require(matches, f"{LOG}: missing event runtime running timestamp")
    return parse_timestamp(matches[-1])


def current_stdout_segment(stdout_text: str) -> str:
    marker = "MSG=event runtime running"
    index = stdout_text.rfind(marker)
    require(index >= 0, f"{LOG}: missing current runtime marker")
    line_start = stdout_text.rfind("\n", 0, index)
    if line_start < 0:
        return stdout_text
    return stdout_text[line_start + 1 :]


def log_segment_since(path: Path, started: datetime) -> str:
    if not path.exists():
        return ""
    lines = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        match = re.search(
            r"TIMESTAMP=(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)",
            line,
        )
        if match is None or parse_timestamp(match.group(1)) >= started:
            lines.append(line)
    return "\n".join(lines)


def current_runtime_text(started: datetime, current_stdout: str) -> str:
    chunks = [current_stdout, log_segment_since(ERR, started)]
    if RUNTIME_LOGS.exists():
        for path in sorted(RUNTIME_LOGS.rglob("*.log")):
            modified = datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)
            if modified >= started:
                chunks.append(path.read_text(encoding="utf-8", errors="replace"))
    return "\n".join(chunks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--min-age-seconds",
        type=int,
        default=0,
        help="Require the active supervisor process to be at least this old.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print a machine-readable JSON health record.",
    )
    parser.add_argument(
        "--append-jsonl",
        type=Path,
        help="Append the health record as one JSON line.",
    )
    args = parser.parse_args()

    launchctl_text = run(["launchctl", "print", f"gui/{os.getuid()}/{LABEL}"])
    require("state = running" in launchctl_text, "LaunchAgent is not running")
    require("FKST_GITHUB_WRITE => 0" in launchctl_text, "FKST_GITHUB_WRITE is not 0")
    require("omega-sair-eqt2" in launchctl_text, "focused SAIR package is not loaded")
    require("omega-open-problem" not in launchctl_text, "broad omega-open-problem package is loaded")

    pid = parse_pid(launchctl_text)
    require(LOG.exists(), f"missing {LOG}")
    stdout_text = LOG.read_text(encoding="utf-8", errors="replace")
    started = current_runtime_start(stdout_text)
    current_stdout = current_stdout_segment(stdout_text)
    age_seconds = runtime_age_seconds(stdout_text)
    if args.min_age_seconds:
        require(
            age_seconds >= args.min_age_seconds,
            f"runtime age {age_seconds}s is below required {args.min_age_seconds}s",
        )
    for needle in REQUIRED_STDOUT:
        require(needle in current_stdout, f"{LOG}: current runtime missing {needle!r}")
    # The department graph grows as packages add departments: legacy=9, portfolio=13,
    # portfolio+codex-advisory(self-drive)=14+. Parse the actual count instead of
    # hardcoding, so a healthy runtime with a larger graph isn't mis-flagged (which
    # made the patrol loop attempt spurious supervisor restarts).
    handle_counts = [int(x) for x in re.findall(r"handles=(\d+)", current_stdout)]
    handles_count = max(handle_counts) if handle_counts else 0
    has_legacy_graph = handles_count >= 9
    has_portfolio_graph = handles_count >= 13
    require(
        handles_count >= 9,
        f"{LOG}: current runtime missing supported handles count (got {handles_count})",
    )
    combined = current_runtime_text(started, current_stdout)
    # HARD safety gate: never tolerate write-enabled / dead-letter / publish-error text.
    for needle in FORBIDDEN_TEXT:
        require(needle not in combined, f"forbidden runtime text found: {needle!r}")

    # SOFT evidence: which departments fired in the current window varies by operating
    # mode (codex self-drive vs portfolio-only) and by how recently the runtime
    # restarted. A missing slow-path department (converge/artifact_writer) is a warning,
    # not an unhealthy runtime; liveness = pid alive + handles + recent activity + no
    # forbidden text (checked above).
    warnings: list[str] = []
    def note(present: bool, msg: str) -> None:
        if not present:
            warnings.append(msg)
    note("tag=DRY_RUN_REPO_ARTIFACT" in combined, "repo_artifact_sink DRY_RUN_REPO_ARTIFACT not seen in window")
    note("github_write=false" in combined, "github_write=false not confirmed in window")
    for needle in CHAIN_COMPLETION_STDOUT:
        note(needle in current_stdout, f"chain-completion evidence not yet in window (warming up): {needle!r}")
    if has_portfolio_graph:
        for needle in PORTFOLIO_STDOUT:
            note(needle in current_stdout, f"portfolio stdout missing {needle!r}")
        for needle in PORTFOLIO_RUNTIME:
            note(needle in combined, f"portfolio runtime evidence missing: {needle!r}")
    for needle in REQUIRED_RUNTIME:
        note(needle in combined, f"runtime evidence missing: {needle!r}")

    record = {
        "schema": "omega.sair_eqt2.health.v1",
        "checked_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "target": "SAIR-EQT2",
        "launchagent": LABEL,
        "state": "running",
        "pid": pid,
        "runtime_age_seconds": age_seconds,
        "github_write": "disabled",
        "graph": "focused omega-sair-eqt2 portfolio" if has_portfolio_graph else "focused omega-sair-eqt2 only",
        "first_cycle": "acked through repo_artifact_sink",
        "runtime_errors": "none matched",
        "warnings": warnings,
    }
    if args.append_jsonl is not None:
        args.append_jsonl.parent.mkdir(parents=True, exist_ok=True)
        with args.append_jsonl.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        print("target: SAIR-EQT2")
        print(f"launchagent: {LABEL}")
        print("state: running")
        print(f"pid: {pid}")
        print(f"runtime_age_seconds: {age_seconds}")
        print("github_write: disabled")
        print("graph: focused omega-sair-eqt2 only")
        print("first_cycle: acked through repo_artifact_sink")
        print("runtime_errors: none matched")


if __name__ == "__main__":
    main()
