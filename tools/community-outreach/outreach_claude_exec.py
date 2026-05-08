#!/usr/bin/env python3
"""outreach_claude_exec — zero-dependency `claude -p` subprocess wrapper.

Extracted from outreach_pi_agent.py to break the cross-import chain that
made outreach_codex_track fail to start whenever outreach_pi_agent.py had
any import-time bug. This module imports only stdlib.

Public API:
    CLAUDE_PATH                 : auto-resolved claude CLI path
    DEFAULT_TIMEOUT_S           : 1200 (20 min)
    DEFAULT_LOG_DIR             : tools/community-outreach/outreach_state/supervisor_logs
    claude_exec(prompt, *, timeout, log_tag, log_dir, repo_root)
        -> tuple[ok, stdout, rc]

Behaviour matches the prior outreach_pi_agent.claude_exec byte-for-byte —
prompt + stdout + stderr are written under the log_dir as
`<log_tag>_<timestamp>.{prompt,stdout,stderr}.txt`.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from datetime import datetime
from pathlib import Path

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO_ROOT = SCRIPT_DIR.parents[1]
DEFAULT_LOG_DIR = SCRIPT_DIR / "outreach_state" / "supervisor_logs"
DEFAULT_TIMEOUT_S = 1200


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def claude_exec(
    prompt: str,
    *,
    timeout: int = DEFAULT_TIMEOUT_S,
    log_tag: str = "claude_exec",
    log_dir: Path | None = None,
    repo_root: Path | None = None,
) -> tuple[bool, str, int]:
    """Run `claude -p --dangerously-skip-permissions <<<prompt>>>` once.

    Returns (ok, stdout, rc). On timeout returns (False, partial_stdout, -9).
    Logs prompt + stdout + stderr to log_dir for postmortem.
    """
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)

    log_dir = Path(log_dir) if log_dir is not None else DEFAULT_LOG_DIR
    repo_root = Path(repo_root) if repo_root is not None else DEFAULT_REPO_ROOT
    log_dir.mkdir(parents=True, exist_ok=True)

    ts = _now_tag()
    (log_dir / f"{log_tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")

    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=str(repo_root),
        env=env,
        encoding="utf-8",
        errors="replace",
        start_new_session=True,
    )
    stdout, stderr, rc = "", "", -1
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""
            stderr = stderr or ""
        rc = -9
    (log_dir / f"{log_tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (log_dir / f"{log_tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)
