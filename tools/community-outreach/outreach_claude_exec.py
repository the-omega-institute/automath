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

Claude is intentionally disabled for normal drafting/gating/refill stages.
Allowed paths:
  - PI supervision (`log_tag` beginning with `pi_`)
  - explicit writeback (`outreach_writeback_loop.py` invokes `/killo-golden`
    directly and does not use this wrapper)
Set `OUTREACH_ALLOW_CLAUDE=1` only for a deliberate one-off diagnostic.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from datetime import datetime
from pathlib import Path

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO_ROOT = SCRIPT_DIR.parents[1]
DEFAULT_LOG_DIR = SCRIPT_DIR / "outreach_state" / "supervisor_logs"
DEFAULT_TIMEOUT_S = 1200
LAST_EXEC_INFO: dict[str, object] = {
    "backend": "none",
    "fallback_used": False,
    "fallback_reason": "",
    "rc": None,
}


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _looks_like_quota_or_limit(text: str) -> bool:
    lower = (text or "").lower()
    needles = (
        "hit your limit",
        "usage limit",
        "rate limit",
        "quota",
        "too many requests",
        "try again later",
        "resets ",
    )
    return any(x in lower for x in needles)


def _strip_codex_jsonl_to_text(stdout: str) -> str:
    parts: list[str] = []
    for line in (stdout or "").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        msg = obj.get("message") or obj.get("content") or ""
        if isinstance(msg, str):
            parts.append(msg)
        elif isinstance(msg, list):
            for item in msg:
                if isinstance(item, dict):
                    text = item.get("text") or item.get("content")
                    if text:
                        parts.append(str(text))
    return "\n".join(parts).strip()


def _codex_fallback_exec(
    prompt: str,
    *,
    timeout: int,
    log_tag: str,
    log_dir: Path,
    repo_root: Path,
    reason: str,
) -> tuple[bool, str, int]:
    if os.environ.get("OUTREACH_CLAUDE_FALLBACK_CODEX", "1") == "0":
        return False, f"Claude failed and Codex fallback disabled: {reason}", -20
    if not CODEX_PATH or not Path(CODEX_PATH).exists():
        return False, f"Claude failed ({reason}); codex CLI not found at {CODEX_PATH}", -21
    ts = _now_tag()
    fallback_prompt = (
        "You are Codex acting as the fallback backend for a Claude-only "
        "outreach pipeline step. Claude is currently unavailable, so you must "
        "produce the exact requested output contract from the original prompt. "
        "If the original prompt asks for JSON, output only that JSON object. "
        "Do not mention that you are a fallback unless the prompt explicitly "
        "asks for backend diagnostics.\n\n"
        f"Fallback reason: {reason}\n\n"
        "=== ORIGINAL PROMPT ===\n"
        f"{prompt}"
    )
    prompt_log = log_dir / f"{log_tag}_{ts}.codex_fallback_prompt.txt"
    stdout_log = log_dir / f"{log_tag}_{ts}.codex_fallback_stdout.jsonl"
    stderr_log = log_dir / f"{log_tag}_{ts}.codex_fallback_stderr.txt"
    raw_log = log_dir / f"{log_tag}_{ts}.codex_fallback_raw.txt"
    prompt_log.write_text(fallback_prompt, encoding="utf-8")
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, suffix=".txt") as out:
        output_path = Path(out.name)
    cmd = [
        CODEX_PATH,
        "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "--json",
        "-C",
        str(repo_root),
        "-o",
        str(output_path),
        "-",
    ]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    try:
        proc = subprocess.run(
            cmd,
            input=fallback_prompt,
            capture_output=True,
            text=True,
            cwd=str(repo_root),
            env=env,
            timeout=timeout + 30,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        stdout, stderr, rc = proc.stdout or "", proc.stderr or "", proc.returncode
    except subprocess.TimeoutExpired:
        stdout, stderr, rc = "", f"codex fallback timed out after {timeout}s", -9
    stdout_log.write_text(stdout or "", encoding="utf-8")
    stderr_log.write_text(stderr or "", encoding="utf-8")
    raw = ""
    try:
        if output_path.exists():
            raw = output_path.read_text(encoding="utf-8", errors="replace")
    finally:
        try:
            output_path.unlink()
        except OSError:
            pass
    if not raw:
        raw = _strip_codex_jsonl_to_text(stdout) or stdout
    raw_log.write_text(raw or "", encoding="utf-8")
    LAST_EXEC_INFO.update({
        "backend": "codex",
        "fallback_used": True,
        "fallback_reason": reason,
        "rc": rc,
    })
    if rc != 0:
        err = stderr.strip() or raw.strip() or stdout.strip()
        return False, f"codex fallback rc={rc}: {err[:1200]}", rc
    return True, raw, rc


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
    allowed_pi = log_tag.startswith("pi_")
    log_dir = Path(log_dir) if log_dir is not None else DEFAULT_LOG_DIR
    repo_root = Path(repo_root) if repo_root is not None else DEFAULT_REPO_ROOT
    log_dir.mkdir(parents=True, exist_ok=True)
    LAST_EXEC_INFO.update({
        "backend": "claude",
        "fallback_used": False,
        "fallback_reason": "",
        "rc": None,
    })

    if not allowed_pi and os.environ.get("OUTREACH_ALLOW_CLAUDE") != "1":
        return _codex_fallback_exec(
            prompt,
            timeout=timeout,
            log_tag=log_tag,
            log_dir=log_dir,
            repo_root=repo_root,
            reason="claude disabled by outreach policy outside PI/writeback",
        )

    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        reason = f"claude CLI not found at {CLAUDE_PATH}"
        return _codex_fallback_exec(
            prompt, timeout=timeout, log_tag=log_tag, log_dir=log_dir,
            repo_root=repo_root, reason=reason,
        )

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
    LAST_EXEC_INFO.update({
        "backend": "claude",
        "fallback_used": False,
        "fallback_reason": "",
        "rc": rc,
    })
    failure_text = "\n".join([stdout or "", stderr or ""]).strip()
    if rc != 0 or rc == -9 or _looks_like_quota_or_limit(failure_text):
        reason = (
            "claude timed out"
            if rc == -9
            else (
                "claude quota/limit"
                if _looks_like_quota_or_limit(failure_text)
                else f"claude rc={rc}"
            )
        )
        ok, fallback_stdout, fallback_rc = _codex_fallback_exec(
            prompt,
            timeout=timeout,
            log_tag=log_tag,
            log_dir=log_dir,
            repo_root=repo_root,
            reason=reason,
        )
        if ok:
            return True, fallback_stdout, fallback_rc
    return (rc == 0, stdout, rc)


def codex_fallback_exec(
    prompt: str,
    *,
    timeout: int = DEFAULT_TIMEOUT_S,
    log_tag: str = "codex_fallback",
    log_dir: Path | None = None,
    repo_root: Path | None = None,
    reason: str = "explicit fallback",
) -> tuple[bool, str, int]:
    log_dir = Path(log_dir) if log_dir is not None else DEFAULT_LOG_DIR
    repo_root = Path(repo_root) if repo_root is not None else DEFAULT_REPO_ROOT
    log_dir.mkdir(parents=True, exist_ok=True)
    return _codex_fallback_exec(
        prompt,
        timeout=timeout,
        log_tag=log_tag,
        log_dir=log_dir,
        repo_root=repo_root,
        reason=reason,
    )
