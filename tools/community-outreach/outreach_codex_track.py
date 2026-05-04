#!/usr/bin/env python3
"""Codex-first outreach drafting loop.

For one arXiv/open-problem/GitHub/forum/X target, Codex drafts a public
message, self-audits it, and either closes with a saved draft, escalates to the
operator/oracle-deep path, or exhausts the configured budget.

This module intentionally does not send email, post comments, or call the
oracle.  It only writes transcripts and, on a clean close, one draft file.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
DEFAULT_DRAFTS_DIR = SCRIPT_DIR / "drafts"
LOG_DIR = SCRIPT_DIR / "outreach_state" / "codex_track_logs"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_pi_agent import claude_exec  # noqa: E402

CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
DEFAULT_CODEX_TIMEOUT = 600
DEFAULT_REDLINE_TIMEOUT = 600


@dataclass
class OutreachCodexTrackResult:
    verdict: str
    rounds: int
    elapsed_seconds: float
    audit_score: int
    redline_pass: bool
    draft_path: Optional[Path]
    transcript_path: Path
    next_action: str
    obstruction_reason: str = ""


@dataclass(frozen=True)
class CodexExecResult:
    ok: bool
    parsed: dict
    raw_output: str
    rc: int
    error: str = ""


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _slugify(value: str, *, fallback: str = "target") -> str:
    value = (value or "").strip()
    value = re.sub(r"^https?://", "", value)
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._-")
    return value[:120] or fallback


def _render_template(name: str, values: dict[str, str]) -> str:
    path = PROMPTS_DIR / name
    template = path.read_text(encoding="utf-8")
    for key, value in values.items():
        template = template.replace("{" + key + "}", value)
    return template


def _extract_json_object(text: str) -> Optional[dict]:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    for start in range(len(text)):
        if text[start] != "{":
            continue
        depth = 0
        in_str = False
        esc = False
        for idx in range(start, len(text)):
            ch = text[idx]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    try:
                        return json.loads(text[start : idx + 1])
                    except json.JSONDecodeError:
                        break
    return None


def _strip_jsonl_to_text(stdout: str) -> str:
    parts: list[str] = []
    for line in (stdout or "").splitlines():
        line = line.strip()
        if not line.startswith("{"):
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


def codex_exec(prompt: str, *, timeout: int, log_tag: str) -> CodexExecResult:
    """Run `codex exec --dangerously-bypass-approvals-and-sandbox` safely."""
    codex_bin = CODEX_PATH
    if not codex_bin or not Path(codex_bin).exists():
        return CodexExecResult(False, {}, "", -1, error=f"codex CLI not found at {codex_bin}")
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    prompt_log = LOG_DIR / f"{log_tag}_{ts}.prompt.txt"
    stdout_log = LOG_DIR / f"{log_tag}_{ts}.stdout.jsonl"
    stderr_log = LOG_DIR / f"{log_tag}_{ts}.stderr.txt"
    prompt_log.write_text(prompt, encoding="utf-8")
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, suffix=".txt") as out:
        output_path = Path(out.name)
    cmd = [
        codex_bin,
        "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "--json",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(output_path),
        "-",
    ]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    try:
        proc = subprocess.run(
            cmd,
            input=prompt,
            capture_output=True,
            text=True,
            cwd=str(REPO_ROOT),
            env=env,
            timeout=timeout + 30,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        stdout, stderr, rc = proc.stdout or "", proc.stderr or "", proc.returncode
    except subprocess.TimeoutExpired:
        stdout, stderr, rc = "", f"codex exec timed out after {timeout}s", -9
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
        raw = _strip_jsonl_to_text(stdout) or stdout
    parsed = _extract_json_object(raw) or {}
    if rc != 0:
        return CodexExecResult(False, parsed, raw, rc, error=f"codex exec rc={rc}")
    return CodexExecResult(True, parsed, raw, rc)


def _infer_channel(source_type: str) -> str:
    normalized = (source_type or "").strip().lower()
    if normalized == "arxiv_paper":
        return "email"
    if normalized in {"gh_issue", "github_issue", "github_pr", "gh_pr"}:
        return "gh_issue"
    if normalized in {"forum", "forum_post", "mathoverflow", "zulip"}:
        return "forum"
    if normalized in {"x_post", "x", "twitter"}:
        return "x_post"
    return "email"


def _channel_constraints(channel: str) -> str:
    common = "\n".join(
        [
            "- Do not send or post anything; produce draft text only.",
            "- Use neutral professional academic English.",
            "- Do not mention internal tools, queues, state files, target ids, or pipeline stages.",
            "- Be precise about what is known, what is conjectural, and what you are asking for.",
        ]
    )
    by_channel = {
        "email": "Format as an email with a concise subject line and body; keep the ask concrete and respectful.",
        "gh_issue": "Format as a GitHub issue/PR comment; include only public, reproducible context.",
        "forum": "Format as a forum post/reply; make the mathematical connection understandable.",
        "x_post": "Format as one short X reply/post; avoid hype, pile-ons, and compressed overclaims.",
    }
    return common + "\n- " + by_channel.get(channel, by_channel["email"])


def _target_block(target: dict, channel: str) -> str:
    fields = target.get("fields") or {}
    if not isinstance(fields, dict):
        fields = {"value": fields}
    return (
        f"Target id: {target.get('target_id', '')}\n"
        f"Title: {target.get('title', '')}\n"
        f"Source type: {target.get('source_type', '')}\n"
        f"Inferred channel: {channel}\n"
        f"Source URL: {target.get('source_url', '')}\n\n"
        f"Summary:\n{target.get('summary', '') or '(none supplied)'}\n\n"
        f"Fields:\n{json.dumps(fields, ensure_ascii=False, indent=2)}"
    )


def _history_summary(rounds: list[dict]) -> str:
    if not rounds:
        return "(none; this is the first drafting round)"
    rows: list[str] = []
    for row in rounds[-6:]:
        audit_outer = row.get("audit") or {}
        audit = audit_outer.get("parsed") or audit_outer
        redline = row.get("redline") or {}
        rows.append(json.dumps({
            "round": row.get("round"),
            "verdict": audit.get("verdict"),
            "audit_score": audit.get("audit_score"),
            "findings": audit.get("audit_findings") or audit.get("findings") or [],
            "redline_pass": redline.get("pass"),
            "redline_issues": redline.get("issues") or redline.get("fix_reasons"),
            "next_direction": audit.get("next_direction") or audit.get("next_step"),
        }, ensure_ascii=False))
    return "\n".join(rows)


def _coerce_score(value: object, default: int = 0) -> int:
    try:
        score = int(value)
    except (TypeError, ValueError):
        return default
    return max(0, min(10, score))


def _audit_verdict(audit: dict) -> str:
    verdict = str(audit.get("verdict", "")).strip().lower()
    if verdict in {"close", "continue", "escalate"}:
        return verdict
    return "continue"


def _draft_from_round(raw: str, parsed: dict) -> str:
    for key in ("draft_text", "draft", "message", "content"):
        value = parsed.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return (raw or "").strip()


def _redline_pass(parsed: dict) -> bool:
    value = parsed.get("pass")
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.strip().lower() in {"true", "pass", "passed", "yes"}:
        return True
    verdict = str(parsed.get("verdict", "")).strip().lower()
    return verdict in {"pass", "passed", "approve", "approved"}


def _redline_check(*, draft_text: str, channel: str, target_block: str, target_id: str) -> tuple[bool, dict, str]:
    prompt = _render_template("claude_redline_outreach.txt", {
        "draft_text": draft_text,
        "channel": channel,
        "target_block": target_block,
    })
    ok, stdout, rc = claude_exec(prompt, timeout=DEFAULT_REDLINE_TIMEOUT, log_tag=f"codex_track_redline_{_slugify(target_id)}")
    parsed = _extract_json_object(stdout) or {}
    if not ok:
        return False, {"pass": False, "issues": [f"claude rc={rc}"], "raw_excerpt": stdout[:1200]}, stdout
    if not parsed:
        return False, {"pass": False, "issues": ["Claude returned no parseable JSON"], "raw_excerpt": stdout[:1200]}, stdout
    return _redline_pass(parsed), parsed, stdout


def _write_transcript(path: Path, transcript: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(transcript, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _result_payload(result: OutreachCodexTrackResult) -> dict:
    data = asdict(result)
    data["draft_path"] = str(result.draft_path) if result.draft_path else None
    data["transcript_path"] = str(result.transcript_path)
    return data


def run_codex_track(
    target: dict,
    *,
    max_rounds: int = 8,
    wall_clock_s: int = 1800,
    drafts_dir: Optional[Path] = None,
) -> OutreachCodexTrackResult:
    target = dict(target or {})
    target_id = str(target.get("target_id") or target.get("id") or target.get("source_url") or "target")
    target["target_id"] = target_id
    channel = _infer_channel(str(target.get("source_type", "")))
    target_slug = _slugify(target_id)
    channel_slug = _slugify(channel, fallback="channel")
    transcript_path = LOG_DIR / f"{target_slug}_{_now_tag()}.transcript.json"
    start = time.monotonic()
    target_context = _target_block(target, channel)
    rounds: list[dict] = []
    final_score = 0
    final_redline_pass = False

    transcript: dict = {"schema": "outreach-codex-track-transcript-v1", "started_at": _now_iso(), "target": target, "channel": channel, "rounds": rounds}

    def finish(
        verdict: str,
        *,
        next_action: str,
        audit_score: int | None = None,
        redline_pass: bool | None = None,
        draft_path: Optional[Path] = None,
        obstruction_reason: str = "",
    ) -> OutreachCodexTrackResult:
        elapsed = time.monotonic() - start
        result = OutreachCodexTrackResult(
            verdict, len(rounds), elapsed,
            final_score if audit_score is None else audit_score,
            final_redline_pass if redline_pass is None else redline_pass,
            draft_path, transcript_path, next_action, obstruction_reason,
        )
        transcript["finished_at"] = _now_iso()
        transcript["elapsed_seconds"] = elapsed
        transcript["result"] = _result_payload(result)
        _write_transcript(transcript_path, transcript)
        return result

    for round_idx in range(1, max_rounds + 1):
        remaining = wall_clock_s - (time.monotonic() - start)
        if remaining <= 45:
            return finish("exhausted", next_action="human_review", obstruction_reason=f"wall-clock {wall_clock_s}s exhausted before round {round_idx}")

        round_prompt = _render_template("codex_track_round.txt", {
            "target_block": target_context,
            "prior_rounds_summary": _history_summary(rounds),
            "channel_constraints": _channel_constraints(channel),
        })
        codex_timeout = min(DEFAULT_CODEX_TIMEOUT, max(60, int(remaining) - 20))
        author_t0 = time.monotonic()
        author = codex_exec(
            round_prompt,
            timeout=codex_timeout,
            log_tag=f"codex_track_{target_slug}_r{round_idx}_author",
        )
        author_seconds = time.monotonic() - author_t0
        candidate_draft = _draft_from_round(author.raw_output, author.parsed)
        round_record: dict = {
            "round": round_idx,
            "started_at": _now_iso(),
            "author": {
                "ok": author.ok,
                "rc": author.rc,
                "parsed": author.parsed,
                "raw_output": author.raw_output,
                "error": author.error,
                "seconds": author_seconds,
            },
        }
        rounds.append(round_record)

        if not author.ok or not candidate_draft:
            round_record["outcome"] = "author_infra_fail"
            _write_transcript(transcript_path, transcript)
            continue

        audit_prompt = _render_template("codex_track_audit.txt", {"draft_text": candidate_draft, "channel": channel})
        remaining = wall_clock_s - (time.monotonic() - start)
        if remaining <= 45:
            return finish("exhausted", next_action="human_review", obstruction_reason="wall-clock exhausted before audit")
        audit_t0 = time.monotonic()
        audit_res = codex_exec(
            audit_prompt,
            timeout=min(DEFAULT_CODEX_TIMEOUT, max(60, int(remaining) - 20)),
            log_tag=f"codex_track_{target_slug}_r{round_idx}_audit",
        )
        audit_seconds = time.monotonic() - audit_t0
        audit = audit_res.parsed if audit_res.parsed else {}
        verdict = _audit_verdict(audit)
        audit_score = _coerce_score(audit.get("audit_score"), 0)
        final_score = audit_score
        draft_text = str(audit.get("draft_text") or candidate_draft).strip()
        round_record["audit"] = {
            "ok": audit_res.ok,
            "rc": audit_res.rc,
            "parsed": audit,
            "raw_output": audit_res.raw_output,
            "error": audit_res.error,
            "seconds": audit_seconds,
        }

        if not audit_res.ok or not audit:
            round_record["outcome"] = "audit_infra_fail"
            _write_transcript(transcript_path, transcript)
            continue

        if verdict == "escalate":
            reason = str(
                audit.get("obstruction_reason")
                or audit.get("escalation_reason")
                or audit.get("audit_findings")
                or "Codex self-audit requested escalation"
            )
            round_record["outcome"] = "escalate"
            return finish(
                "escalate",
                next_action="oracle_deep",
                audit_score=audit_score,
                obstruction_reason=reason[:2000],
            )

        if verdict == "continue" or audit_score < 7:
            round_record["outcome"] = "continue"
            if verdict == "close" and audit_score < 7:
                round_record["outcome"] = "low_audit_continue"
            _write_transcript(transcript_path, transcript)
            continue

        redline_ok, redline_parsed, redline_raw = _redline_check(
            draft_text=draft_text,
            channel=channel,
            target_block=target_context,
            target_id=target_id,
        )
        final_redline_pass = redline_ok
        round_record["redline"] = {
            "pass": redline_ok,
            "parsed": redline_parsed,
            "raw_output": redline_raw,
        }
        if not redline_ok:
            round_record["outcome"] = "redline_continue"
            _write_transcript(transcript_path, transcript)
            continue

        out_dir = drafts_dir or DEFAULT_DRAFTS_DIR
        out_dir.mkdir(parents=True, exist_ok=True)
        draft_path = out_dir / f"{target_slug}_{channel_slug}.md"
        draft_path.write_text(draft_text.rstrip() + "\n", encoding="utf-8")
        round_record["outcome"] = "close"
        round_record["draft_path"] = str(draft_path)
        return finish(
            "close",
            next_action="send",
            audit_score=audit_score,
            redline_pass=True,
            draft_path=draft_path,
        )

    return finish(
        "exhausted",
        next_action="human_review",
        obstruction_reason=f"codex track exhausted {max_rounds} rounds without close",
    )


def _load_target_from_args(args: argparse.Namespace) -> dict:
    if args.target_json:
        target = json.loads(args.target_json)
    elif args.target_file:
        target = json.loads(Path(args.target_file).read_text(encoding="utf-8"))
    else:
        raise SystemExit("provide --target-json or --target-file")
    if not isinstance(target, dict):
        raise SystemExit("target payload must be a JSON object")
    if args.target_id:
        target["target_id"] = args.target_id
    if not target.get("target_id"):
        raise SystemExit("target_id is required in payload or via --target-id")
    return target


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="run Codex-first outreach drafting track")
    parser.add_argument("--target-id", help="target id used for transcript/draft filenames")
    parser.add_argument("--target-json", help="target JSON object")
    parser.add_argument("--target-file", type=Path, help="path to target JSON object")
    parser.add_argument("--max-rounds", type=int, default=8)
    parser.add_argument("--wall-clock-s", type=int, default=1800)
    parser.add_argument("--drafts-dir", type=Path)
    args = parser.parse_args(argv)

    target = _load_target_from_args(args)
    result = run_codex_track(
        target,
        max_rounds=args.max_rounds,
        wall_clock_s=args.wall_clock_s,
        drafts_dir=args.drafts_dir,
    )
    print(json.dumps(_result_payload(result), ensure_ascii=False, indent=2))
    return 0 if result.verdict in {"close", "escalate"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
