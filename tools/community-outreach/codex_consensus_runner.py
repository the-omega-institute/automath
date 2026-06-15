#!/usr/bin/env python3
"""Run independent Codex workers and check numerical consensus.

This script consumes the latest direction-only Oracle response for one target,
selects one attack direction, asks three independent Codex workers to implement
the finite computation, and records a 2-of-3 consensus artifact.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
TARGETS_DIR = SCRIPT_DIR / "targets"
ORACLE_LOG_DIR = SCRIPT_DIR / "logs" / "oracle"
BEGIN_BLOCK = "<!-- BEGIN CODEX_CONSENSUS_PRIOR_ROUND -->"
END_BLOCK = "<!-- END CODEX_CONSENSUS_PRIOR_ROUND -->"


@dataclass
class Direction:
    theorem: str
    finite_python_computation: str
    kill_criterion: str
    predicted_result: str


@dataclass
class WorkerRecord:
    worker_id: int
    status: str
    result_path: str
    stdout_tail: str = ""
    stderr_tail: str = ""
    result: Any = None
    script_path: str | None = None
    notes: str = ""
    runtime_sec: float | None = None
    error: str | None = None


def log(msg: str) -> None:
    print(f"[consensus] {msg}", flush=True)


def timestamp_tag() -> str:
    return time.strftime("%Y%m%d_%H%M%S")


def compact_slug(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", text.lower())


def locate_latest_oracle_response(slug: str) -> Path:
    if not ORACLE_LOG_DIR.exists():
        raise FileNotFoundError(f"oracle log dir missing: {ORACLE_LOG_DIR}")
    candidates = list(ORACLE_LOG_DIR.glob("deep_*_t*.response.txt"))
    exact: list[Path] = []
    fuzzy: list[Path] = []
    slug_compact = compact_slug(slug)
    for path in candidates:
        stem = path.name
        m = re.match(r"deep_(.+)_t\d+\.response\.txt$", stem)
        if not m:
            continue
        file_slug = m.group(1)
        if file_slug == slug:
            exact.append(path)
            continue
        file_compact = compact_slug(file_slug)
        if (
            file_slug.startswith(slug)
            or slug.startswith(file_slug)
            or file_compact.startswith(slug_compact)
            or slug_compact.startswith(file_compact)
            or _token_overlap_match(slug, file_slug)
        ):
            fuzzy.append(path)
    pool = exact or fuzzy
    if not pool:
        raise FileNotFoundError(f"no deep response found for slug/prefix: {slug}")
    min_bytes = int(os.environ.get("OUTREACH_CONSENSUS_MIN_BYTES", "200") or "200")
    substantive = [p for p in pool if p.stat().st_size >= min_bytes]
    if substantive:
        chosen = max(substantive, key=lambda p: p.stat().st_mtime)
    else:
        chosen = max(pool, key=lambda p: p.stat().st_mtime)
        log(f"WARN: no Oracle response >= {min_bytes}B; falling back to newest ({chosen.stat().st_size}B)")
    mode = "exact" if chosen in exact else "prefix/fuzzy"
    log(f"oracle response selected ({mode}, {chosen.stat().st_size}B): {chosen}")
    return chosen


def _token_overlap_match(slug: str, file_slug: str) -> bool:
    a = {t for t in slug.lower().split("_") if len(t) > 2}
    b = {t for t in file_slug.lower().split("_") if len(t) > 2}
    if not a or not b:
        return False
    overlap = len(a & b)
    return overlap >= max(2, min(len(a), len(b)) - 1)


def clean_markdown_value(value: str) -> str:
    value = value.strip()
    value = re.sub(r"^\s*[-*]\s+", "", value)
    value = re.sub(r"^\s*\d+[.)]\s+", "", value)
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] == "`":
        value = value[1:-1].strip()
    return value


def field_key(line: str) -> tuple[str | None, str]:
    stripped = line.strip()
    stripped = re.sub(r"^\s*(?:[-*]|\d+[.)])\s+", "", stripped)
    stripped = stripped.strip()
    patterns = [
        ("theorem", r"^\*{0,2}(?:specific\s+)?(?:theorem|source|structure)(?:\s*/\s*(?:source|structure(?:\s+to\s+use)?))*\*{0,2}\s*[:\-–—]\s*(.*)$"),
        ("finite_python_computation", r"^\*{0,2}finite\s+(?:codex\s+)?(?:python\s+)?computation\*{0,2}\s*[:\-–—]\s*(.*)$"),
        ("kill_criterion", r"^\*{0,2}kill\s*/\s*confirm\s+criterion\*{0,2}\s*[:\-–—]\s*(.*)$"),
        ("kill_criterion", r"^\*{0,2}kill\s+(?:or\s+)?confirm\s+criterion\*{0,2}\s*[:\-–—]\s*(.*)$"),
        ("kill_criterion", r"^\*{0,2}kill\s+criterion\*{0,2}\s*[:\-–—]\s*(.*)$"),
        ("predicted_result", r"^\*{0,2}predicted\s+result\*{0,2}\s*[:\-–—]\s*(.*)$"),
    ]
    for key, pattern in patterns:
        m = re.match(pattern, stripped, flags=re.IGNORECASE)
        if m:
            return key, clean_markdown_value(m.group(1))
    return None, ""


def split_direction_blocks(text: str) -> list[str]:
    # Pass 1 strict: only match lines that contain the word "Direction" explicitly
    # to avoid matching inner enumerations like "1. **Specific theorem**".
    strict_pattern = re.compile(
        r"(?im)^(?:#{2,4}\s*Direction\s+[123]\b.*|\*\*Direction\s+[123]\*\*.*|Direction\s+[123]\s*[:\-–—].*|[123][.)]\s+\*\*?Direction\b.*)$"
    )
    matches = list(strict_pattern.finditer(text))
    if len(matches) < 3:
        # Pass 2 fallback: accept top-level numbered items that contain field cues
        loose_pattern = re.compile(
            r"(?im)^[123][.)]\s+.*(?:theorem|source|structure).*$"
        )
        matches = list(loose_pattern.finditer(text))
    blocks: list[str] = []
    for i, match in enumerate(matches):
        start = match.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        blocks.append(text[start:end].strip())
    if len(blocks) >= 3:
        return blocks[:3]

    numbered = list(re.finditer(r"(?m)^([123])[.)]\s+", text))
    blocks = []
    for i, match in enumerate(numbered):
        start = match.start()
        end = numbered[i + 1].start() if i + 1 < len(numbered) else len(text)
        candidate = text[start:end].strip()
        if sum(1 for key in ("theorem", "computation", "criterion", "predicted") if key in candidate.lower()) >= 3:
            blocks.append(candidate)
    return blocks[:3]


def parse_direction_block(block: str) -> Direction | None:
    fields: dict[str, list[str]] = {
        "theorem": [],
        "finite_python_computation": [],
        "kill_criterion": [],
        "predicted_result": [],
    }
    current: str | None = None
    for raw_line in block.splitlines():
        key, initial = field_key(raw_line)
        if key:
            current = key
            if initial:
                fields[current].append(initial)
            continue
        if current is not None:
            line = raw_line.rstrip()
            if not line.strip():
                if fields[current] and fields[current][-1] != "":
                    fields[current].append("")
                continue
            if re.match(r"^\s*(?:#{1,4}\s+|\*\*Direction\s+\d+|\d+[.)]\s+\*\*?Direction)", line, re.I):
                continue
            fields[current].append(clean_markdown_value(line))
    packed = {k: "\n".join(v).strip() for k, v in fields.items()}
    if all(packed.values()):
        return Direction(**packed)

    ordered_items = re.split(r"(?m)^\s*(?:[-*]|\d+[.)])\s+", block)
    ordered_items = [item.strip() for item in ordered_items if item.strip()]
    if len(ordered_items) >= 4:
        values: list[str] = []
        for item in ordered_items:
            if re.search(r"\bDirection\s+\d+\b", item, flags=re.I) and len(item) < 120:
                continue
            values.append(clean_markdown_value(item))
            if len(values) == 4:
                break
        if len(values) == 4:
            return Direction(values[0], values[1], values[2], values[3])
    return None


def parse_directions(text: str) -> list[Direction]:
    blocks = split_direction_blocks(text)
    directions: list[Direction] = []
    for block in blocks:
        parsed = parse_direction_block(block)
        if parsed is not None:
            directions.append(parsed)
    return directions


def write_skipped_artifact(slug: str, response_path: Path, text: str, reason: str) -> Path:
    artifacts = TARGETS_DIR / slug / "codex_consensus_artifacts"
    artifacts.mkdir(parents=True, exist_ok=True)
    out = artifacts / f"{timestamp_tag()}_skipped.json"
    payload = {
        "timestamp": timestamp_tag(),
        "target": slug,
        "oracle_response_file": str(response_path),
        "reason": reason,
        "input_prefix": text[:500],
    }
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return out


def prior_consensus_count(slug: str) -> int:
    artifacts = TARGETS_DIR / slug / "codex_consensus_artifacts"
    if not artifacts.exists():
        return 0
    return len(list(artifacts.glob("*_consensus.json")))


def select_direction(slug: str, override: int | None) -> int:
    if override is not None:
        if override not in (0, 1, 2):
            raise ValueError("--direction-index must be 0, 1, or 2")
        return override
    return prior_consensus_count(slug) % 3


def read_verified_state_context(slug: str) -> str:
    target_dir = TARGETS_DIR / slug
    verified = target_dir / "VERIFIED_STATE.md"
    if verified.exists():
        return verified.read_text(encoding="utf-8", errors="replace")[:6000]
    question = target_dir / "next_oracle_question.md"
    if not question.exists():
        return ""
    lines = question.read_text(encoding="utf-8", errors="replace").splitlines()
    kept: list[str] = []
    skip_prediction_line = re.compile(r"predicted\s+result", re.I)
    for line in lines[:80]:
        if skip_prediction_line.search(line):
            continue
        kept.append(line)
    return "\n".join(kept).strip()


def make_worker_prompt(slug: str, direction: Direction, result_path: Path, context: str) -> str:
    return f"""You are one of three independent Codex verification workers for the outreach pipeline.

Target: {slug}

Verified-state context:
{context}

Chosen Oracle attack direction, blinded from Oracle prediction:

Theorem / structure to use:
{direction.theorem}

Finite Python computation:
{direction.finite_python_computation}

Kill / confirm criterion:
{direction.kill_criterion}

Task:
Implement the finite Python computation independently. Write the final numerical result as JSON to:
{result_path}

Do not read other workers' outputs. Use pure Python stdlib only unless mathlib-style packages are obviously needed. If you write a script, save it next to result.json.

Output JSON schema exactly:
{{"result": <number|list|dict>, "script_path": <abs path or null>, "notes": <short str>, "runtime_sec": <float>}}
"""


def run_one_worker(
    worker_id: int,
    slug: str,
    direction: Direction,
    run_tag: str,
    direction_index: int,
    timeout_sec: int,
    context: str,
) -> WorkerRecord:
    target_dir = TARGETS_DIR / slug
    worker_dir = target_dir / "codex_consensus_artifacts" / "_workers" / f"{run_tag}_dir{direction_index}_w{worker_id}"
    worker_dir.mkdir(parents=True, exist_ok=True)
    result_path = worker_dir / "result.json"
    prompt_path = worker_dir / "prompt.txt"
    stdout_path = worker_dir / "stdout.txt"
    stderr_path = worker_dir / "stderr.txt"
    prompt = make_worker_prompt(slug, direction, result_path.resolve(), context)
    prompt_path.write_text(prompt, encoding="utf-8")
    cmd = [
        "codex",
        "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C",
        str(target_dir.resolve()),
        prompt,
    ]
    started = time.time()
    try:
        with open(stdout_path, "w", encoding="utf-8") as out, open(stderr_path, "w", encoding="utf-8") as err:
            proc = subprocess.Popen(
                cmd,
                cwd=str(REPO_ROOT),
                stdin=subprocess.DEVNULL,
                stdout=out,
                stderr=err,
                text=True,
                start_new_session=True,
            )
            try:
                rc = proc.wait(timeout=timeout_sec)
            except subprocess.TimeoutExpired:
                rc = 124
                try:
                    proc.terminate()
                except OSError:
                    pass
                time.sleep(2)
                if proc.poll() is None:
                    try:
                        proc.kill()
                    except OSError:
                        pass
    except OSError as exc:
        return WorkerRecord(worker_id, "fail", str(result_path), error=f"spawn_error: {exc}")

    elapsed = time.time() - started
    stdout_tail = read_tail(stdout_path)
    stderr_tail = read_tail(stderr_path)
    if rc == 124:
        return WorkerRecord(worker_id, "fail", str(result_path), stdout_tail, stderr_tail, error="timeout")
    if not result_path.exists():
        return WorkerRecord(worker_id, "fail", str(result_path), stdout_tail, stderr_tail, error="missing")
    try:
        payload = json.loads(result_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return WorkerRecord(worker_id, "fail", str(result_path), stdout_tail, stderr_tail, error=f"parse_error: {exc}")
    if not isinstance(payload, dict) or "result" not in payload:
        return WorkerRecord(worker_id, "fail", str(result_path), stdout_tail, stderr_tail, error="parse_error: missing result")
    return WorkerRecord(
        worker_id=worker_id,
        status="done",
        result_path=str(result_path),
        stdout_tail=stdout_tail,
        stderr_tail=stderr_tail,
        result=payload.get("result"),
        script_path=payload.get("script_path"),
        notes=str(payload.get("notes") or ""),
        runtime_sec=float(payload.get("runtime_sec", elapsed) or elapsed),
    )


def read_tail(path: Path, limit: int = 500) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    return text[-limit:]


def run_workers(
    slug: str,
    direction_index: int,
    direction: Direction,
    run_tag: str,
    timeout_sec: int,
) -> list[WorkerRecord]:
    context = read_verified_state_context(slug)
    statuses = {0: "running", 1: "running", 2: "running"}
    started = time.time()
    last_heartbeat = 0.0
    records: dict[int, WorkerRecord] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        future_map = {
            pool.submit(run_one_worker, i, slug, direction, run_tag, direction_index, timeout_sec, context): i
            for i in range(3)
        }
        while future_map:
            done, _pending = concurrent.futures.wait(
                future_map,
                timeout=1.0,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            for fut in done:
                worker_id = future_map.pop(fut)
                try:
                    rec = fut.result()
                except Exception as exc:  # noqa: BLE001
                    rec = WorkerRecord(worker_id, "fail", "", error=f"exception: {exc}")
                records[worker_id] = rec
                statuses[worker_id] = "done" if rec.status == "done" else "fail"
            elapsed = time.time() - started
            if elapsed - last_heartbeat >= 20 or not future_map:
                last_heartbeat = elapsed
                log(
                    "t={:.0f}s workers: w0={} w1={} w2={}".format(
                        elapsed, statuses[0], statuses[1], statuses[2]
                    )
                )
    return [records[i] for i in range(3)]


def normalize_for_output(value: Any) -> Any:
    if isinstance(value, float):
        if math.isfinite(value) and value.is_integer():
            return int(value)
        return value
    if isinstance(value, list):
        return [normalize_for_output(v) for v in value]
    if isinstance(value, dict):
        return {str(k): normalize_for_output(value[k]) for k in sorted(value)}
    return value


def numbers_equal(a: int | float, b: int | float) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return a == b
    if isinstance(a, int) and isinstance(b, int):
        return abs(a - b) <= 1e-9
    return math.isclose(float(a), float(b), rel_tol=1e-6, abs_tol=1e-9)


def results_equal(a: Any, b: Any) -> bool:
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return numbers_equal(a, b)
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(results_equal(x, y) for x, y in zip(a, b))
    if isinstance(a, dict) and isinstance(b, dict):
        if set(map(str, a.keys())) != set(map(str, b.keys())):
            return False
        a_str = {str(k): v for k, v in a.items()}
        b_str = {str(k): v for k, v in b.items()}
        return all(results_equal(a_str[k], b_str[k]) for k in a_str)
    return a == b


def largest_cluster(values: list[Any]) -> tuple[list[int], Any | None]:
    best: list[int] = []
    best_value: Any | None = None
    for i, value in enumerate(values):
        cluster = [j for j, other in enumerate(values) if results_equal(value, other)]
        if len(cluster) > len(best):
            best = cluster
            best_value = value
    return best, best_value


def parse_prediction_value(text: str) -> Any | None:
    stripped = text.strip()
    if not stripped:
        return None
    candidates = [stripped]
    m = re.search(r"(?<![A-Za-z0-9_])[-+]?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?(?![A-Za-z0-9_])", stripped)
    if m:
        candidates.append(m.group(0))
    for candidate in candidates:
        try:
            return json.loads(candidate)
        except json.JSONDecodeError:
            pass
        try:
            if re.fullmatch(r"[-+]?\d+", candidate):
                return int(candidate)
            if re.fullmatch(r"[-+]?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?", candidate):
                return float(candidate)
        except ValueError:
            pass
    return None


def evaluate_consensus(records: list[WorkerRecord], predicted_raw: str) -> tuple[Any | None, bool | None, str]:
    successes = [rec.result for rec in records if rec.status == "done"]
    if len(successes) < 2:
        return None, None, "NO_CONSENSUS_INSUFFICIENT_WORKERS"
    cluster, consensus = largest_cluster(successes)
    if len(cluster) < 2:
        return None, None, "NO_CONSENSUS"
    prediction = parse_prediction_value(predicted_raw)
    if prediction is None:
        matches: bool | None = None
        verdict = "PASS_CONSENSUS_MATCHES_PREDICTION"
    else:
        matches = results_equal(consensus, prediction)
        verdict = "PASS_CONSENSUS_MATCHES_PREDICTION" if matches else "PASS_CONSENSUS_CONTRADICTS_PREDICTION"
    return normalize_for_output(consensus), matches, verdict


def worker_record_to_json(record: WorkerRecord) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "worker_id": record.worker_id,
        "status": record.status,
        "result_path": record.result_path,
    }
    if record.status == "done":
        payload.update({
            "result": normalize_for_output(record.result),
            "script_path": record.script_path,
            "notes": record.notes,
            "runtime_sec": record.runtime_sec,
        })
    else:
        payload.update({
            "error": record.error,
            "stderr_tail": record.stderr_tail[-500:],
            "stdout_tail": record.stdout_tail[-500:],
        })
    return payload


def one_line(text: str, limit: int = 140) -> str:
    compact = re.sub(r"\s+", " ", text).strip()
    if len(compact) <= limit:
        return compact
    return compact[: limit - 3].rstrip() + "..."


def append_or_replace_prior_block(slug: str, artifact_path: Path, payload: dict[str, Any]) -> None:
    question_path = TARGETS_DIR / slug / "next_oracle_question.md"
    if not question_path.exists():
        return
    direction = payload["direction_4tuple"]
    outputs = []
    for rec in payload["worker_outputs"]:
        if rec.get("status") == "done":
            outputs.append(f"w{rec['worker_id']}={json.dumps(rec.get('result'), ensure_ascii=False)}")
        else:
            outputs.append(f"w{rec['worker_id']}={rec.get('error') or 'fail'}")
    consensus = payload.get("consensus_result")
    match = payload.get("matches_prediction")
    if match is True:
        match_text = "yes"
    elif match is False:
        match_text = "no"
    else:
        match_text = "unverifiable"
    rel_artifact = artifact_path.relative_to(SCRIPT_DIR)
    block = "\n".join([
        BEGIN_BLOCK,
        "## Previous round Codex consensus result",
        f"- Direction selected: {int(payload['direction_index']) + 1} - {one_line(direction.get('theorem', ''))}",
        f"- Worker outputs: {', '.join(outputs)}",
        f"- Consensus: {json.dumps(consensus, ensure_ascii=False) if consensus is not None else 'no consensus'}",
        f"- Oracle prediction: {payload.get('predicted_result_raw') or ''}",
        f"- Match: {match_text}",
        f"- Verdict: {payload.get('verdict')}",
        f"- Artifact: {rel_artifact}",
        END_BLOCK,
        "",
    ])
    text = question_path.read_text(encoding="utf-8", errors="replace")
    pattern = re.compile(re.escape(BEGIN_BLOCK) + r".*?" + re.escape(END_BLOCK) + r"\n?", re.S)
    if pattern.search(text):
        new_text = pattern.sub(block, text)
    else:
        new_text = text.rstrip() + "\n\n" + block
    question_path.write_text(new_text, encoding="utf-8")


def write_consensus_artifact(
    slug: str,
    run_tag: str,
    direction_index: int,
    direction: Direction,
    records: list[WorkerRecord],
    response_path: Path,
) -> Path:
    consensus, matches, verdict = evaluate_consensus(records, direction.predicted_result)
    artifacts = TARGETS_DIR / slug / "codex_consensus_artifacts"
    artifacts.mkdir(parents=True, exist_ok=True)
    out = artifacts / f"{run_tag}_dir{direction_index}_consensus.json"
    payload = {
        "timestamp": run_tag,
        "target": slug,
        "direction_index": direction_index,
        "direction_4tuple": {
            "theorem": direction.theorem,
            "finite_python_computation": direction.finite_python_computation,
            "kill_criterion": direction.kill_criterion,
            "predicted_result": direction.predicted_result,
        },
        "worker_outputs": [worker_record_to_json(record) for record in records],
        "consensus_result": consensus,
        "predicted_result_raw": direction.predicted_result,
        "matches_prediction": matches,
        "verdict": verdict,
        "oracle_response_file": str(response_path),
    }
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    append_or_replace_prior_block(slug, out, payload)
    return out


def print_dry_run(directions: list[Direction], chosen: int, response_path: Path) -> None:
    log(f"dry-run response_file={response_path}")
    log(f"parsed_directions={len(directions)} chosen_direction_index={chosen}")
    for idx, direction in enumerate(directions):
        print(f"\nDirection {idx}:")
        print(f"  theorem: {one_line(direction.theorem, 220)}")
        print(f"  finite_python_computation: {one_line(direction.finite_python_computation, 220)}")
        print(f"  kill_criterion: {one_line(direction.kill_criterion, 220)}")
        print(f"  predicted_result: {one_line(direction.predicted_result, 220)}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True, help="target slug under tools/community-outreach/targets")
    parser.add_argument("--direction-index", type=int, choices=(0, 1, 2), default=None)
    parser.add_argument("--worker-timeout-sec", type=int, default=3600)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)

    slug = args.target
    target_dir = TARGETS_DIR / slug
    if not target_dir.exists():
        print(f"[consensus] target dir missing: {target_dir}", file=sys.stderr)
        return 1
    try:
        response_path = locate_latest_oracle_response(slug)
    except Exception as exc:  # noqa: BLE001
        print(f"[consensus] {exc}", file=sys.stderr)
        return 1
    text = response_path.read_text(encoding="utf-8", errors="replace")
    directions = parse_directions(text)
    if len(directions) < 3:
        skipped = write_skipped_artifact(slug, response_path, text, "old_format_or_unparseable")
        log(f"skipped old/unparseable Oracle response; artifact={skipped}")
        return 2
    chosen = select_direction(slug, args.direction_index)
    if args.dry_run:
        print_dry_run(directions, chosen, response_path)
        return 0
    run_tag = timestamp_tag()
    log(f"selected direction index={chosen} run_tag={run_tag}")
    records = run_workers(slug, chosen, directions[chosen], run_tag, args.worker_timeout_sec)
    artifact = write_consensus_artifact(slug, run_tag, chosen, directions[chosen], records, response_path)
    log(f"wrote consensus artifact: {artifact}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
