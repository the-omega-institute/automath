#!/usr/bin/env python3
"""Minimal finite-frontier search harness.

This runner does not invent search moves. It evaluates one artifact against a
target's score and verifier commands, then updates frontier_state.json if the
artifact improves the best known score or verifies the target.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TARGETS_DIR = ROOT / "targets"


@dataclass
class TargetConfig:
    slug: str
    title: str
    score_command: list[str]
    verify_command: list[str]
    lower_is_better: bool
    initial_artifact: str


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _load_simple_yaml(path: Path) -> dict:
    """Tiny YAML subset parser for target.yaml.

    Supports `key: value`, booleans, and JSON-style lists. This avoids adding a
    dependency while keeping the target file readable.
    """
    data: dict = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line or ":" not in line:
            continue
        key, value = line.split(":", 1)
        key = key.strip()
        value = value.strip()
        if value.lower() in {"true", "false"}:
            data[key] = value.lower() == "true"
        elif value.startswith("["):
            data[key] = json.loads(value)
        else:
            data[key] = value.strip('"').strip("'")
    return data


def load_config(slug: str) -> TargetConfig:
    target_dir = TARGETS_DIR / slug
    data = _load_simple_yaml(target_dir / "target.yaml")
    required = ["slug", "title", "score_command", "verify_command", "initial_artifact"]
    missing = [k for k in required if k not in data]
    if missing:
        raise ValueError(f"{slug} target.yaml missing: {', '.join(missing)}")
    return TargetConfig(
        slug=str(data["slug"]),
        title=str(data["title"]),
        score_command=list(data["score_command"]),
        verify_command=list(data["verify_command"]),
        lower_is_better=bool(data.get("lower_is_better", True)),
        initial_artifact=str(data["initial_artifact"]),
    )


def _state_path(slug: str) -> Path:
    return TARGETS_DIR / slug / "frontier_state.json"


def _load_state(slug: str) -> dict:
    try:
        return json.loads(_state_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"schema_version": "frontier-search-state-v1", "slug": slug, "attempts": []}


def _write_state(slug: str, state: dict) -> None:
    path = _state_path(slug)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def _run_json(cmd_template: list[str], *, artifact: Path, cwd: Path, timeout_s: int) -> dict:
    cmd = [part.replace("{artifact}", str(artifact)) for part in cmd_template]
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        payload = {"ok": False, "error": "stdout was not JSON", "stdout": proc.stdout[:1000]}
    payload.setdefault("returncode", proc.returncode)
    if proc.stderr:
        payload["stderr"] = proc.stderr[:1000]
    if proc.returncode != 0:
        payload["ok"] = False
    return payload


def _is_improvement(*, score: float, best_score: float | None, lower_is_better: bool) -> bool:
    if best_score is None:
        return True
    return score < best_score if lower_is_better else score > best_score


def evaluate_artifact(slug: str, artifact: Path, *, timeout_s: int = 600) -> dict:
    cfg = load_config(slug)
    target_dir = TARGETS_DIR / slug
    artifact = artifact if artifact.is_absolute() else target_dir / artifact
    if not artifact.exists():
        raise FileNotFoundError(artifact)
    state = _load_state(slug)
    score_payload = _run_json(cfg.score_command, artifact=artifact, cwd=target_dir, timeout_s=timeout_s)
    verify_payload = _run_json(cfg.verify_command, artifact=artifact, cwd=target_dir, timeout_s=timeout_s)
    score = score_payload.get("score")
    if score is None:
        score_value = None
        improved = False
    else:
        score_value = float(score)
        best = state.get("best_score")
        best_score = float(best) if best is not None else None
        improved = _is_improvement(score=score_value, best_score=best_score, lower_is_better=cfg.lower_is_better)

    attempts_dir = target_dir / "attempts"
    attempts_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    attempt_dir = attempts_dir / stamp
    attempt_dir.mkdir(parents=True, exist_ok=True)
    copied_artifact = attempt_dir / artifact.name
    if artifact.resolve() != copied_artifact.resolve():
        shutil.copy2(artifact, copied_artifact)

    verified = bool(verify_payload.get("verified"))
    if improved or verified:
        best_dir = target_dir / "best"
        best_dir.mkdir(parents=True, exist_ok=True)
        best_artifact = best_dir / artifact.name
        shutil.copy2(artifact, best_artifact)
        state["best_artifact"] = str(best_artifact.relative_to(target_dir))
        state["best_score"] = score_value
        state["best_verified"] = verified
        state["best_updated_at"] = _now_iso()

    attempt = {
        "attempted_at": _now_iso(),
        "artifact": str(copied_artifact.relative_to(target_dir)),
        "score": score_value,
        "score_payload": score_payload,
        "verify_payload": verify_payload,
        "improved": improved,
        "verified": verified,
    }
    history = state.setdefault("attempts", [])
    if isinstance(history, list):
        history.append(attempt)
        state["attempts"] = history[-100:]
    state["last_attempt"] = attempt
    state["title"] = cfg.title
    _write_state(slug, state)
    _append_run_record(target_dir, attempt)
    return state


def _append_run_record(target_dir: Path, attempt: dict) -> None:
    path = target_dir / "run_record.md"
    if not path.exists():
        path.write_text(f"# Frontier Run Record - {target_dir.name}\n\n", encoding="utf-8")
    line = (
        f"- {attempt['attempted_at']} score={attempt.get('score')} "
        f"improved={attempt.get('improved')} verified={attempt.get('verified')} "
        f"artifact=`{attempt.get('artifact')}`\n"
    )
    with open(path, "a", encoding="utf-8") as f:
        f.write(line)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("slug")
    parser.add_argument("--artifact", default="", help="artifact path relative to target dir; defaults to initial_artifact")
    parser.add_argument("--timeout-s", type=int, default=600)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    cfg = load_config(args.slug)
    artifact = Path(args.artifact or cfg.initial_artifact)
    state = evaluate_artifact(args.slug, artifact, timeout_s=args.timeout_s)
    if args.json:
        print(json.dumps(state, ensure_ascii=False, indent=2))
    else:
        last = state.get("last_attempt") or {}
        print(
            f"{args.slug}: score={last.get('score')} "
            f"improved={last.get('improved')} verified={last.get('verified')}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
