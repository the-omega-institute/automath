#!/usr/bin/env python3
"""Generate the final SHA-256 digest manifest for the support surface."""
from __future__ import annotations

import hashlib
import platform
import subprocess
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "review_bundle" / "FINAL_DIGESTS_SHA256.md"
LOG = ROOT / "review_bundle" / "final_digest_generation_run.log"
EXCLUDED = {
    Path("review_bundle/FINAL_DIGESTS_SHA256.md").as_posix(),
    Path("review_bundle/final_digest_generation_run.log").as_posix(),
}


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        return "unavailable"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def support_paths() -> list[Path]:
    paths: list[Path] = []
    for path in ROOT.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(ROOT).as_posix()
        if ".git/" in relative or relative.startswith(".git/"):
            continue
        if relative in EXCLUDED:
            continue
        if "__pycache__/" in relative or relative.endswith(".pyc"):
            continue
        paths.append(path)
    return sorted(paths, key=lambda p: p.relative_to(ROOT).as_posix().lower())


def main() -> int:
    now_utc = datetime.now(timezone.utc)
    local = now_utc.astimezone()
    paths = support_paths()
    command = "python review_bundle/generate_final_digests.py"
    environment = f"Python {platform.python_version()} on {platform.system()} {platform.release()}"
    cwd = str(ROOT)
    commit = git_head()

    lines = [
        "# Final SHA-256 Digest Manifest",
        "",
        f"Generated at local time `{local.isoformat(timespec='seconds')}` (`{now_utc.isoformat(timespec='seconds')}` UTC).",
        "",
        f"Command: `{command}`",
        f"Environment: `{environment}`",
        f"Working directory: `{cwd}`",
        f"Source commit: `{commit}`",
        "Generation log: `review_bundle/final_digest_generation_run.log`",
        "Excluded self-digest inputs: `review_bundle/FINAL_DIGESTS_SHA256.md, review_bundle/final_digest_generation_run.log`",
        f"Path count: `{len(paths)}`",
        "",
        "| Path | SHA-256 |",
        "| --- | --- |",
    ]
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        lines.append(f"| `{relative}` | `{sha256_file(path)}` |")
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")

    log_lines = [
        f"command={command}",
        f"cwd={cwd}",
        f"generated_utc={now_utc.isoformat(timespec='seconds')}",
        f"source_commit={commit}",
        f"environment={environment}",
        "exit_code=0",
        "output=review_bundle/FINAL_DIGESTS_SHA256.md",
        "excluded=review_bundle/FINAL_DIGESTS_SHA256.md; review_bundle/final_digest_generation_run.log",
        f"file_count={len(paths)}",
    ]
    LOG.write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT).as_posix()} with {len(paths)} paths")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
