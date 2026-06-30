#!/usr/bin/env python3
"""Append one SAIR-EQT2 FKST health sample, including failures."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys


DEFAULT_JSONL = Path("/tmp/fkst-sair-eqt2-health.jsonl")
ROOT = Path(__file__).resolve().parents[1]
HEALTH_CHECK = ROOT / "scripts" / "sair_eqt2_health_check.py"


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def append(path: Path, record: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--jsonl",
        type=Path,
        default=DEFAULT_JSONL,
        help="Health ledger path. Defaults to /tmp/fkst-sair-eqt2-health.jsonl.",
    )
    parser.add_argument(
        "--min-age-seconds",
        type=int,
        default=0,
        help="Pass through to the health check for final 24-hour verification.",
    )
    args = parser.parse_args()

    command = [
        sys.executable,
        str(HEALTH_CHECK),
        "--json",
    ]
    if args.min_age_seconds:
        command.extend(["--min-age-seconds", str(args.min_age_seconds)])
    result = subprocess.run(command, check=False, text=True, capture_output=True)
    if result.returncode == 0:
        record = json.loads(result.stdout)
        record["watch_status"] = "ok"
        append(args.jsonl, record)
        print(f"watch_status: ok")
        print(f"jsonl: {args.jsonl}")
        return

    append(
        args.jsonl,
        {
            "schema": "omega.sair_eqt2.health_error.v1",
            "checked_at": utc_now(),
            "target": "SAIR-EQT2",
            "watch_status": "error",
            "returncode": result.returncode,
            "stdout": result.stdout[-4000:],
            "stderr": result.stderr[-4000:],
        },
    )
    print("watch_status: error")
    print(f"jsonl: {args.jsonl}")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
