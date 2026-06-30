#!/usr/bin/env python3
"""Combined SAIR-EQT2 FKST dogfood status report."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
HEALTH = ROOT / "scripts" / "sair_eqt2_health_check.py"
LEDGER = ROOT / "scripts" / "sair_eqt2_ledger_audit.py"


def run_json(command: list[str]) -> tuple[dict | None, str | None]:
    result = subprocess.run(command, check=False, text=True, capture_output=True)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        return None, detail or f"command failed with {result.returncode}"
    return json.loads(result.stdout), None


def run(command: list[str]) -> str | None:
    result = subprocess.run(command, check=False, text=True, capture_output=True)
    if result.returncode != 0:
        return (result.stderr or result.stdout).strip() or f"command failed with {result.returncode}"
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jsonl", default="/tmp/fkst-sair-eqt2-health.jsonl")
    parser.add_argument("--final-24h", action="store_true")
    parser.add_argument("--append-current", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    min_age = "86400" if args.final_24h else "0"
    min_samples = "24" if args.final_24h else "1"
    gates = {
        "min_age_seconds": int(min_age),
        "min_samples": int(min_samples),
        "max_gap_seconds": 1800,
        "max_staleness_seconds": 1800,
        "max_first_age_seconds": 1800,
        "append_current": args.append_current,
    }
    append_error = None
    if args.append_current:
        append_error = run(
            [
                sys.executable,
                str(HEALTH),
                "--min-age-seconds",
                min_age,
                "--append-jsonl",
                args.jsonl,
            ]
        )
    health, health_error = run_json(
        [
            sys.executable,
            str(HEALTH),
            "--min-age-seconds",
            min_age,
            "--json",
        ]
    )
    ledger, ledger_error = run_json(
        [
            sys.executable,
            str(LEDGER),
            "--jsonl",
            args.jsonl,
            "--min-age-seconds",
            min_age,
            "--min-samples",
            min_samples,
            "--max-gap-seconds",
            "1800",
            "--max-staleness-seconds",
            "1800",
            "--max-first-age-seconds",
            "1800",
            "--json",
        ]
    )

    ok = append_error is None and health_error is None and ledger_error is None
    record = {
        "schema": "omega.sair_eqt2.status_report.v1",
        "checked_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "target": "SAIR-EQT2",
        "final_24h": args.final_24h,
        "status": "ok" if ok else "not_ready",
        "append_current": args.append_current,
        "append_error": append_error,
        "gates": gates,
        "health": health,
        "health_error": health_error,
        "ledger": ledger,
        "ledger_error": ledger_error,
    }

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")

    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        print("target: SAIR-EQT2")
        print(f"status: {record['status']}")
        print(f"final_24h: {str(args.final_24h).lower()}")
        if health is not None:
            print(f"runtime_age_seconds: {health['runtime_age_seconds']}")
        else:
            print(f"health_error: {health_error}")
        if ledger is not None:
            print(f"ledger_samples: {ledger['samples']}")
            print(f"ledger_final_age_seconds: {ledger['final_runtime_age_seconds']}")
            print(f"ledger_staleness_seconds: {ledger['staleness_seconds']}")
        else:
            print(f"ledger_error: {ledger_error}")

    if append_error is not None or not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
