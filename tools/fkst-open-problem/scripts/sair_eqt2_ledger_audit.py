#!/usr/bin/env python3
"""Audit SAIR-EQT2 FKST health JSONL samples."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path


DEFAULT_JSONL = Path("/tmp/fkst-sair-eqt2-health.jsonl")
ALLOWED_GRAPHS = {
    "focused omega-sair-eqt2 only",
    "focused omega-sair-eqt2 portfolio",
}


def parse_time(value: str) -> datetime:
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def load_rows(path: Path) -> list[dict]:
    if not path.exists():
        raise SystemExit(f"missing health ledger: {path}")
    rows = []
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line:
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{path}:{index}: invalid JSON: {exc}") from exc
        rows.append(row)
    if not rows:
        raise SystemExit(f"{path}: no health rows")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jsonl", type=Path, default=DEFAULT_JSONL)
    parser.add_argument("--min-age-seconds", type=int, default=0)
    parser.add_argument("--min-samples", type=int, default=1)
    parser.add_argument("--max-gap-seconds", type=int, default=0)
    parser.add_argument("--max-staleness-seconds", type=int, default=0)
    parser.add_argument("--max-first-age-seconds", type=int, default=0)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    rows = load_rows(args.jsonl)
    if len(rows) < args.min_samples:
        raise SystemExit(f"only {len(rows)} samples, need {args.min_samples}")

    ok_rows = []
    error_rows = []
    for index, row in enumerate(rows, start=1):
        if row.get("target") != "SAIR-EQT2":
            raise SystemExit(f"row {index}: target is not SAIR-EQT2")
        schema = row.get("schema")
        if schema == "omega.sair_eqt2.health_error.v1":
            error_rows.append(row)
            continue
        if schema != "omega.sair_eqt2.health.v1":
            raise SystemExit(f"row {index}: unexpected schema {schema!r}")
        if row.get("state") != "running":
            raise SystemExit(f"row {index}: state is not running")
        if row.get("github_write") != "disabled":
            raise SystemExit(f"row {index}: GitHub write is not disabled")
        if row.get("graph") not in ALLOWED_GRAPHS:
            raise SystemExit(f"row {index}: graph is not focused")
        if row.get("runtime_errors") != "none matched":
            raise SystemExit(f"row {index}: runtime errors were reported")
        ok_rows.append(row)

    if error_rows:
        raise SystemExit(f"health ledger contains {len(error_rows)} error rows")
    if not ok_rows:
        raise SystemExit("health ledger contains no ok rows")

    times = [parse_time(row["checked_at"]) for row in ok_rows]
    ages = [int(row["runtime_age_seconds"]) for row in ok_rows]
    pids = {row.get("pid") for row in ok_rows}

    for index in range(1, len(times)):
        if times[index] < times[index - 1]:
            raise SystemExit(f"row {index + 1}: checked_at moved backwards")
        if ok_rows[index].get("pid") == ok_rows[index - 1].get("pid") and ages[index] < ages[index - 1]:
            raise SystemExit(f"row {index + 1}: runtime age moved backwards within one pid")
        if args.max_gap_seconds:
            gap = int((times[index] - times[index - 1]).total_seconds())
            if gap > args.max_gap_seconds:
                raise SystemExit(
                    f"row {index + 1}: sample gap {gap}s exceeds {args.max_gap_seconds}s"
                )

    final_age = ages[-1]
    first_age = ages[0]
    staleness_seconds = int((datetime.now(timezone.utc) - times[-1]).total_seconds())
    if args.max_first_age_seconds and first_age > args.max_first_age_seconds:
        raise SystemExit(
            f"first runtime age {first_age}s exceeds {args.max_first_age_seconds}s"
        )
    if args.min_age_seconds and final_age < args.min_age_seconds:
        raise SystemExit(
            f"final runtime age {final_age}s is below required {args.min_age_seconds}s"
        )
    if args.max_staleness_seconds and staleness_seconds > args.max_staleness_seconds:
        raise SystemExit(
            f"last sample is {staleness_seconds}s old, "
            f"exceeds {args.max_staleness_seconds}s"
        )

    record = {
        "schema": "omega.sair_eqt2.ledger_audit.v1",
        "target": "SAIR-EQT2",
        "jsonl": str(args.jsonl),
        "samples": len(ok_rows),
        "errors": 0,
        "pid_count": len(pids),
        "graphs": sorted({row.get("graph") for row in ok_rows}),
        "first_checked_at": times[0].strftime("%Y-%m-%dT%H:%M:%SZ"),
        "last_checked_at": times[-1].strftime("%Y-%m-%dT%H:%M:%SZ"),
        "first_runtime_age_seconds": first_age,
        "final_runtime_age_seconds": final_age,
        "min_age_seconds": args.min_age_seconds,
        "min_samples": args.min_samples,
        "max_gap_seconds": args.max_gap_seconds,
        "max_staleness_seconds": args.max_staleness_seconds,
        "max_first_age_seconds": args.max_first_age_seconds,
        "staleness_seconds": staleness_seconds,
        "ledger_audit": "ok",
    }
    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        print(f"target: {record['target']}")
        print(f"jsonl: {record['jsonl']}")
        print(f"samples: {record['samples']}")
        print(f"errors: {record['errors']}")
        print(f"pid_count: {record['pid_count']}")
        print(f"first_checked_at: {record['first_checked_at']}")
        print(f"last_checked_at: {record['last_checked_at']}")
        print(f"first_runtime_age_seconds: {record['first_runtime_age_seconds']}")
        print(f"final_runtime_age_seconds: {record['final_runtime_age_seconds']}")
        print(f"staleness_seconds: {record['staleness_seconds']}")
        print("ledger_audit: ok")


if __name__ == "__main__":
    main()
