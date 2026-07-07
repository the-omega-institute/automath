#!/usr/bin/env python3
"""Validate the accepted-certificate JSONL schema used by this artifact."""
import argparse
import json
import pathlib
import sys

REQUIRED = {
    "id": str,
    "set": str,
    "eq1_id": int,
    "eq2_id": int,
    "equation1": str,
    "equation2": str,
    "truth": bool,
    "verdict": str,
    "code": str,
}


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("jsonl", type=pathlib.Path)
    return parser


def validate_row(row, line_no):
    errors = []
    for key, typ in REQUIRED.items():
        if key not in row:
            errors.append(f"line {line_no}: missing {key}")
            continue
        if not isinstance(row[key], typ):
            errors.append(f"line {line_no}: {key} must be {typ.__name__}")
    if row.get("set") not in {"sample_200", "hard2"}:
        errors.append(f"line {line_no}: set must be sample_200 or hard2")
    if row.get("verdict") not in {"true", "false"}:
        errors.append(f"line {line_no}: verdict must be true or false")
    if isinstance(row.get("truth"), bool):
        expected = "true" if row["truth"] else "false"
        if row.get("verdict") != expected:
            errors.append(f"line {line_no}: verdict does not match truth")
    if not row.get("code"):
        errors.append(f"line {line_no}: code must be nonempty")
    return errors


def main():
    args = build_parser().parse_args()
    errors = []
    count = 0
    with args.jsonl.open() as fh:
        for line_no, line in enumerate(fh, 1):
            if not line.strip():
                continue
            count += 1
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                errors.append(f"line {line_no}: invalid JSON: {exc}")
                continue
            errors.extend(validate_row(row, line_no))
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print(f"ok: {args.jsonl} ({count} certificates)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
