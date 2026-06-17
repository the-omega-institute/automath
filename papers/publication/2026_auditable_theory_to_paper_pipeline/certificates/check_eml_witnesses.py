#!/usr/bin/env python3
"""Check finite pure-EML syntax witnesses.

This checker proves only membership in the grammar
    S -> 1 | x | EML[S,S]
for the catalogue strings.  It intentionally has no real-domain semantics.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


EXPECTED_KEYS = ("W_PI_EML", "W_SIN_EML_X", "W_SQRT_EML_X")


@dataclass(frozen=True)
class Stats:
    eml_nodes: int
    depth: int


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_term(text: str, pos: int = 0) -> tuple[Stats, int]:
    if text.startswith("1", pos):
        return Stats(eml_nodes=0, depth=1), pos + 1
    if text.startswith("x", pos):
        return Stats(eml_nodes=0, depth=1), pos + 1
    if not text.startswith("EML[", pos):
        raise ValueError(f"expected '1', 'x', or 'EML[' at byte {pos}")

    left, pos = parse_term(text, pos + 4)
    if pos >= len(text) or text[pos] != ",":
        raise ValueError(f"expected ',' at byte {pos}")
    right, pos = parse_term(text, pos + 1)
    if pos >= len(text) or text[pos] != "]":
        raise ValueError(f"expected ']' at byte {pos}")
    return Stats(
        eml_nodes=1 + left.eml_nodes + right.eml_nodes,
        depth=1 + max(left.depth, right.depth),
    ), pos + 1


def parse_complete(text: str) -> Stats:
    stats, pos = parse_term(text)
    if pos != len(text):
        raise ValueError(f"trailing bytes after byte {pos}")
    return stats


def load_catalogue(path: Path) -> tuple[dict[str, Any], str]:
    data = path.read_bytes()
    return json.loads(data.decode("utf-8")), sha256_bytes(data)


def build_report(catalogue_path: Path) -> dict[str, Any]:
    catalogue, catalogue_sha256 = load_catalogue(catalogue_path)
    witnesses = catalogue.get("witnesses", [])
    keys = [row.get("catalogue_key") for row in witnesses]
    if tuple(keys) != EXPECTED_KEYS:
        raise ValueError(
            f"catalogue keys must be exactly {EXPECTED_KEYS}, got {tuple(keys)}"
        )

    rows = []
    for row in witnesses:
        term = row["term"]
        stats = parse_complete(term)
        rows.append(
            {
                "printed_name": row["printed_name"],
                "catalogue_key": row["catalogue_key"],
                "role": row["role"],
                "semantic_status": row["semantic_status"],
                "eml_nodes": stats.eml_nodes,
                "depth": stats.depth,
                "sha256": sha256_bytes(term.encode("utf-8")),
            }
        )

    return {
        "catalogue_path": str(catalogue_path.as_posix()),
        "catalogue_sha256": catalogue_sha256,
        "grammar": "S -> 1 | x | EML[S,S]",
        "checker_claim": "finite grammar membership only; no real-domain semantic identity",
        "witnesses": rows,
        "status": "syntax_certificate_ok",
    }


def validate_certificate(report: dict[str, Any], certificate_path: Path) -> None:
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    manifest = certificate["reproducible_artifact_manifest"]
    if manifest["catalogue_sha256"] != report["catalogue_sha256"]:
        raise ValueError("catalogue SHA-256 mismatch")
    if certificate["checker_claim"] != report["checker_claim"]:
        raise ValueError("checker claim mismatch")

    expected = {
        row["catalogue_key"]: row
        for row in certificate["witnesses"]
    }
    for row in report["witnesses"]:
        cert_row = expected[row["catalogue_key"]]
        for field in ("printed_name", "eml_nodes", "depth", "sha256"):
            if cert_row[field] != row[field]:
                raise ValueError(
                    f"{row['catalogue_key']} {field} mismatch: "
                    f"{cert_row[field]!r} != {row[field]!r}"
                )


def write_json(report: dict[str, Any]) -> None:
    json.dump(report, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


def write_csv(report: dict[str, Any]) -> None:
    fieldnames = ["printed_name", "catalogue_key", "eml_nodes", "depth", "sha256"]
    writer = csv.DictWriter(sys.stdout, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    for row in report["witnesses"]:
        writer.writerow({field: row[field] for field in fieldnames})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "catalogue",
        nargs="?",
        default="certificates/eml_witness_catalogue.json",
        help="JSON catalogue of finite EML witness strings",
    )
    parser.add_argument(
        "certificate",
        nargs="?",
        help="optional certificate JSON whose hashes and statistics are checked",
    )
    parser.add_argument("--format", choices=("json", "csv"), default="json")
    args = parser.parse_args()

    try:
        report = build_report(Path(args.catalogue))
        if args.certificate:
            validate_certificate(report, Path(args.certificate))
    except Exception as exc:  # keep CLI failure concise and auditable
        print(f"syntax_certificate_failed: {exc}", file=sys.stderr)
        return 1

    if args.format == "json":
        write_json(report)
    else:
        write_csv(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
