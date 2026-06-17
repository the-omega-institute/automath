#!/usr/bin/env python3
"""Static source-level scan for TeX labels and stale endpoint-certificate tokens.

This checker is intentionally lexical.  It does not evaluate TeX conditionals,
comments, includes, or macros.  Every occurrence in the selected source bytes is
counted, including material that would be inactive in a compiled TeX run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    "main.tex",
    "submission_abstract.tex",
    "appendix_full_technical_ledger.tex",
)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
FORBIDDEN_TOKENS = (
    "199/100",
    "101/300",
    "203/600",
    "s=199/100",
    "central roots \\ge101/300",
    "endpoint roots <101/300",
)


def read_bytes(path: Path) -> bytes:
    return path.read_bytes()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def line_col(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    line_start = text.rfind("\n", 0, offset) + 1
    return line, offset - line_start + 1


def scan_source(relative: str) -> dict[str, object]:
    path = ROOT / relative
    raw = read_bytes(path)
    text = raw.decode("utf-8-sig")
    labels = []
    for match in LABEL_RE.finditer(text):
        line, column = line_col(text, match.start())
        labels.append(
            {
                "label": match.group(1),
                "line": line,
                "column": column,
            }
        )
    duplicates = sorted(
        label for label, count in Counter(item["label"] for item in labels).items() if count > 1
    )
    forbidden_hits = []
    for token in FORBIDDEN_TOKENS:
        start = 0
        while True:
            offset = text.find(token, start)
            if offset < 0:
                break
            line, column = line_col(text, offset)
            forbidden_hits.append({"token": token, "line": line, "column": column})
            start = offset + len(token)
    return {
        "source": relative,
        "sha256": sha256_bytes(raw),
        "byte_count": len(raw),
        "label_count": len(labels),
        "unique_label_count": len({item["label"] for item in labels}),
        "duplicate_label_count": len(duplicates),
        "duplicate_labels": duplicates,
        "forbidden_endpoint_certificate_token_count": len(forbidden_hits),
        "forbidden_endpoint_certificate_hits": forbidden_hits,
        "labels": labels,
    }


def build_report() -> dict[str, object]:
    source_reports = [scan_source(source) for source in SOURCES]
    label_locations: dict[str, list[dict[str, object]]] = defaultdict(list)
    for report in source_reports:
        source = str(report["source"])
        for item in report["labels"]:
            label_locations[str(item["label"])].append(
                {
                    "source": source,
                    "line": item["line"],
                    "column": item["column"],
                }
            )
    cross_source_duplicates = {
        label: locations
        for label, locations in sorted(label_locations.items())
        if len(locations) > 1
    }
    errors = []
    for report in source_reports:
        if report["duplicate_label_count"]:
            errors.append(f"{report['source']}: duplicate labels")
        if report["forbidden_endpoint_certificate_token_count"]:
            errors.append(f"{report['source']}: stale endpoint-certificate token")
    if cross_source_duplicates:
        errors.append("cross-source duplicate labels")
    return {
        "command": "python certificates/scan_tex_source_labels.py --write certificates/static_source_label_scan.json",
        "scan_policy": "raw lexical scan of selected TeX source bytes; TeX conditionals, comments, includes, and macros are not evaluated, so inactive branches are included",
        "source_root": str(ROOT).replace("\\", "/"),
        "sources": list(SOURCES),
        "label_pattern": r"\\label\{([^}]*)\}",
        "forbidden_endpoint_certificate_tokens": list(FORBIDDEN_TOKENS),
        "source_reports": source_reports,
        "total_label_count": sum(int(report["label_count"]) for report in source_reports),
        "total_unique_label_count": len(label_locations),
        "cross_source_duplicate_label_count": len(cross_source_duplicates),
        "cross_source_duplicate_labels": cross_source_duplicates,
        "total_forbidden_endpoint_certificate_token_count": sum(
            int(report["forbidden_endpoint_certificate_token_count"])
            for report in source_reports
        ),
        "errors": errors,
        "exit_code": 1 if errors else 0,
        "boundary": "source-level label uniqueness and stale endpoint-certificate-token absence only; no proof checking or semantic theorem validation",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path, help="write the JSON report to this path")
    args = parser.parse_args(argv)
    report = build_report()
    output = json.dumps(report, indent=2, sort_keys=True)
    if args.write:
        target = args.write if args.write.is_absolute() else ROOT / args.write
        target.write_text(output + "\n", encoding="utf-8")
    print(output)
    return int(report["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
