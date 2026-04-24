#!/usr/bin/env python3
"""Audit the Window-6 Fin 21 certificate against current ETP full_entries.json."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path


WINDOW_SAT = {10, 52, 55}
WINDOW_REF = {43, 46}
PAIRWISE = [(a, b) for a in sorted(WINDOW_SAT) for b in sorted(WINDOW_REF)]
ABSENT_PAIRWISE = [(10, 46), (52, 43), (52, 46), (55, 43), (55, 46)]


def equation_number(value: str) -> int:
    match = re.fullmatch(r"Equation(\d+)", value)
    if not match:
        raise ValueError(f"unexpected equation label {value!r}")
    return int(match.group(1))


def git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def facts_entries(entries: list[dict[str, object]]) -> list[dict[str, object]]:
    facts = []
    for entry in entries:
        variant = entry.get("variant")
        if not isinstance(variant, dict) or "facts" not in variant:
            continue
        payload = variant["facts"]
        if not isinstance(payload, dict):
            continue
        satisfied = {equation_number(item) for item in payload.get("satisfied", [])}
        refuted = {equation_number(item) for item in payload.get("refuted", [])}
        facts.append(
            {
                "name": entry.get("name"),
                "filename": entry.get("filename"),
                "line": entry.get("line"),
                "finite": payload.get("finite"),
                "satisfied": satisfied,
                "refuted": refuted,
            }
        )
    return facts


def slim_hit(hit: dict[str, object]) -> dict[str, object]:
    return {
        "name": hit["name"],
        "filename": hit["filename"],
        "line": hit["line"],
        "finite": hit["finite"],
        "satisfied": sorted(hit["satisfied"]),
        "refuted": sorted(hit["refuted"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--etp-root",
        type=Path,
        default=Path("/tmp/etp-364-current"),
        help="path to a teorth/equational_theories checkout",
    )
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    full_entries_path = args.etp_root / "full_entries.json"
    entries = json.loads(full_entries_path.read_text(encoding="utf-8"))
    facts = facts_entries(entries)

    exact_combined_hits = [
        item
        for item in facts
        if item["satisfied"] == WINDOW_SAT and item["refuted"] == WINDOW_REF
    ]
    superset_combined_hits = [
        item
        for item in facts
        if WINDOW_SAT <= item["satisfied"] and WINDOW_REF <= item["refuted"]
    ]

    pairwise = {}
    for pair in PAIRWISE:
        antecedent, consequent = pair
        exact_hits = [
            item
            for item in facts
            if item["satisfied"] == {antecedent} and item["refuted"] == {consequent}
        ]
        superset_hits = [
            item
            for item in facts
            if antecedent in item["satisfied"] and consequent in item["refuted"]
        ]
        pairwise[f"E{antecedent}_not_E{consequent}"] = {
            "exact_hits": len(exact_hits),
            "superset_hits": len(superset_hits),
            "hits": [slim_hit(item) for item in superset_hits[:10]],
            "hits_truncated": len(superset_hits) > 10,
        }

    absent_pair_pass = all(
        pairwise[f"E{a}_not_E{b}"]["exact_hits"] == 0
        and pairwise[f"E{a}_not_E{b}"]["superset_hits"] == 0
        for a, b in ABSENT_PAIRWISE
    )

    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "full_entries_json": str(full_entries_path),
        "full_entries_count": len(entries),
        "facts_entries_count": len(facts),
        "combined_certificate": {
            "satisfied": sorted(WINDOW_SAT),
            "refuted": sorted(WINDOW_REF),
            "exact_hits": len(exact_combined_hits),
            "superset_hits": len(superset_combined_hits),
            "superset_examples": [slim_hit(item) for item in superset_combined_hits[:10]],
        },
        "pairwise": pairwise,
        "absent_pairwise_checked": [f"E{a}_not_E{b}" for a, b in ABSENT_PAIRWISE],
        "absent_pairwise_all_zero_exact_and_superset": absent_pair_pass,
    }

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
