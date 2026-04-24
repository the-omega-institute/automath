#!/usr/bin/env python3
"""Intersect stableAdd/stableMul anti-implications with ETP dashboard unknowns.

This uses the same dashboard-unknown extraction convention as the `_364`
`z144_anti_implications.py` artifact: each item in
`home_page/fme/unknowns.json` contributes the ordered pair
`lhs -> not rhs` when both sides parse as `EquationN`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

from stable_arithmetic_facts import (
    MODULI,
    add_holds,
    anti_pairs_bitset,
    existing_pairwise_coverage,
    facts_entries,
    mul_holds,
    term_counts,
)


def git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def equation_id(name: str | None, equation_count: int) -> int | None:
    if name is None:
        return None
    match = re.fullmatch(r"Equation(\d+)", name)
    if match is None:
        return None
    number = int(match.group(1))
    if 1 <= number <= equation_count:
        return number
    return None


def pairs_from_bits(bits: int, equation_count: int) -> list[dict[str, int]]:
    pairs = []
    while bits:
        low_bit = bits & -bits
        position = low_bit.bit_length() - 1
        bits -= low_bit
        pairs.append(
            {
                "satisfies": position // equation_count + 1,
                "refutes": position % equation_count + 1,
            }
        )
    return pairs


def dashboard_unknown_bits(etp_root: Path, equation_count: int) -> int:
    raw_unknowns = json.loads((etp_root / "home_page/fme/unknowns.json").read_text())
    bits = 0
    for item in raw_unknowns:
        lhs = equation_id(item.get("lhs"), equation_count)
        rhs = equation_id(item.get("rhs"), equation_count)
        if lhs is not None and rhs is not None:
            bits |= 1 << ((lhs - 1) * equation_count + rhs - 1)
    return bits


def stable_pair_bits(etp_root: Path) -> tuple[int, int, list[dict[str, object]], int]:
    equations = json.loads((etp_root / "tools/fme/src/eqdb.json").read_text())
    equation_count = len(equations)
    counts = [(term_counts(equation["lhs"]), term_counts(equation["rhs"])) for equation in equations]

    full_entries = json.loads((etp_root / "full_entries.json").read_text())
    existing_pair_bits = existing_pairwise_coverage(facts_entries(full_entries), equation_count)

    generated = 0
    spectra = []
    for modulus in MODULI:
        for operation in ("stableAdd", "stableMul"):
            if operation == "stableAdd":
                satisfied = [
                    index
                    for index, (lhs, rhs) in enumerate(counts, start=1)
                    if add_holds(lhs, rhs, modulus)
                ]
            else:
                satisfied = [
                    index
                    for index, (lhs, rhs) in enumerate(counts, start=1)
                    if mul_holds(lhs, rhs, modulus)
                ]
            satisfied_set = set(satisfied)
            refuted = [index for index in range(1, equation_count + 1) if index not in satisfied_set]
            pair_bits = anti_pairs_bitset(satisfied, refuted, equation_count)
            generated |= pair_bits
            spectra.append(
                {
                    "operation": operation,
                    "modulus": modulus,
                    "satisfied_count": len(satisfied),
                    "refuted_count": len(refuted),
                    "anti_implications": pair_bits.bit_count(),
                    "anti_implications_not_covered_by_full_entries": (
                        pair_bits & ~existing_pair_bits
                    ).bit_count(),
                }
            )

    return generated, existing_pair_bits, spectra, equation_count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("stable_dashboard_unknowns.json"),
    )
    args = parser.parse_args()

    generated, existing_pair_bits, spectra, equation_count = stable_pair_bits(args.etp_root)
    not_covered = generated & ~existing_pair_bits
    dashboard_unknowns = dashboard_unknown_bits(args.etp_root, equation_count)
    all_intersection = generated & dashboard_unknowns
    not_covered_intersection = not_covered & dashboard_unknowns

    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "equation_count": equation_count,
        "spectra": spectra,
        "stable_union": {
            "anti_implications": generated.bit_count(),
            "already_covered_by_full_entries": (generated & existing_pair_bits).bit_count(),
            "not_covered_by_full_entries": not_covered.bit_count(),
        },
        "dashboard_unknowns": {
            "count": dashboard_unknowns.bit_count(),
            "stable_union_intersection_count": all_intersection.bit_count(),
            "stable_union_intersection_pairs": pairs_from_bits(all_intersection, equation_count),
            "stable_not_covered_intersection_count": not_covered_intersection.bit_count(),
            "stable_not_covered_intersection_pairs": pairs_from_bits(
                not_covered_intersection, equation_count
            ),
        },
    }

    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "wrote": str(args.out),
                "etp_head": result["etp_head"],
                "stable_not_covered_by_full_entries": result["stable_union"][
                    "not_covered_by_full_entries"
                ],
                "dashboard_unknowns": result["dashboard_unknowns"]["count"],
                "resolved_dashboard_unknowns": result["dashboard_unknowns"][
                    "stable_not_covered_intersection_count"
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
