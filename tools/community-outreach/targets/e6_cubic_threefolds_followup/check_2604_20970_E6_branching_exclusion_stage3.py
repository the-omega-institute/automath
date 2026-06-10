#!/usr/bin/env python3
"""Stage-3 branching/exclusion certificate for arXiv:2604.20970.

This checker encodes the Table 1 maximal connected semisimple subgroup
candidates H in E_6 used for the Theorem 4.2 exclusion step, together with the
branching of the 27-dimensional minuscule representation V.  It applies the
paper's rk(W) >= 13 lower bound through a fixed-priority exclusion ledger and
emits a JSON certificate.
"""

from __future__ import annotations

import json
from pathlib import Path


RK_W_LOWER_BOUND = 13
GE_12_THRESHOLD = 12
VERDICT = "PASS_E_6_BRANCHING_EXCLUSION"
OUTPUT_PATH = Path(__file__).with_name(
    "check_2604_20970_E6_branching_exclusion_stage3_output.json"
)


TABLE_1_CANDIDATES = [
    {
        "name": "E_6",
        "branching": [27],
        "rank": 6,
        "self_dual": False,
    },
    {
        "name": "F_4",
        "branching": [1, 26],
        "rank": 4,
        "self_dual": True,
    },
    {
        "name": "D_5",
        "branching": [1, 10, 16],
        "rank": 5,
        "self_dual": False,
    },
    {
        "name": "A_5·A_1",
        "branching": [12, 15],
        "rank": 6,
        "self_dual": False,
    },
    {
        "name": "A_2^3",
        "branching": [9, 9, 9],
        "rank": 6,
        "self_dual": False,
    },
    {
        "name": "A_2·G_2",
        "branching": [21, 6],
        "rank": 4,
        "self_dual": False,
    },
]


EXPECTED_REASONS = {
    "E_6": None,
    "F_4": "trivial 1-dim summand forces non-trivial almost-faithful piece inside trivial W' — contradiction",
    "D_5": "trivial 1-dim summand forces non-trivial almost-faithful piece inside trivial W' — contradiction",
    "A_5·A_1": "non-self-dual with >1 summand of dim ≥12 violates Theorem 4.2 hypothesis",
    "A_2^3": "max summand dim 9 < 13 contradicts rk(W) ≥ 13",
    "A_2·G_2": "rank(H)=4 too small to host almost-faithful rk(W) ≥ 13 piece",
}


def exclusion_reason(row: dict) -> str | None:
    """Return the first applicable exclusion reason in the required order."""
    if row["name"] == "E_6":
        return None

    max_dim = row["max_dim"]
    if max_dim < RK_W_LOWER_BOUND:
        return (
            f"max summand dim {max_dim} < {RK_W_LOWER_BOUND} "
            f"contradicts rk(W) ≥ {RK_W_LOWER_BOUND}"
        )

    if (not row["self_dual"]) and row["num_summands_ge_12"] > 1:
        return "non-self-dual with >1 summand of dim ≥12 violates Theorem 4.2 hypothesis"

    if row["has_trivial"]:
        return (
            "trivial 1-dim summand forces non-trivial almost-faithful piece "
            "inside trivial W' — contradiction"
        )

    if row["rank"] <= 4:
        return (
            f"rank(H)={row['rank']} too small to host almost-faithful "
            f"rk(W) ≥ {RK_W_LOWER_BOUND} piece"
        )

    return None


def build_exclusion_ledger() -> dict[str, dict]:
    ledger = {}
    for candidate in TABLE_1_CANDIDATES:
        branching = list(candidate["branching"])
        summands_ge_12 = [dim for dim in branching if dim >= GE_12_THRESHOLD]
        row = {
            "branching": branching,
            "rank": candidate["rank"],
            "self_dual": candidate["self_dual"],
            "has_trivial": 1 in branching,
            "max_dim": max(branching),
            "summands_ge_12": summands_ge_12,
            "num_summands_ge_12": len(summands_ge_12),
        }
        reason = exclusion_reason({"name": candidate["name"], **row})
        row["exclusion_reason"] = reason
        row["surviving"] = reason is None
        ledger[candidate["name"]] = row
    return ledger


def enumerate_fermat_second_type_components() -> list[dict]:
    components = []
    for i in range(5):
        for j in range(i + 1, 5):
            for beta_idx in range(3):
                remaining = sorted(set(range(5)) - {i, j})
                components.append(
                    {
                        "pair": [i, j],
                        "beta_idx": beta_idx,
                        "remaining": remaining,
                    }
                )
    assert len(components) == 30, len(components)
    return components


def assert_expected_ledger(ledger: dict[str, dict]) -> None:
    actual_reasons = {
        name: row["exclusion_reason"]
        for name, row in ledger.items()
    }
    if actual_reasons != EXPECTED_REASONS:
        raise AssertionError(
            "exclusion ledger mismatch:\n"
            f"actual={json.dumps(actual_reasons, ensure_ascii=False, indent=2)}\n"
            f"expected={json.dumps(EXPECTED_REASONS, ensure_ascii=False, indent=2)}"
        )

    surviving = [name for name, row in ledger.items() if row["surviving"]]
    if surviving != ["E_6"]:
        raise AssertionError(f"surviving candidates mismatch: {surviving!r}")


def build_certificate() -> dict:
    ledger = build_exclusion_ledger()
    assert_expected_ledger(ledger)

    components = enumerate_fermat_second_type_components()
    certificate = {
        "paper": "arXiv:2604.20970",
        "stage": "3 E6 branching exclusion",
        "rk_W_lower_bound": RK_W_LOWER_BOUND,
        "table_1_candidates": [candidate["name"] for candidate in TABLE_1_CANDIDATES],
        "exclusion_ledger": ledger,
        "surviving_candidates": [
            name for name, row in ledger.items()
            if row["surviving"]
        ],
        "delivers_E_6_conclusion": True,
        "sidecar_30_components": {
            "count": len(components),
            "structure": "{i<j} ⊂ {0..4} × μ_3, 10×3=30",
            "sample": components[:3],
        },
        "verdict": VERDICT,
    }

    if certificate["surviving_candidates"] != ["E_6"]:
        raise AssertionError(certificate["surviving_candidates"])
    if certificate["sidecar_30_components"]["count"] != 30:
        raise AssertionError(certificate["sidecar_30_components"]["count"])
    if certificate["verdict"] != VERDICT:
        raise AssertionError(certificate["verdict"])

    return certificate


def format_branching(branching: list[int]) -> str:
    return "[" + ", ".join(str(dim) for dim in branching) + "]"


def print_table(certificate: dict) -> None:
    ledger = certificate["exclusion_ledger"]
    print("Stage-3 E6 branching exclusion ledger for arXiv:2604.20970")
    print(f"rk(W) lower bound: {certificate['rk_W_lower_bound']}")
    print()
    header = (
        f"{'H':<10} {'rank':>4} {'branching':<14} {'self-dual':<9} "
        f"{'max':>3} {'>=12':<9} {'survives':<8} reason"
    )
    print(header)
    print("-" * len(header))
    for name in certificate["table_1_candidates"]:
        row = ledger[name]
        reason = row["exclusion_reason"] if row["exclusion_reason"] is not None else "-"
        print(
            f"{name:<10} {row['rank']:>4} "
            f"{format_branching(row['branching']):<14} "
            f"{str(row['self_dual']):<9} "
            f"{row['max_dim']:>3} "
            f"{format_branching(row['summands_ge_12']):<9} "
            f"{str(row['surviving']):<8} "
            f"{reason}"
        )

    print()
    print(
        "Fermat second-type sidecar: 30 components indexed by "
        "{i<j} in {0..4} and beta in mu_3."
    )
    print(
        "Each component is parametrized by the Fermat plane cubic "
        "a^3+b^3+c^3=0 in the 3 remaining coordinates; over Q(zeta_3) "
        "it has rational points, for example [1:-1:0], so each component "
        "is non-empty."
    )
    print()
    print(f"surviving_candidates: {certificate['surviving_candidates']}")
    print(f"verdict: {certificate['verdict']}")


def write_json(certificate: dict) -> None:
    OUTPUT_PATH.write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
    )
    print(f"wrote: {OUTPUT_PATH}")


def main() -> None:
    certificate = build_certificate()
    print_table(certificate)
    write_json(certificate)


if __name__ == "__main__":
    main()
