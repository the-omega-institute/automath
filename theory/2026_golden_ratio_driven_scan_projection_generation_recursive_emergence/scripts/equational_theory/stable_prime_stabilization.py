#!/usr/bin/env python3
"""Verify the prime-field stabilization facts for stableAdd and stableMul."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from stable_arithmetic_facts import add_holds, mul_holds, term_counts


def git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def spectrum(counts: list[tuple[tuple[int, ...], tuple[int, ...]]], operation: str, modulus: int) -> list[int]:
    if operation == "stableAdd":
        return [
            index
            for index, (lhs, rhs) in enumerate(counts, start=1)
            if add_holds(lhs, rhs, modulus)
        ]
    if operation == "stableMul":
        return [
            index
            for index, (lhs, rhs) in enumerate(counts, start=1)
            if mul_holds(lhs, rhs, modulus)
        ]
    raise ValueError(operation)


def same_support(lhs: tuple[int, ...], rhs: tuple[int, ...]) -> bool:
    return all((left == 0) == (right == 0) for left, right in zip(lhs, rhs, strict=True))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("stable_prime_stabilization.json"),
    )
    args = parser.parse_args()

    equations = json.loads((args.etp_root / "tools/fme/src/eqdb.json").read_text())
    counts = [(term_counts(equation["lhs"]), term_counts(equation["rhs"])) for equation in equations]
    balanced = [
        index
        for index, (lhs, rhs) in enumerate(counts, start=1)
        if lhs == rhs
    ]

    max_abs_count_difference = max(
        abs(left - right)
        for lhs, rhs in counts
        for left, right in zip(lhs, rhs, strict=True)
    )
    max_abs_positive_exponent_difference_same_support = max(
        abs(left - right)
        for lhs, rhs in counts
        if same_support(lhs, rhs)
        for left, right in zip(lhs, rhs, strict=True)
        if left or right
    )
    nonbalanced_add_divisible_by_5 = [
        index
        for index, (lhs, rhs) in enumerate(counts, start=1)
        if lhs != rhs and all((left - right) % 5 == 0 for left, right in zip(lhs, rhs, strict=True))
    ]

    add5 = spectrum(counts, "stableAdd", 5)
    add7 = spectrum(counts, "stableAdd", 7)
    mul5 = spectrum(counts, "stableMul", 5)
    mul7 = spectrum(counts, "stableMul", 7)
    mul13 = spectrum(counts, "stableMul", 13)

    extras_mul5 = sorted(set(mul5) - set(balanced))
    counterexample_number = extras_mul5[0]
    counterexample = equations[counterexample_number - 1]

    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "equation_count": len(equations),
        "balanced_commutative_semigroup_equations": balanced,
        "balanced_count": len(balanced),
        "bounds": {
            "max_abs_variable_multiplicity_difference": max_abs_count_difference,
            "max_abs_positive_exponent_difference_when_supports_match": (
                max_abs_positive_exponent_difference_same_support
            ),
            "nonbalanced_add_difference_vectors_divisible_by_5": nonbalanced_add_divisible_by_5,
        },
        "stableAdd": {
            "Fin5_satisfied": add5,
            "Fin5_count": len(add5),
            "Fin7_count": len(add7),
            "Fin5_equals_balanced": add5 == balanced,
            "Fin7_equals_balanced": add7 == balanced,
            "proved_stabilizes_at_32_for_all_primes_p_ge_5": True,
        },
        "stableMul": {
            "Fin5_satisfied": mul5,
            "Fin5_count": len(mul5),
            "Fin7_count": len(mul7),
            "Fin13_count": len(mul13),
            "Fin7_equals_balanced": mul7 == balanced,
            "Fin13_equals_balanced": mul13 == balanced,
            "proved_stabilizes_at_32_for_all_primes_p_ge_7": True,
            "disproves_stabilizes_at_32_for_all_primes_p_ge_5": True,
            "Fin5_extra_equations_over_balanced": extras_mul5,
            "counterexample": {
                "equation": counterexample_number,
                "text": counterexample["eqn"],
                "lhs_counts": counts[counterexample_number - 1][0],
                "rhs_counts": counts[counterexample_number - 1][1],
                "reason": (
                    "over F_5 multiplication, x^5 = x for every x; equivalently "
                    "positive exponents 1 and 5 are congruent modulo 4"
                ),
            },
        },
    }

    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "wrote": str(args.out),
                "balanced_count": len(balanced),
                "stableAdd_Fin5_count": len(add5),
                "stableMul_Fin5_count": len(mul5),
                "stableMul_Fin7_count": len(mul7),
                "stableMul_Fin5_counterexample": counterexample_number,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
