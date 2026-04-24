#!/usr/bin/env python3
"""Verify the ETP equations true in all abelian groups.

In an abelian group with operation written as x◇y = x+y, an ETP term evaluates
to the sum of its variables with natural-number multiplicities.  Thus an
equation is an identity of all abelian groups iff its left and right
multiplicity vectors are exactly equal.  This script checks the resulting
32-equation set against the claimed list and compares Z/4Z and Z/6Z addition
spectra with that set.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


EXPECTED_BALANCED_SET = [
    1,
    43,
    4283,
    4290,
    4320,
    4358,
    4362,
    4364,
    4369,
    4380,
    4396,
    4398,
    4405,
    4433,
    4435,
    4442,
    4473,
    4480,
    4482,
    4512,
    4515,
    4525,
    4531,
    4541,
    4544,
    4598,
    4605,
    4635,
    4673,
    4677,
    4679,
    4684,
]
VARS = ("x", "y", "z", "w", "u", "v")
VAR_INDEX = {name: index for index, name in enumerate(VARS)}


def git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def term_counts(tokens: list[str]) -> tuple[int, ...]:
    counts = [0] * len(VARS)
    for token in tokens:
        if token != "+":
            counts[VAR_INDEX[token]] += 1
    return tuple(counts)


def add_spectrum_mod(
    counts: list[tuple[tuple[int, ...], tuple[int, ...]]], modulus: int
) -> list[int]:
    return [
        index
        for index, (lhs, rhs) in enumerate(counts, start=1)
        if all((left - right) % modulus == 0 for left, right in zip(lhs, rhs, strict=True))
    ]


def first_witness_assignment(lhs: tuple[int, ...], rhs: tuple[int, ...]) -> dict[str, int]:
    for index, (left, right) in enumerate(zip(lhs, rhs, strict=True)):
        if left != right:
            return {VARS[index]: 1}
    raise ValueError("balanced vectors have no separating assignment")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("abelian_group_identity_check.json"),
    )
    args = parser.parse_args()

    equations = json.loads((args.etp_root / "tools/fme/src/eqdb.json").read_text())
    counts = [(term_counts(equation["lhs"]), term_counts(equation["rhs"])) for equation in equations]
    balanced = [index for index, (lhs, rhs) in enumerate(counts, start=1) if lhs == rhs]
    expected = EXPECTED_BALANCED_SET
    balanced_set = set(balanced)

    finite_cyclic = {}
    for modulus in (4, 6):
        spectrum = add_spectrum_mod(counts, modulus)
        spectrum_set = set(spectrum)
        extras = sorted(spectrum_set - balanced_set)
        missing = sorted(balanced_set - spectrum_set)
        finite_cyclic[f"Fin{modulus}"] = {
            "satisfied": spectrum,
            "satisfied_count": len(spectrum),
            "equals_abelian_group_identity_set": spectrum == balanced,
            "extra_over_abelian_group_identities": extras,
            "missing_from_abelian_group_identities": missing,
            "extra_count": len(extras),
            "missing_count": len(missing),
        }

    nonbalanced_witness_samples = []
    for index, (lhs, rhs) in enumerate(counts, start=1):
        if lhs == rhs:
            continue
        nonbalanced_witness_samples.append(
            {
                "equation": index,
                "lhs_counts": lhs,
                "rhs_counts": rhs,
                "separating_assignment_in_Z": first_witness_assignment(lhs, rhs),
            }
        )
        if len(nonbalanced_witness_samples) == 10:
            break

    max_abs_count_difference = max(
        abs(left - right)
        for lhs, rhs in counts
        for left, right in zip(lhs, rhs, strict=True)
    )

    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "equation_count": len(equations),
        "claimed_32_equation_set": expected,
        "computed_balanced_equation_set": balanced,
        "computed_balanced_count": len(balanced),
        "claimed_set_matches_computed_balanced_set": balanced == expected,
        "proof": {
            "criterion": (
                "An equation is true in every abelian group iff the variable "
                "multiplicity vectors on the two sides are exactly equal."
            ),
            "if_equal": (
                "Associativity and commutativity rewrite both terms to the same "
                "formal sum of variables."
            ),
            "if_not_equal": (
                "A variable with unequal multiplicity separates the equation in "
                "the infinite cyclic group Z by assigning that variable to 1 and "
                "all others to 0."
            ),
            "witness_samples_for_nonbalanced_equations": nonbalanced_witness_samples,
        },
        "finite_cyclic_addition_checks": finite_cyclic,
        "bounds": {
            "max_abs_variable_multiplicity_difference": max_abs_count_difference,
            "consequence": (
                "No cyclic group Z/nZ with n greater than this bound can satisfy "
                "a nonbalanced ETP equation by torsion alone."
            ),
        },
    }

    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "wrote": str(args.out),
                "etp_head": result["etp_head"],
                "balanced_count": len(balanced),
                "claimed_matches_computed": balanced == expected,
                "Fin4_count": finite_cyclic["Fin4"]["satisfied_count"],
                "Fin4_extra_count": finite_cyclic["Fin4"]["extra_count"],
                "Fin6_count": finite_cyclic["Fin6"]["satisfied_count"],
                "Fin6_extra_count": finite_cyclic["Fin6"]["extra_count"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
