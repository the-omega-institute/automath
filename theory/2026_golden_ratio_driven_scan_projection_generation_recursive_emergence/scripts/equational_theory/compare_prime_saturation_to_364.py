#!/usr/bin/env python3
"""Compare the old <=2-variable prime-field saturation claim with _364 data.

The old Finding 1 reported 608,948 separated ordered pairs among the 810 ETP
laws using at most two variables.  This script recomputes that bitset directly
from the current ETP eqdb.json for the linear magma operation

    x ◇ y = a*x + b*y

over prime fields p <= 31, then checks overlap with the _364
Z/144Z-new-vs-prime-baseline witness list.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


VARS = ("x", "y", "z", "w", "u", "v")
VAR_INDEX = {name: index for index, name in enumerate(VARS)}
SCAN_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def used_variable_count(equation: dict[str, object]) -> int:
    tokens = equation["lhs"] + equation["rhs"]
    return len({token for token in tokens if token != "+"})


def term_coeff_vector(tokens: list[str], p: int, a: int, b: int) -> tuple[int, ...]:
    stack: list[list[int]] = []
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            stack.append([(a * left[i] + b * right[i]) % p for i in range(len(VARS))])
        else:
            vector = [0] * len(VARS)
            vector[VAR_INDEX[token]] = 1
            stack.append(vector)
    if len(stack) != 1:
        raise ValueError(f"bad RPN term {tokens!r}")
    return tuple(stack[0])


def anti_pairs_from_patterns(patterns: set[int], equation_count: int) -> int:
    all_equations = (1 << equation_count) - 1
    anti = 0
    for satisfied in patterns:
        refuted = all_equations ^ satisfied
        bits = satisfied
        while bits:
            low_bit = bits & -bits
            index = low_bit.bit_length() - 1
            bits -= low_bit
            anti |= refuted << (index * equation_count)
    return anti


def local_to_global_bits(local_bits: int, selected_numbers: list[int], global_count: int) -> int:
    global_bits = 0
    local_count = len(selected_numbers)
    while local_bits:
        low_bit = local_bits & -local_bits
        position = low_bit.bit_length() - 1
        local_bits -= low_bit
        antecedent = selected_numbers[position // local_count]
        consequent = selected_numbers[position % local_count]
        global_bits |= 1 << ((antecedent - 1) * global_count + consequent - 1)
    return global_bits


def recompute_finding1(etp_root: Path) -> tuple[int, list[dict[str, int]], list[int], int]:
    equations = json.loads((etp_root / "tools/fme/src/eqdb.json").read_text(encoding="utf-8"))
    selected = [
        (index, equation)
        for index, equation in enumerate(equations, start=1)
        if used_variable_count(equation) <= 2
    ]
    selected_numbers = [index for index, _ in selected]

    cumulative = 0
    rows = []
    for p in SCAN_PRIMES:
        patterns: set[int] = set()
        for a in range(p):
            for b in range(p):
                satisfied = 0
                for local_index, (_, equation) in enumerate(selected):
                    lhs = term_coeff_vector(equation["lhs"], p, a, b)
                    rhs = term_coeff_vector(equation["rhs"], p, a, b)
                    if lhs == rhs:
                        satisfied |= 1 << local_index
                patterns.add(satisfied)
        anti = anti_pairs_from_patterns(patterns, len(selected))
        new = anti & ~cumulative
        cumulative |= anti
        rows.append(
            {
                "p": p,
                "patterns": len(patterns),
                "new_anti_implications": new.bit_count(),
                "cumulative_anti_implications": cumulative.bit_count(),
            }
        )

    global_bits = local_to_global_bits(cumulative, selected_numbers, len(equations))
    return global_bits, rows, selected_numbers, len(equations)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--z144",
        type=Path,
        default=Path(__file__).parents[1] / "teorth_equational_theories_364" / "z144_anti_implications.json",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("prime_saturation_vs_364.json"),
    )
    args = parser.parse_args()

    finding_bits, rows, selected_numbers, equation_count = recompute_finding1(args.etp_root)
    z144 = json.loads(args.z144.read_text(encoding="utf-8"))
    z144_witnesses = z144["z144"]["new_vs_prime_fields_le_199_plus_z8_witnesses"]
    z144_new_bits = 0
    for item in z144_witnesses:
        antecedent = int(item["satisfies"])
        consequent = int(item["refutes"])
        z144_new_bits |= 1 << ((antecedent - 1) * equation_count + consequent - 1)

    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "equation_count": equation_count,
        "finding1_scope": {
            "description": "ETP equations using at most two variables, prime-field linear magmas p <= 31",
            "equation_count": len(selected_numbers),
            "selected_equation_numbers_first_20": selected_numbers[:20],
            "prime_scan": rows,
            "separated_pairs": finding_bits.bit_count(),
        },
        "z144_artifact": {
            "path": str(args.z144),
            "etp_head": z144.get("etp_head"),
            "new_vs_prime_fields_le_199_plus_z8": z144["z144"]["new_vs_prime_fields_le_199_plus_z8"],
            "witnesses_in_artifact": len(z144_witnesses),
        },
        "comparison": {
            "z144_new_overlap_with_finding1_pairs": (z144_new_bits & finding_bits).bit_count(),
            "finding1_subset_of_364_prime_field_baseline_by_prime_range_argument": True,
            "reason": (
                "Finding 1 uses a subset of equations and primes p<=31. The _364 baseline is the "
                "all-4694-equation prime-field union for p<=199, so every Finding 1 witness pair is "
                "also a _364 baseline prime-field witness pair. The Z/144 witness list is defined "
                "as new after removing that prime-field baseline plus Z/8Z."
            ),
            "finding1_is_redundant_as_anti_implication_data": True,
        },
    }

    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("Prime saturation comparison complete")
    print(f"  <=2-variable equations: {len(selected_numbers)}")
    print(f"  Finding 1 recomputed separated pairs: {finding_bits.bit_count()}")
    print(f"  Z/144 new-vs-baseline witnesses: {len(z144_witnesses)}")
    print(f"  overlap: {(z144_new_bits & finding_bits).bit_count()}")
    print(f"  output: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
