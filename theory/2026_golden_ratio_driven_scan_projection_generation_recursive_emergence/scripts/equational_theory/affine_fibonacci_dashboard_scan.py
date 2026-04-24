#!/usr/bin/env python3
"""Scan Fibonacci affine-linear magmas against ETP dashboard unknowns.

For fixed n,a,b, the magma operation on Z/nZ is

    x ◇ y = a*x + b*y.

Every ETP term is therefore a linear form in the variables.  An equation holds
on all assignments in Z/nZ iff the left and right coefficient vectors agree
modulo n.  This script enumerates all (n,a,b) with n in the requested
Fibonacci-modulus list and tests whether any resulting Facts spectrum contains
an anti-implication appearing in home_page/fme/unknowns.json.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import subprocess
from pathlib import Path


FIBONACCI_MODULI = [2, 3, 5, 8, 13, 21, 34, 55, 89, 144]
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


def load_dashboard_pairs(etp_root: Path, equation_count: int) -> list[tuple[int, int]]:
    raw_unknowns = json.loads((etp_root / "home_page/fme/unknowns.json").read_text())
    pairs: set[tuple[int, int]] = set()
    for item in raw_unknowns:
        lhs = equation_id(item.get("lhs"), equation_count)
        rhs = equation_id(item.get("rhs"), equation_count)
        if lhs is not None and rhs is not None:
            pairs.add((lhs, rhs))
    return sorted(pairs)


def term_coeff_vector(tokens: list[str], modulus: int, a: int, b: int) -> tuple[int, ...]:
    stack: list[tuple[int, ...]] = []
    zero = (0,) * len(VARS)
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            stack.append(
                tuple((a * left[index] + b * right[index]) % modulus for index in range(len(VARS)))
            )
        else:
            coeffs = list(zero)
            coeffs[VAR_INDEX[token]] = 1
            stack.append(tuple(coeffs))
    if len(stack) != 1:
        raise ValueError(f"bad RPN term {tokens!r}")
    return stack[0]


def equation_holds(equation: dict[str, object], modulus: int, a: int, b: int) -> bool:
    lhs = equation["lhs"]
    rhs = equation["rhs"]
    if not isinstance(lhs, list) or not isinstance(rhs, list):
        raise TypeError("eqdb terms must be token lists")
    return term_coeff_vector(lhs, modulus, a, b) == term_coeff_vector(rhs, modulus, a, b)


def eval_term(tokens: list[str], assignment: dict[str, int], modulus: int, a: int, b: int) -> int:
    stack: list[int] = []
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            stack.append((a * left + b * right) % modulus)
        else:
            stack.append(assignment[token] % modulus)
    if len(stack) != 1:
        raise ValueError(f"bad RPN term {tokens!r}")
    return stack[0]


def brute_equation_holds(equation: dict[str, object], modulus: int, a: int, b: int) -> bool:
    lhs = equation["lhs"]
    rhs = equation["rhs"]
    if not isinstance(lhs, list) or not isinstance(rhs, list):
        raise TypeError("eqdb terms must be token lists")
    used_vars = sorted({token for token in lhs + rhs if token != "+"}, key=VAR_INDEX.__getitem__)
    for values in itertools.product(range(modulus), repeat=len(used_vars)):
        assignment = dict(zip(used_vars, values, strict=True))
        if eval_term(lhs, assignment, modulus, a, b) != eval_term(rhs, assignment, modulus, a, b):
            return False
    return True


def run_brute_cross_checks(
    equations: list[dict[str, object]], needed_equations: list[int]
) -> list[dict[str, object]]:
    checks = []
    for modulus in (2, 3):
        checked = 0
        for a in range(modulus):
            for b in range(modulus):
                for equation_number in needed_equations:
                    equation = equations[equation_number - 1]
                    fast = equation_holds(equation, modulus, a, b)
                    slow = brute_equation_holds(equation, modulus, a, b)
                    if fast != slow:
                        raise AssertionError(
                            f"coefficient criterion mismatch at n={modulus}, "
                            f"a={a}, b={b}, E{equation_number}"
                        )
                    checked += 1
        checks.append(
            {
                "modulus": modulus,
                "parameter_pairs": modulus * modulus,
                "unique_dashboard_equations_checked": len(needed_equations),
                "total_equation_parameter_checks": checked,
                "result": "coefficient criterion matched exhaustive assignment evaluation",
            }
        )
    return checks


def pair_to_dict(pair: tuple[int, int]) -> dict[str, int]:
    return {"satisfies": pair[0], "refutes": pair[1]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("affine_fibonacci_dashboard_scan.json"),
    )
    parser.add_argument("--brute-check-small", action="store_true")
    args = parser.parse_args()

    equations = json.loads((args.etp_root / "tools/fme/src/eqdb.json").read_text())
    equation_count = len(equations)
    dashboard_pairs = load_dashboard_pairs(args.etp_root, equation_count)
    needed_equations = sorted({equation for pair in dashboard_pairs for equation in pair})

    brute_checks = run_brute_cross_checks(equations, needed_equations) if args.brute_check_small else []

    resolved_pairs: dict[tuple[int, int], dict[str, int]] = {}
    spectra_with_hits = 0
    per_modulus: list[dict[str, object]] = []
    sample_hit_spectra: list[dict[str, object]] = []
    max_hits_in_one_spectrum = 0

    for modulus in FIBONACCI_MODULI:
        modulus_spectra = 0
        modulus_spectra_with_hits = 0
        modulus_resolved_pairs: set[tuple[int, int]] = set()
        for a in range(modulus):
            for b in range(modulus):
                statuses = {
                    equation_number: equation_holds(equations[equation_number - 1], modulus, a, b)
                    for equation_number in needed_equations
                }
                hits = [
                    pair
                    for pair in dashboard_pairs
                    if statuses[pair[0]] and not statuses[pair[1]]
                ]
                modulus_spectra += 1
                if not hits:
                    continue

                spectra_with_hits += 1
                modulus_spectra_with_hits += 1
                max_hits_in_one_spectrum = max(max_hits_in_one_spectrum, len(hits))
                modulus_resolved_pairs.update(hits)
                for pair in hits:
                    resolved_pairs.setdefault(pair, {"modulus": modulus, "a": a, "b": b})
                if len(sample_hit_spectra) < 50:
                    sample_hit_spectra.append(
                        {
                            "modulus": modulus,
                            "a": a,
                            "b": b,
                            "dashboard_hit_count": len(hits),
                            "dashboard_hits": [pair_to_dict(pair) for pair in hits[:50]],
                        }
                    )

        per_modulus.append(
            {
                "modulus": modulus,
                "parameter_pairs": modulus_spectra,
                "spectra_with_dashboard_hits": modulus_spectra_with_hits,
                "resolved_dashboard_pair_count": len(modulus_resolved_pairs),
                "resolved_dashboard_pairs": [pair_to_dict(pair) for pair in sorted(modulus_resolved_pairs)],
            }
        )

    resolved_pairs_sorted = sorted(resolved_pairs)
    result = {
        "etp_root": str(args.etp_root),
        "etp_head": git_head(args.etp_root),
        "equation_count": equation_count,
        "moduli": FIBONACCI_MODULI,
        "parameter_triples_checked": sum(modulus * modulus for modulus in FIBONACCI_MODULI),
        "dashboard_unknowns": {
            "ordered_pair_count": len(dashboard_pairs),
            "unique_equations_in_unknown_pairs": len(needed_equations),
        },
        "criterion": (
            "For x◇y = ax+by over Z/nZ, each term is a linear form; an equation "
            "holds iff the two coefficient vectors agree modulo n."
        ),
        "brute_force_cross_checks": brute_checks,
        "result": {
            "resolved_dashboard_pair_count": len(resolved_pairs_sorted),
            "spectra_with_dashboard_hits": spectra_with_hits,
            "max_dashboard_hits_in_one_spectrum": max_hits_in_one_spectrum,
            "resolved_dashboard_pairs": [
                {
                    **pair_to_dict(pair),
                    "witness": resolved_pairs[pair],
                }
                for pair in resolved_pairs_sorted
            ],
            "sample_hit_spectra": sample_hit_spectra,
            "disjoint_from_dashboard_unknowns": len(resolved_pairs_sorted) == 0,
        },
        "per_modulus": per_modulus,
    }

    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "wrote": str(args.out),
                "etp_head": result["etp_head"],
                "parameter_triples_checked": result["parameter_triples_checked"],
                "dashboard_unknowns": len(dashboard_pairs),
                "resolved_dashboard_pairs": len(resolved_pairs_sorted),
                "spectra_with_dashboard_hits": spectra_with_hits,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
