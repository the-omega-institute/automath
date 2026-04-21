#!/usr/bin/env python3
"""Generate ETP Facts spectra for Fibonacci stableAdd/stableMul prime phases.

The requested operations are the transported stable arithmetic operations on
Fin p for Fibonacci prime moduli p in {2, 3, 5, 13, 89}:

* stableAdd: x ◇ y = x + y mod p
* stableMul: x ◇ y = x * y mod p

The 4,694 ETP equations in tools/fme/src/eqdb.json have at most six leaves.
For addition, a law holds iff the two sides have the same variable
multiplicity vector modulo p.  For multiplication over the prime field F_p, a
law holds iff the two monomial functions agree: the supports match and the
positive exponents are congruent modulo p-1.  These criteria avoid the
impossible brute-force pass over 89^6 assignments.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import subprocess
from pathlib import Path


MODULI = [2, 3, 5, 13, 89]
LEAN_MODULI = {2, 3, 5}
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


def equation_number(label: str) -> int:
    match = re.fullmatch(r"Equation(\d+)", label)
    if match is None:
        raise ValueError(f"unexpected equation label {label!r}")
    return int(match.group(1))


def term_counts(tokens: list[str]) -> tuple[int, ...]:
    counts = [0] * len(VARS)
    for token in tokens:
        if token == "+":
            continue
        counts[VAR_INDEX[token]] += 1
    return tuple(counts)


def add_holds(lhs: tuple[int, ...], rhs: tuple[int, ...], modulus: int) -> bool:
    return all((left - right) % modulus == 0 for left, right in zip(lhs, rhs, strict=True))


def mul_holds(lhs: tuple[int, ...], rhs: tuple[int, ...], modulus: int) -> bool:
    period = modulus - 1
    for left, right in zip(lhs, rhs, strict=True):
        if (left == 0) != (right == 0):
            return False
        if left and (left - right) % period != 0:
            return False
    return True


def eval_term(tokens: list[str], assignment: dict[str, int], modulus: int, op: str) -> int:
    stack: list[int] = []
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            if op == "stableAdd":
                stack.append((left + right) % modulus)
            elif op == "stableMul":
                stack.append((left * right) % modulus)
            else:
                raise ValueError(op)
        else:
            stack.append(assignment[token] % modulus)
    if len(stack) != 1:
        raise ValueError(f"bad RPN term {tokens!r}")
    return stack[0]


def brute_holds(equation: dict[str, object], modulus: int, op: str) -> bool:
    lhs = equation["lhs"]
    rhs = equation["rhs"]
    if not isinstance(lhs, list) or not isinstance(rhs, list):
        raise TypeError("eqdb term must be a list")
    used_vars = sorted({token for token in lhs + rhs if token != "+"}, key=VAR_INDEX.__getitem__)
    for values in itertools.product(range(modulus), repeat=len(used_vars)):
        assignment = dict(zip(used_vars, values, strict=True))
        if eval_term(lhs, assignment, modulus, op) != eval_term(rhs, assignment, modulus, op):
            return False
    return True


def facts_entries(entries: list[dict[str, object]]) -> list[tuple[set[int], set[int]]]:
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
        facts.append((satisfied, refuted))
    return facts


def anti_pairs_bitset(satisfied: list[int], refuted: list[int], equation_count: int) -> int:
    refuted_mask = 0
    for consequent in refuted:
        refuted_mask |= 1 << (consequent - 1)
    bits = 0
    for antecedent in satisfied:
        bits |= refuted_mask << ((antecedent - 1) * equation_count)
    return bits


def existing_pairwise_coverage(facts: list[tuple[set[int], set[int]]], equation_count: int) -> int:
    bits = 0
    for satisfied, refuted in facts:
        bits |= anti_pairs_bitset(sorted(satisfied), sorted(refuted), equation_count)
    return bits


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_snippet(name: str, op: str, modulus: int, satisfied: list[int], refuted: list[int]) -> str:
    lean_op = "x + y" if op == "stableAdd" else "x * y"
    return "\n".join(
        [
            f"def {name} : Magma (Fin {modulus}) where",
            f"  op := memoFinOp fun x y => {lean_op}",
            "",
            "@[equational_result]",
            f"theorem {name}_facts :",
            f"    ∃ (G : Type) (_ : Magma G) (_ : Finite G), Facts G {lean_list(satisfied)} {lean_list(refuted)} := by",
            f"  exact ⟨Fin {modulus}, {name}, Finite.of_fintype _, by decideFin!⟩",
            "",
        ]
    )


def build_artifact(etp_root: Path, brute_check_small: bool) -> dict[str, object]:
    equations = json.loads((etp_root / "tools/fme/src/eqdb.json").read_text(encoding="utf-8"))
    if len(equations) != 4694:
        raise ValueError(f"expected 4694 ETP equations, found {len(equations)}")

    counts = []
    for equation in equations:
        lhs = term_counts(equation["lhs"])
        rhs = term_counts(equation["rhs"])
        counts.append((lhs, rhs))

    full_entries_path = etp_root / "full_entries.json"
    full_entries = json.loads(full_entries_path.read_text(encoding="utf-8"))
    existing_facts = facts_entries(full_entries)
    existing_pair_bits = existing_pairwise_coverage(existing_facts, len(equations))

    spectra = []
    all_generated_pairs = 0
    for modulus in MODULI:
        for op in ("stableAdd", "stableMul"):
            if op == "stableAdd":
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
            refuted = [index for index in range(1, len(equations) + 1) if index not in satisfied_set]
            refuted_set = set(refuted)
            pair_bits = anti_pairs_bitset(satisfied, refuted, len(equations))
            all_generated_pairs |= pair_bits

            exact_hits = sum(
                1
                for old_satisfied, old_refuted in existing_facts
                if old_satisfied == satisfied_set and old_refuted == refuted_set
            )
            superset_hits = sum(
                1
                for old_satisfied, old_refuted in existing_facts
                if satisfied_set <= old_satisfied and refuted_set <= old_refuted
            )

            name = f"OmegaStable{op.removeprefix('stable')}_Fin{modulus}"
            spectra.append(
                {
                    "name": name,
                    "operation": op,
                    "modulus": modulus,
                    "satisfied": satisfied,
                    "refuted": refuted,
                    "satisfied_count": len(satisfied),
                    "refuted_count": len(refuted),
                    "facts": f"Facts G {lean_list(satisfied)} {lean_list(refuted)}",
                    "lean": lean_snippet(name, op, modulus, satisfied, refuted),
                    "anti_implications": pair_bits.bit_count(),
                    "anti_implications_already_covered_by_full_entries": (pair_bits & existing_pair_bits).bit_count(),
                    "anti_implications_not_covered_by_full_entries": (pair_bits & ~existing_pair_bits).bit_count(),
                    "full_facts_exact_hits": exact_hits,
                    "full_facts_superset_hits": superset_hits,
                }
            )

    brute_checks = []
    if brute_check_small:
        for modulus in (2, 3):
            for op in ("stableAdd", "stableMul"):
                for index, equation in enumerate(equations, start=1):
                    lhs, rhs = counts[index - 1]
                    fast = add_holds(lhs, rhs, modulus) if op == "stableAdd" else mul_holds(lhs, rhs, modulus)
                    slow = brute_holds(equation, modulus, op)
                    if fast != slow:
                        raise AssertionError(f"criterion mismatch for {op} Fin {modulus} E{index}")
                brute_checks.append(
                    {
                        "operation": op,
                        "modulus": modulus,
                        "equations_checked": len(equations),
                        "result": "fast criterion matched exhaustive assignment check",
                    }
                )

    return {
        "etp_root": str(etp_root),
        "etp_head": git_head(etp_root),
        "equation_count": len(equations),
        "full_entries_json": str(full_entries_path),
        "full_entries_count": len(full_entries),
        "facts_entries_count": len(existing_facts),
        "criteria": {
            "stableAdd": "lhs and rhs variable multiplicity vectors agree modulo p",
            "stableMul": "over prime p, lhs and rhs monomial functions have equal support and equal positive exponents modulo p-1",
        },
        "brute_force_cross_checks": brute_checks,
        "spectra": spectra,
        "generated_union": {
            "anti_implications": all_generated_pairs.bit_count(),
            "already_covered_by_full_entries": (all_generated_pairs & existing_pair_bits).bit_count(),
            "not_covered_by_full_entries": (all_generated_pairs & ~existing_pair_bits).bit_count(),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etp-root", type=Path, default=Path("/tmp/etp-364-current"))
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("stable_arithmetic_facts.json"),
    )
    parser.add_argument(
        "--lean-out",
        type=Path,
        default=Path(__file__).with_name("stable_arithmetic_facts.lean"),
    )
    parser.add_argument("--no-brute-check-small", action="store_true")
    args = parser.parse_args()

    artifact = build_artifact(args.etp_root, brute_check_small=not args.no_brute_check_small)
    args.out.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.lean_out.write_text(
        "import Mathlib.Data.Finite.Prod\n"
        "import equational_theories.MemoFinOp\n"
        "import equational_theories.FactsSyntax\n"
        "import equational_theories.Equations.All\n"
        "import equational_theories.DecideBang\n"
        "import equational_theories.EquationalResult\n\n"
        "set_option linter.unusedVariables false\n"
        "set_option maxHeartbeats 800000\n\n"
        "namespace OmegaStableArithmeticFacts\n\n"
        + "\n".join(
            item["lean"] for item in artifact["spectra"] if item["modulus"] in LEAN_MODULI
        )
        + "\nend OmegaStableArithmeticFacts\n",
        encoding="utf-8",
    )

    print("Stable arithmetic Facts generation complete")
    print(f"  ETP equations: {artifact['equation_count']}")
    print(f"  ETP HEAD: {artifact['etp_head']}")
    for item in artifact["spectra"]:
        print(
            f"  {item['operation']} Fin {item['modulus']}: "
            f"{item['satisfied_count']} satisfied, {item['refuted_count']} refuted, "
            f"{item['anti_implications_not_covered_by_full_entries']} pairwise not covered"
        )
    union = artifact["generated_union"]
    print(
        "  generated union: "
        f"{union['anti_implications']} anti-implications, "
        f"{union['not_covered_by_full_entries']} not covered by full_entries Facts"
    )
    print(f"  JSON: {args.out}")
    print(f"  Lean snippets: {args.lean_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
