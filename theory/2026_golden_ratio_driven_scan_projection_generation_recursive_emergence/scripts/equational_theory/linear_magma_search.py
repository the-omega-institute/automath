#!/usr/bin/env python3
"""Search linear magma anti-implications over prime fields.

The operation is x diamond y = a*x + b*y mod p.  Terms in this magma are
linear forms in the input variables, so the main search checks identities by
comparing coefficient vectors over GF(p).  A brute-force checker using
itertools.product is also included for sanity checks and counterexample
validation.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import itertools
import json
import re
import subprocess
import sys
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_PATH = SCRIPT_DIR / "linear_magma_results.json"
VAR_ORDER = ("x", "y", "z", "w", "u", "v")
BASELINE_PRIMES_LE_200 = [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
    101,
    103,
    107,
    109,
    113,
    127,
    131,
    137,
    139,
    149,
    151,
    157,
    163,
    167,
    173,
    179,
    181,
    191,
    193,
    197,
    199,
]


Term = tuple[Any, ...]


@dataclass(frozen=True)
class Equation:
    number: int
    text: str
    left: Term
    right: Term
    variables: tuple[str, ...]


class ParseError(ValueError):
    pass


class TermParser:
    def __init__(self, source: str) -> None:
        self.tokens = tokenize(source)
        self.pos = 0

    def parse(self) -> Term:
        term = self.parse_expr()
        if self.pos != len(self.tokens):
            raise ParseError(f"unexpected token {self.tokens[self.pos]!r}")
        return term

    def parse_expr(self) -> Term:
        left = self.parse_atom()
        while self.peek() == "D":
            self.pos += 1
            right = self.parse_atom()
            left = ("op", left, right)
        return left

    def parse_atom(self) -> Term:
        token = self.peek()
        if token is None:
            raise ParseError("unexpected end of term")
        if token in VAR_ORDER:
            self.pos += 1
            return ("var", token)
        if token == "(":
            self.pos += 1
            term = self.parse_expr()
            if self.peek() != ")":
                raise ParseError("missing closing parenthesis")
            self.pos += 1
            return term
        raise ParseError(f"unexpected token {token!r}")

    def peek(self) -> str | None:
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]


def tokenize(source: str) -> list[str]:
    normalized = normalize_operator(source)
    tokens: list[str] = []
    i = 0
    while i < len(normalized):
        char = normalized[i]
        if char.isspace():
            i += 1
            continue
        if char in "()":
            tokens.append(char)
            i += 1
            continue
        if char == "D":
            tokens.append("D")
            i += 1
            continue
        if char in VAR_ORDER:
            tokens.append(char)
            i += 1
            continue
        raise ParseError(f"cannot tokenize {char!r} in {source!r}")
    return tokens


def normalize_operator(source: str) -> str:
    return (
        source.replace("\u25c7", "D")
        .replace("\u22c4", "D")
        .replace("\u25ca", "D")
        .replace("<>", "D")
    )


def collect_variables(term: Term, seen: set[str]) -> None:
    if term[0] == "var":
        seen.add(term[1])
        return
    collect_variables(term[1], seen)
    collect_variables(term[2], seen)


def parse_term(source: str) -> Term:
    return TermParser(source).parse()


def parse_equation(number: int, text: str) -> Equation:
    cleaned = clean_equation_text(text)
    if "=" not in cleaned:
        raise ParseError("equation has no equals sign")
    left_text, right_text = cleaned.split("=", 1)
    left = parse_term(left_text.strip())
    right = parse_term(right_text.strip())
    seen: set[str] = set()
    collect_variables(left, seen)
    collect_variables(right, seen)
    variables = tuple(var for var in VAR_ORDER if var in seen)
    return Equation(number=number, text=cleaned, left=left, right=right, variables=variables)


def clean_equation_text(text: str) -> str:
    cleaned = text.strip().rstrip(",")
    cleaned = re.sub(r"\s+", " ", cleaned)
    if "," in cleaned and "=" in cleaned and cleaned.rfind(",", 0, cleaned.find("=")) != -1:
        cleaned = cleaned[cleaned.rfind(",", 0, cleaned.find("=")) + 1 :].strip()
    return cleaned


def parse_equations(raw: str) -> list[Equation]:
    equations: list[Equation] = []
    plain_number = 1
    for raw_line in raw.splitlines():
        line = raw_line.split("--", 1)[0].strip()
        if not line:
            continue

        lean_match = re.search(r"\bEquation(\d+)\s*:\s*(.*?)\s*:=", line)
        if lean_match:
            number = int(lean_match.group(1))
            candidate = lean_match.group(2)
        elif "=" in line and not line.startswith(("import ", "namespace ", "end ")):
            number = plain_number
            candidate = line
            plain_number += 1
        else:
            continue

        try:
            equations.append(parse_equation(number, candidate))
        except ParseError:
            continue

    if not equations:
        raise ParseError("no equations could be parsed")
    equations.sort(key=lambda equation: equation.number)
    return equations


def synthetic_equations() -> str:
    op = "\u25c7"
    return "\n".join(
        [
            "x = x",
            f"x {op} y = y {op} x",
            f"x {op} x = x",
            f"(x {op} y) {op} z = x {op} (y {op} z)",
            f"x {op} (y {op} z) = x {op} (z {op} y)",
            f"x {op} (x {op} y) = x {op} y",
            f"(x {op} y) {op} y = x {op} y",
            f"x {op} (y {op} x) = x",
            f"(x {op} y) {op} x = x",
            f"x {op} (y {op} z) = y {op} (x {op} z)",
            f"(x {op} y) {op} (z {op} w) = (x {op} z) {op} (y {op} w)",
            f"x {op} (y {op} z) = (x {op} y) {op} (x {op} z)",
            f"(x {op} y) {op} z = (x {op} z) {op} (y {op} z)",
        ]
    )


def run_gh_content(path: str) -> tuple[str | None, str | None]:
    command = [
        "gh",
        "api",
        f"repos/teorth/equational_theories/contents/{path}",
        "--jq",
        ".content",
    ]
    try:
        completed = subprocess.run(
            command,
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except FileNotFoundError as exc:
        return None, str(exc)
    except subprocess.TimeoutExpired as exc:
        return None, f"timed out after {exc.timeout} seconds"
    except subprocess.CalledProcessError as exc:
        stderr = (exc.stderr or "").strip()
        if stderr:
            return None, stderr
        return None, str(exc)

    try:
        decoded = base64.b64decode(completed.stdout).decode("utf-8")
    except Exception as exc:  # noqa: BLE001
        return None, f"base64 decode failed: {exc}"
    return decoded, None


def load_equations() -> tuple[list[Equation], dict[str, Any]]:
    attempts = []
    for path in (
        "data/equations.txt",
        "equational_theories/Equations.lean",
    ):
        raw, error = run_gh_content(path)
        attempts.append({"path": path, "ok": raw is not None, "error": error})
        if raw is None:
            continue
        try:
            equations = parse_equations(raw)
        except ParseError as exc:
            attempts[-1]["parse_error"] = str(exc)
            continue
        return equations, {
            "source": f"github:{path}",
            "synthetic_fallback": False,
            "attempts": attempts,
        }

    raw = synthetic_equations()
    equations = parse_equations(raw)
    return equations, {
        "source": "synthetic_standard_magma_laws",
        "synthetic_fallback": True,
        "attempts": attempts,
    }


def term_coefficients(term: Term, a: int, b: int, p: int, var_index: dict[str, int]) -> tuple[int, ...]:
    if term[0] == "var":
        coeffs = [0] * len(var_index)
        coeffs[var_index[term[1]]] = 1
        return tuple(coeffs)
    left = term_coefficients(term[1], a, b, p, var_index)
    right = term_coefficients(term[2], a, b, p, var_index)
    return tuple((a * left[i] + b * right[i]) % p for i in range(len(var_index)))


def term_value(term: Term, assignment: tuple[int, ...], a: int, b: int, p: int, var_index: dict[str, int]) -> int:
    if term[0] == "var":
        return assignment[var_index[term[1]]]
    return (
        a * term_value(term[1], assignment, a, b, p, var_index)
        + b * term_value(term[2], assignment, a, b, p, var_index)
    ) % p


def equation_holds_by_coefficients(equation: Equation, p: int, a: int, b: int) -> bool:
    var_index = {var: idx for idx, var in enumerate(equation.variables)}
    left = term_coefficients(equation.left, a, b, p, var_index)
    right = term_coefficients(equation.right, a, b, p, var_index)
    return left == right


def brute_force_equation_holds(equation: Equation, p: int, a: int, b: int) -> bool:
    var_index = {var: idx for idx, var in enumerate(equation.variables)}
    for assignment in itertools.product(range(p), repeat=len(equation.variables)):
        left = term_value(equation.left, assignment, a, b, p, var_index)
        right = term_value(equation.right, assignment, a, b, p, var_index)
        if left != right:
            return False
    return True


def find_counterexample(equation: Equation, p: int, a: int, b: int) -> dict[str, int] | None:
    var_index = {var: idx for idx, var in enumerate(equation.variables)}
    for assignment in itertools.product(range(p), repeat=len(equation.variables)):
        left = term_value(equation.left, assignment, a, b, p, var_index)
        right = term_value(equation.right, assignment, a, b, p, var_index)
        if left != right:
            return {var: assignment[idx] for var, idx in var_index.items()}
    return None


def equations_with_var_bound(equations: list[Equation], max_vars: int | None) -> list[Equation]:
    if max_vars is None:
        return list(equations)
    return [equation for equation in equations if len(equation.variables) <= max_vars]


def pattern_hash(satisfied: tuple[int, ...]) -> str:
    payload = ",".join(str(item) for item in satisfied).encode("ascii")
    return hashlib.sha1(payload).hexdigest()[:16]


def run_prime(
    p: int,
    equations: list[Equation],
    max_vars: int | None,
    pattern_detail_limit: int,
) -> tuple[dict[str, Any], set[tuple[int, ...]]]:
    selected = equations_with_var_bound(equations, max_vars)
    start = time.perf_counter()
    patterns: Counter[tuple[int, ...]] = Counter()
    examples: dict[tuple[int, ...], tuple[int, int]] = {}

    for a in range(p):
        for b in range(p):
            satisfied = tuple(
                equation.number
                for equation in selected
                if equation_holds_by_coefficients(equation, p, a, b)
            )
            patterns[satisfied] += 1
            examples.setdefault(satisfied, (a, b))

    all_ids = {equation.number for equation in selected}
    details = []
    for satisfied, count in patterns.most_common(pattern_detail_limit):
        satisfied_set = set(satisfied)
        details.append(
            {
                "hash": pattern_hash(satisfied),
                "coefficient_pair_count": count,
                "example_coefficients": list(examples[satisfied]),
                "satisfied": list(satisfied),
                "refuted": sorted(all_ids - satisfied_set),
            }
        )

    result = {
        "prime": p,
        "coefficients_tested": p * p,
        "max_variables": max_vars,
        "equations_checked": len(selected),
        "distinct_satisfaction_patterns": len(patterns),
        "elapsed_seconds": round(time.perf_counter() - start, 6),
        "pattern_details": details,
        "pattern_details_truncated": len(patterns) > pattern_detail_limit,
    }
    return result, set(patterns)


def anti_implications_from_patterns(patterns: set[tuple[int, ...]], equation_ids: set[int]) -> set[tuple[int, int]]:
    anti_implications: set[tuple[int, int]] = set()
    for pattern in patterns:
        satisfied = set(pattern)
        refuted = equation_ids - satisfied
        for antecedent in satisfied:
            for consequent in refuted:
                anti_implications.add((antecedent, consequent))
    return anti_implications


def run_bruteforce_sanity(equations: list[Equation], max_vars: int, sample_coefficients: int) -> dict[str, Any]:
    selected = equations_with_var_bound(equations, max_vars)
    mismatches = []
    checked = 0
    for a, b in itertools.islice(itertools.product(range(13), repeat=2), sample_coefficients):
        for equation in selected:
            by_coefficients = equation_holds_by_coefficients(equation, 13, a, b)
            by_product = brute_force_equation_holds(equation, 13, a, b)
            checked += 1
            if by_coefficients != by_product:
                mismatches.append(
                    {
                        "equation": equation.number,
                        "a": a,
                        "b": b,
                        "coefficients": by_coefficients,
                        "bruteforce": by_product,
                    }
                )
                if len(mismatches) >= 20:
                    break
        if len(mismatches) >= 20:
            break
    return {
        "prime": 13,
        "max_variables": max_vars,
        "sample_coefficient_pairs": sample_coefficients,
        "equation_results_checked": checked,
        "mismatches": mismatches,
    }


def equation_catalog(equations: list[Equation]) -> list[dict[str, Any]]:
    return [
        {
            "number": equation.number,
            "text": equation.text,
            "variables": list(equation.variables),
            "variable_count": len(equation.variables),
        }
        for equation in equations
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-vars-p13", type=int, default=None)
    parser.add_argument("--max-vars-p89", type=int, default=4)
    parser.add_argument("--max-vars-p233", type=int, default=2)
    parser.add_argument("--max-vars-baseline", type=int, default=2)
    parser.add_argument("--pattern-detail-limit", type=int, default=20)
    parser.add_argument("--novel-pair-limit", type=int, default=5000)
    parser.add_argument("--bruteforce-sanity-max-vars", type=int, default=2)
    parser.add_argument("--bruteforce-sanity-coefficients", type=int, default=20)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    SCRIPT_DIR.mkdir(parents=True, exist_ok=True)
    equations, source_info = load_equations()
    print(f"Loaded {len(equations)} equations from {source_info['source']}")
    if source_info["synthetic_fallback"]:
        print("GitHub equation fetch failed; using synthetic standard magma laws.")

    run_started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    prime_configs = {
        13: args.max_vars_p13,
        89: args.max_vars_p89,
        233: args.max_vars_p233,
    }

    selected_prime_results: dict[str, Any] = {}
    selected_patterns: dict[int, set[tuple[int, ...]]] = {}
    for p, max_vars in prime_configs.items():
        result, patterns = run_prime(p, equations, max_vars, args.pattern_detail_limit)
        selected_prime_results[str(p)] = result
        selected_patterns[p] = patterns
        print(
            f"p={p}: checked {result['equations_checked']} equations over "
            f"{result['coefficients_tested']} coefficient pairs; "
            f"{result['distinct_satisfaction_patterns']} distinct patterns"
        )

    novelty_equations = equations_with_var_bound(equations, args.max_vars_baseline)
    novelty_ids = {equation.number for equation in novelty_equations}
    baseline_patterns: dict[int, set[tuple[int, ...]]] = {}
    baseline_anti: set[tuple[int, int]] = set()
    baseline_start = time.perf_counter()
    for p in BASELINE_PRIMES_LE_200:
        result, patterns = run_prime(p, equations, args.max_vars_baseline, 0)
        baseline_patterns[p] = patterns
        baseline_anti.update(anti_implications_from_patterns(patterns, novelty_ids))
        print(
            f"baseline p={p}: {result['distinct_satisfaction_patterns']} patterns, "
            f"{len(baseline_anti)} cumulative anti-implications"
        )

    p233_patterns_for_novelty = selected_patterns[233]
    if args.max_vars_p233 != args.max_vars_baseline:
        _, p233_patterns_for_novelty = run_prime(233, equations, args.max_vars_baseline, 0)
    p233_anti = anti_implications_from_patterns(p233_patterns_for_novelty, novelty_ids)
    novel_pairs = sorted(p233_anti - baseline_anti)

    sanity = run_bruteforce_sanity(
        equations,
        args.bruteforce_sanity_max_vars,
        args.bruteforce_sanity_coefficients,
    )
    if sanity["mismatches"]:
        print(f"WARNING: brute-force sanity found {len(sanity['mismatches'])} mismatches")
    else:
        print(
            "Brute-force sanity: "
            f"{sanity['equation_results_checked']} p=13 checks matched coefficient criterion"
        )

    results = {
        "run_started": run_started,
        "run_finished": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "method": {
            "main_search": "exact linear coefficient comparison over GF(p)",
            "bruteforce_checker": "available and sampled with itertools.product",
            "note": (
                "For x diamond y = a*x + b*y, every term is a linear form. "
                "An identity holds for all assignments iff left and right "
                "coefficient vectors are equal modulo p."
            ),
        },
        "source_info": source_info,
        "equation_count_total": len(equations),
        "equations": equation_catalog(equations),
        "selected_prime_results": selected_prime_results,
        "baseline": {
            "primes": BASELINE_PRIMES_LE_200,
            "max_variables": args.max_vars_baseline,
            "equations_checked": len(novelty_equations),
            "distinct_patterns_by_prime": {
                str(p): len(patterns) for p, patterns in baseline_patterns.items()
            },
            "anti_implication_count": len(baseline_anti),
            "elapsed_seconds": round(time.perf_counter() - baseline_start, 6),
        },
        "p233_novelty": {
            "max_variables": args.max_vars_baseline,
            "equations_checked": len(novelty_equations),
            "p233_anti_implication_count": len(p233_anti),
            "novel_anti_implication_count": len(novel_pairs),
            "novel_anti_implications": [
                {"satisfies": pair[0], "refutes": pair[1]}
                for pair in novel_pairs[: args.novel_pair_limit]
            ],
            "novel_anti_implications_truncated": len(novel_pairs) > args.novel_pair_limit,
        },
        "bruteforce_sanity": sanity,
    }

    RESULTS_PATH.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {RESULTS_PATH}")
    print(
        "p=233 novelty: "
        f"{len(novel_pairs)} anti-implications not achieved by baseline primes <= 200 "
        f"within <= {args.max_vars_baseline} variables"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
