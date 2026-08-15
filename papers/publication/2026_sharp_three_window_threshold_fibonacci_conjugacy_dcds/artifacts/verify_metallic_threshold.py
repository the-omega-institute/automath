#!/usr/bin/env python3
"""Finite verification battery for the metallic threshold classification.

The output symbols are represented by their valuation residues.  This is
lossless because Val_{A,m} is bijective on the legal language X_m^(A).
"""

from __future__ import annotations

import argparse
import sys
from contextlib import redirect_stdout
from io import StringIO
from itertools import product
from math import sqrt
from pathlib import Path


MAIN_CASES = (
    [(a, m) for a in range(1, 5) for m in range(2, 6)]
    + [(a, m) for a in range(5, 7) for m in range(2, 5)]
)
EXTENDED_CASES = (
    [(1, m) for m in range(3, 6)]
    + [(a, m) for a in range(2, 5) for m in range(2, 5)]
)


def q_sequence(a: int, m: int) -> list[int]:
    q = [1, a + 1]
    while len(q) <= m:
        q.append(a * q[-1] + q[-2])
    return q


def residue_table(a: int, m: int, q: list[int]) -> list[int]:
    base = a + 1
    weights = q[:m]
    return [
        sum(digit * weight for digit, weight in zip(word, weights)) % q[m]
        for word in product(range(base), repeat=m)
    ]


def legal_range_holds(a: int, m: int, q: list[int]) -> bool:
    values = []
    for word in product(range(a + 1), repeat=m):
        if all(word[k] != a or word[k - 1] == 0 for k in range(1, m)):
            values.append(sum(word[k] * q[k] for k in range(m)))
    return sorted(values) == list(range(q[m]))


def language_profile(a: int, m: int, lengths: tuple[int, ...]) -> tuple[dict[int, int], bool]:
    """Return exact language counts and whether the longest map collides."""
    base = a + 1
    q = q_sequence(a, m)
    modulus = q[m]
    table = residue_table(a, m, q)
    suffix_modulus = base ** (m - 1)
    max_n = max(lengths)
    languages = {n: set() for n in lengths}
    longest_seen: set[int] = set()
    collision = False

    for raw in product(range(base), repeat=max_n + m - 1):
        window_code = 0
        for digit in raw[:m]:
            window_code = window_code * base + digit

        output_code = 0
        prefix_codes: dict[int, int] = {}
        for t in range(max_n):
            residue = table[window_code]
            output_code = output_code * modulus + residue
            n = t + 1
            if n in languages:
                prefix_codes[n] = output_code
            if n < max_n:
                window_code = (
                    (window_code % suffix_modulus) * base + raw[t + m]
                )

        for n, code in prefix_codes.items():
            languages[n].add(code)
        longest_code = prefix_codes[max_n]
        if longest_code in longest_seen:
            collision = True
        else:
            longest_seen.add(longest_code)

    return {n: len(languages[n]) for n in lengths}, collision


def periodic_language_count(a: int, m: int, n: int) -> int:
    """Count output points fixed by sigma^n using cyclic raw words."""
    base = a + 1
    q = q_sequence(a, m)
    table = residue_table(a, m, q)
    outputs = set()
    for raw in product(range(base), repeat=n):
        residues = []
        for t in range(n):
            code = 0
            for j in range(m):
                code = code * base + raw[(t + j) % n]
            residues.append(table[code])
        outputs.add(tuple(residues))
    return len(outputs)


def predicted_injective(a: int, m: int) -> bool:
    return (a, m) != (1, 2)


def _run_verification() -> int:
    failures = 0
    counterexamples = 0
    injective_cases_searched = 0
    expected_obstructions = 0
    profiles: dict[tuple[int, int], dict[int, int]] = {}
    injectivity: dict[tuple[int, int], bool] = {}

    print("Metallic threshold finite verification")
    print("Model: beta_A=(A+sqrt(A^2+4))/2, integer A>=1")
    print("Output words are encoded by canonical valuation residues modulo Q_m.")
    print()

    for a, m in MAIN_CASES:
        q = q_sequence(a, m)
        if not legal_range_holds(a, m, q):
            failures += 1
            print(f"FAIL legal range: A={a}, m={m}")

        counts, collision = language_profile(a, m, tuple(range(1, m + 1)))
        profiles[a, m] = counts
        injectivity[a, m] = not collision
        total = (a + 1) ** (2 * m - 1)

        if predicted_injective(a, m):
            injective_cases_searched += 1
            if collision:
                counterexamples += 1
                failures += 1
                print(f"COUNTEREXAMPLE collision: A={a}, m={m}, n={m}")
            if counts[m] != total:
                failures += 1
                print(
                    f"FAIL block count: A={a}, m={m}, n={m}, "
                    f"got={counts[m]}, expected={total}"
                )
        else:
            expected_count = total - 1
            if collision and counts[m] == expected_count:
                expected_obstructions += 1
            else:
                failures += 1
                print(
                    f"FAIL expected golden obstruction: got={counts[m]}, "
                    f"expected={expected_count}, collision={collision}"
                )

    print("Block-language battery (entry is |L_m| / raw-block count):")
    for a in range(1, 7):
        beta = (a + sqrt(a * a + 4)) / 2
        tested_m = sorted(m for aa, m in MAIN_CASES if aa == a)
        entries = []
        for m in tested_m:
            got = profiles[a, m][m]
            total = (a + 1) ** (2 * m - 1)
            marker = "I" if injectivity[a, m] else "N"
            entries.append(f"m={m}: {got}/{total} [{marker}]")
        print(f"  A={a}, beta={beta:.12f}: " + "; ".join(entries))
    print("  [I] injective finite-block map; [N] noninjective.")
    print()

    print("Observed nontrivial thresholds over all tested apertures:")
    for a in range(1, 7):
        tested_m = sorted(m for aa, m in MAIN_CASES if aa == a)
        observed = next(
            m
            for m in tested_m
            if all(injectivity[a, k] for k in tested_m if k >= m)
        )
        expected = 3 if a == 1 else 2
        print(f"  A={a}: observed m*={observed}, predicted m*={expected}")
        if observed != expected:
            failures += 1

    print()
    print("Extended n=m+1 block-count battery:")
    for a, m in EXTENDED_CASES:
        n = m + 1
        counts, collision = language_profile(a, m, (n,))
        expected = (a + 1) ** (n + m - 1)
        print(f"  A={a}, m={m}, n={n}: {counts[n]} / {expected}")
        if collision:
            counterexamples += 1
            failures += 1
            print(f"COUNTEREXAMPLE extended collision: A={a}, m={m}, n={n}")
        elif counts[n] != expected:
            failures += 1

    print()
    print("Golden block-bijection identity battery:")
    for m in range(3, 7):
        for n in (m, m + 1):
            counts, collision = language_profile(1, m, (n,))
            expected = 2 ** (n + m - 1)
            print(f"  A=1, m={m}, n={n}: {counts[n]} / {expected}")
            if collision:
                counterexamples += 1
                failures += 1
            elif counts[n] != expected:
                failures += 1

    print()
    print("Periodic-point / zeta-coefficient battery (n=1,...,6):")
    for a in range(1, 5):
        got = [periodic_language_count(a, 2, n) for n in range(1, 7)]
        expected = [
            (2**n - 1) if a == 1 else (a + 1) ** n
            for n in range(1, 7)
        ]
        print(f"  A={a}, m=2: got={got}; expected={expected}")
        if got != expected:
            failures += 1

    print()
    print("Expected obstruction witness:")
    print("  A=1, m=2: raw periodic points 0^Z and 1^Z both map to (00)^Z.")
    print(f"  expected obstruction cases confirmed: {expected_obstructions}")
    print(f"  predicted-injective cases searched explicitly: {injective_cases_searched}")
    print()
    print(f"SUMMARY: {failures} failures / {counterexamples} counterexamples")
    return 0 if failures == 0 and counterexamples == 0 else 1


def main(argv=()) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.output is None:
        return _run_verification()

    capture = StringIO()
    with redirect_stdout(capture):
        status = _run_verification()
    report = capture.getvalue()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="utf-8", newline="\n")
    print(report, end="")
    return status


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
