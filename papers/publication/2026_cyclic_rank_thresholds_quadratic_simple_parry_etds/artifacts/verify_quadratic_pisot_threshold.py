#!/usr/bin/env python3
"""Exact finite verification for the quadratic-Pisot Parry-rank fold.

Output symbols are stored as their Parry ranks.  The manuscript proves that
rank is a bijection on the reversed greedy language, so this representation
does not discard output information.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from contextlib import redirect_stdout
from dataclasses import dataclass
from fractions import Fraction
from io import StringIO
from itertools import product
from math import sqrt
from pathlib import Path


@dataclass(frozen=True)
class QuadraticPisot:
    conjugate_sign: str
    a: int
    b: int

    def __post_init__(self) -> None:
        if self.conjugate_sign == "negative":
            valid = self.a >= 1 and 1 <= self.b <= self.a
        elif self.conjugate_sign == "positive":
            valid = self.a >= 3 and 1 <= self.b <= self.a - 2
        else:
            valid = False
        if not valid:
            raise ValueError("parameters do not define a quadratic Pisot number")

    @property
    def alphabet_size(self) -> int:
        return self.a + 1 if self.conjugate_sign == "negative" else self.a

    @property
    def max_digit(self) -> int:
        return self.alphabet_size - 1

    @property
    def beta(self) -> float:
        radicand = self.a * self.a + (4 * self.b if self.conjugate_sign == "negative" else -4 * self.b)
        return (self.a + sqrt(radicand)) / 2

    @property
    def polynomial(self) -> str:
        sign = "-" if self.conjugate_sign == "negative" else "+"
        return f"x^2-{self.a}x{sign}{self.b}"

    @property
    def parry_data(self) -> str:
        if self.conjugate_sign == "negative":
            return f"d_beta(1)={self.a},{self.b},0^inf; d_beta^*(1)=({self.a},{self.b - 1})^inf"
        return f"d_beta(1)={self.a - 1},({self.a - self.b - 1})^inf"

    def q_sequence(self, m: int) -> list[int]:
        q = [1, self.alphabet_size]
        recurrence_sign = 1 if self.conjugate_sign == "negative" else -1
        while len(q) <= m:
            q.append(self.a * q[-1] + recurrence_sign * self.b * q[-2])
        return q

    def q(self, m: int) -> int:
        return self.q_sequence(m)[m]

    def is_legal(self, word: tuple[int, ...]) -> bool:
        """Test whether the low-to-high word reverses to a greedy beta word."""
        if self.conjugate_sign == "negative":
            return all(word[k] != self.a or word[k - 1] < self.b for k in range(1, len(word)))

        maximum = self.a - 1
        tail_digit = self.a - self.b - 1
        high_to_low = word[::-1]
        for start in range(len(high_to_low)):
            tail = high_to_low[start:]
            parry_prefix = (maximum,) + (tail_digit,) * (len(tail) - 1)
            if tail > parry_prefix:
                return False
        return True

    def value(self, word: tuple[int, ...]) -> int:
        q = self.q_sequence(len(word))
        return sum(digit * q[index] for index, digit in enumerate(word))


def classify_minimal_polynomial(trace: int, norm: int) -> QuadraticPisot:
    """Classify x^2-trace*x+norm, rejecting non-Pisot parameters."""
    if norm < 0:
        return QuadraticPisot("negative", trace, -norm)
    if norm > 0:
        return QuadraticPisot("positive", trace, norm)
    raise ValueError("a quadratic Pisot minimal polynomial is irreducible")


def predicted_threshold(beta: QuadraticPisot) -> int:
    if beta.conjugate_sign == "negative":
        return 3 if beta.a == beta.b else 2
    return 3 if beta.b == 1 else 2


def nearest_multiple_separation(
    beta: QuadraticPisot, r: int, difference: int
) -> tuple[int, int]:
    """Return the exact nearest-multiple distance and its claimed lower bound."""
    if r < 4 or not 1 <= abs(difference) <= beta.max_digit:
        raise ValueError("require r>=4 and a nonzero bounded digit difference")
    q = beta.q_sequence(r)
    residue = beta.b * difference * q[r - 1] % q[r]
    distance = min(residue, q[r] - residue)
    return distance, q[r - 2]


def separation_proof_obligations(beta: QuadraticPisot) -> bool:
    """Check the exact integer branches used in the separation proof."""
    a, b = beta.a, beta.b
    if beta.conjugate_sign == "negative":
        denominator_u = a * a + a + b
        denominator_l = a**3 + a * a + 2 * a * b + b
        upper_offset = Fraction(b * (a + 1), denominator_u)
        lower_offset = Fraction(b * denominator_u, denominator_l)
        for e in range(1, a + 1):
            q, remainder = divmod(b * e, a)
            for k in range(0, b + 1):
                h = b * e - a * k
                if h <= 0:
                    continue
                if k <= q - 1:
                    if h * (a + lower_offset) - k * b < 1:
                        return False
                    continue
                if k != q:
                    return False
                p, terminal = divmod(q * b, a)
                if p < remainder:
                    if remainder * (a + lower_offset) - q * b < 1:
                        return False
                elif p > remainder:
                    if q * b - remainder * (a + upper_offset) < 1:
                        return False
                else:
                    w = remainder * b - a * terminal
                    if w == 0:
                        return False
                    if w > 0:
                        if (
                            remainder * b * denominator_u
                            < (terminal + 1) * denominator_l
                        ):
                            return False
                    elif (
                        terminal * denominator_u
                        < remainder * b * (a + 1) + denominator_u
                    ):
                        return False
        return True

    denominator = a * a - b
    upper = Fraction(a**3 - 2 * a * b, denominator)
    for e in range(1, a):
        for k in range(0, b + 1):
            g = a * k - b * e
            if g <= 0:
                continue
            norm = k * k - a * e * k + b * e * e
            if norm == 0:
                return False
            if norm > 0 and k * b - g * upper < 1:
                return False
    return True


def residue_table(beta: QuadraticPisot, m: int) -> list[int]:
    base = beta.alphabet_size
    q = beta.q_sequence(m)
    return [
        sum(digit * q[index] for index, digit in enumerate(word)) % q[m]
        for word in product(range(base), repeat=m)
    ]


def legal_rank_range_holds(beta: QuadraticPisot, m: int) -> bool:
    values = [
        beta.value(word)
        for word in product(range(beta.alphabet_size), repeat=m)
        if beta.is_legal(word)
    ]
    return sorted(values) == list(range(beta.q(m)))


def block_language_profile(beta: QuadraticPisot, m: int, n: int) -> tuple[int, int, bool]:
    base = beta.alphabet_size
    modulus = beta.q(m)
    table = residue_table(beta, m)
    suffix_modulus = base ** (m - 1)
    outputs: set[int] = set()
    collision = False

    for raw in product(range(base), repeat=n + m - 1):
        window_code = 0
        for digit in raw[:m]:
            window_code = window_code * base + digit
        output_code = 0
        for t in range(n):
            output_code = output_code * modulus + table[window_code]
            if t + 1 < n:
                window_code = (window_code % suffix_modulus) * base + raw[t + m]
        if output_code in outputs:
            collision = True
        outputs.add(output_code)

    raw_count = base ** (n + m - 1)
    return len(outputs), raw_count, collision


def causal_first_digit_is_determined(beta: QuadraticPisot, m: int, output_length: int) -> bool:
    """Check whether an output block determines the first raw digit exactly."""
    if m < 1 or output_length < 1:
        raise ValueError("m and output_length must be positive")

    base = beta.alphabet_size
    table = residue_table(beta, m)
    suffix_modulus = base ** (m - 1)
    first_digits: dict[tuple[int, ...], int] = {}

    for raw in product(range(base), repeat=m + output_length - 1):
        window_code = 0
        for digit in raw[:m]:
            window_code = window_code * base + digit

        outputs = []
        for t in range(output_length):
            outputs.append(table[window_code])
            if t + 1 < output_length:
                window_code = (window_code % suffix_modulus) * base + raw[t + m]

        key = tuple(outputs)
        previous = first_digits.setdefault(key, raw[0])
        if previous != raw[0]:
            return False
    return True


def minimum_injective_output_length(beta: QuadraticPisot, m: int) -> int | None:
    """Return the first injective finite-block length up to the aperture."""
    for n in range(1, m + 1):
        _, _, collision = block_language_profile(beta, m, n)
        if not collision:
            return n
    return None


def critical_periodic_fiber_histogram(beta: QuadraticPisot, period: int) -> Counter[int]:
    """Count periodic output fibers for an extremal aperture-two recoding."""
    if predicted_threshold(beta) != 3:
        raise ValueError("the critical double-fiber profile is extremal only")
    if period < 1:
        raise ValueError("period must be positive")

    base = beta.alphabet_size
    table = residue_table(beta, 2)
    fibers: Counter[tuple[int, ...]] = Counter()
    for raw in product(range(base), repeat=period):
        outputs = []
        for t in range(period):
            code = raw[t] * base + raw[(t + 1) % period]
            outputs.append(table[code])
        fibers[tuple(outputs)] += 1
    return Counter(fibers.values())


def periodic_point_count(beta: QuadraticPisot, m: int, n: int) -> int:
    base = beta.alphabet_size
    table = residue_table(beta, m)
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


def verification_cases() -> tuple[QuadraticPisot, ...]:
    negative = [QuadraticPisot("negative", a, b) for a in range(1, 7) for b in range(1, a + 1)]
    positive = [QuadraticPisot("positive", a, b) for a in range(3, 9) for b in range(1, a - 1)]
    return tuple(negative + positive)


def _run_verification() -> int:
    failures = 0
    counterexamples = 0
    cases = verification_cases()

    print("Quadratic-Pisot Parry-rank fold verification")
    print("Families: x^2-a*x-b (a>=b>=1) and x^2-a*x+b (a>=3, 1<=b<=a-2)")
    print("Exact integer arithmetic; output blocks are encoded by canonical Parry ranks modulo Q_m.")
    print()

    for beta in cases:
        for m in range(1, 6):
            if not legal_rank_range_holds(beta, m):
                failures += 1
                print(f"FAIL Parry rank: {beta.polynomial}, m={m}")

    print(f"Parry-language rank battery: {len(cases) * 5} cases checked")
    print()
    print("Threshold and block-language battery (n=m):")
    for beta in cases:
        entries = []
        for m in (2, 3, 4):
            got, raw, collision = block_language_profile(beta, m, m)
            expected_collision = m < predicted_threshold(beta)
            expected = raw - 1 if expected_collision else raw
            if collision != expected_collision or got != expected:
                failures += 1
                if collision and not expected_collision:
                    counterexamples += 1
            entries.append(f"m={m}:{got}/{raw}[{'N' if collision else 'I'}]")
        print(
            f"  {beta.polynomial:11s} beta={beta.beta:.12f} "
            f"m*={predicted_threshold(beta)}  " + "; ".join(entries)
        )

    print()
    print("Extended block battery (n=m+1) on boundary and interior representatives:")
    extended = (
        QuadraticPisot("negative", 1, 1),
        QuadraticPisot("negative", 4, 4),
        QuadraticPisot("negative", 6, 3),
        QuadraticPisot("positive", 3, 1),
        QuadraticPisot("positive", 6, 1),
        QuadraticPisot("positive", 6, 3),
    )
    for beta in extended:
        for m in range(predicted_threshold(beta), 5):
            got, raw, collision = block_language_profile(beta, m, m + 1)
            print(f"  {beta.polynomial}, m={m}, n={m + 1}: {got}/{raw}")
            if collision or got != raw:
                failures += 1
                counterexamples += 1

    print()
    print("Exceptional two-window periodic-point battery (n=1,...,6):")
    extremals = (
        QuadraticPisot("negative", 1, 1),
        QuadraticPisot("negative", 4, 4),
        QuadraticPisot("positive", 3, 1),
        QuadraticPisot("positive", 7, 1),
    )
    for beta in extremals:
        got = [periodic_point_count(beta, 2, n) for n in range(1, 7)]
        expected = [beta.alphabet_size**n - 1 for n in range(1, 7)]
        print(f"  {beta.polynomial}: got={got}; expected={expected}")
        if got != expected:
            failures += 1

    print()
    print("Aperture-two chamber-duality and aperture-three separation battery:")
    duality_checks = 0
    for q in range(3, 8):
        for kappa in range(2, q):
            negative = QuadraticPisot("negative", q - 1, kappa)
            positive = QuadraticPisot("positive", q, q - kappa)
            same_fold = residue_table(negative, 2) == residue_table(positive, 2)
            negative_words = {
                word for word in product(range(q), repeat=3) if negative.is_legal(word)
            }
            positive_words = {
                word for word in product(range(q), repeat=3) if positive.is_legal(word)
            }
            expected_difference = {
                (high, kappa - 1, q - 1) for high in range(kappa, q)
            }
            separated = (
                negative_words - positive_words == expected_difference
                and not positive_words - negative_words
                and negative.q(3) - positive.q(3) == q - kappa
            )
            duality_checks += 1
            if not same_fold or not separated:
                failures += 1
    print(f"  {duality_checks} paired chambers checked: identical at m=2, exact separation at m=3")

    print()
    print("Optimal causal-length and exact finite-block-onset battery:")
    negative_depth_cases = tuple(
        QuadraticPisot("negative", a, b)
        for a in range(1, 5)
        for b in range(1, a + 1)
    )
    positive_depth_cases = (
        QuadraticPisot("positive", 3, 1),
        QuadraticPisot("positive", 5, 2),
    )
    local_checks = 0
    for beta in negative_depth_cases:
        for m in range(3, 7):
            lower = causal_first_digit_is_determined(beta, m, 1)
            exact = causal_first_digit_is_determined(beta, m, 2)
            local_checks += 1
            if lower or not exact:
                failures += 1
    for beta in positive_depth_cases:
        for m in range(3, 6):
            lower = causal_first_digit_is_determined(beta, m, 2)
            exact = causal_first_digit_is_determined(beta, m, 3)
            local_checks += 1
            if lower or not exact:
                failures += 1
    print(
        f"  {local_checks} parameter/aperture pairs checked: "
        "exact negative/positive causal lengths 2/3"
    )

    print()
    print("Critical periodic-fiber battery:")
    fiber_checks = 0
    for beta in extremals:
        for period in range(1, 7):
            histogram = critical_periodic_fiber_histogram(beta, period)
            expected_singletons = beta.alphabet_size**period - 2
            fiber_checks += 1
            if histogram.get(2) != 1 or histogram.get(1, 0) != expected_singletons:
                failures += 1
    print(f"  {fiber_checks} parameter/period pairs checked: one double fiber, all others singleton")

    print()
    print("Nearest-multiple separation battery:")
    separation_checks = 0
    for a in range(1, 16):
        for b in range(1, a + 1):
            beta = QuadraticPisot("negative", a, b)
            for r in range(4, 11):
                for difference in range(1, a + 1):
                    distance, lower_bound = nearest_multiple_separation(
                        beta, r, difference
                    )
                    separation_checks += 1
                    failures += distance < lower_bound
    for a in range(3, 16):
        for b in range(1, a - 1):
            beta = QuadraticPisot("positive", a, b)
            for r in range(4, 11):
                for difference in range(1, a):
                    distance, lower_bound = nearest_multiple_separation(
                        beta, r, difference
                    )
                    separation_checks += 1
                    failures += distance < lower_bound
    print(f"  {separation_checks} exact distances checked in both chambers")

    print()
    print("Nearest-multiple proof-obligation battery:")
    obligation_checks = 0
    for a in range(1, 40):
        for b in range(1, a + 1):
            obligation_checks += 1
            failures += not separation_proof_obligations(
                QuadraticPisot("negative", a, b)
            )
    for a in range(3, 40):
        for b in range(1, a - 1):
            obligation_checks += 1
            failures += not separation_proof_obligations(
                QuadraticPisot("positive", a, b)
            )
    print(f"  {obligation_checks} exact branch tables checked")

    print()
    print("Counterexample search domain:")
    print("  negative conjugate: 1<=a<=6, 1<=b<=a, m=2,3,4")
    print("  positive conjugate: 3<=a<=8, 1<=b<=a-2, m=2,3,4")
    print(f"  parameter pairs searched: {len(cases)}")
    print(f"SUMMARY: {failures} failures / {counterexamples} unexpected collisions")
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
