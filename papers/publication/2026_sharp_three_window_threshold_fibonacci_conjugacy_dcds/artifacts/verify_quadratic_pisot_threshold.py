#!/usr/bin/env python3
"""Exact finite verification for the quadratic-Pisot Parry-rank fold.

Output symbols are stored as their Parry ranks.  The manuscript proves that
rank is a bijection on the reversed greedy language, so this representation
does not discard output information.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import sqrt


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


def main() -> int:
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
    print("Counterexample search domain:")
    print("  negative conjugate: 1<=a<=6, 1<=b<=a, m=2,3,4")
    print("  positive conjugate: 3<=a<=8, 1<=b<=a-2, m=2,3,4")
    print(f"  parameter pairs searched: {len(cases)}")
    print(f"SUMMARY: {failures} failures / {counterexamples} unexpected collisions")
    return 0 if failures == 0 and counterexamples == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
