#!/usr/bin/env python3
"""Exact finite verification for the simple-Parry causal obstructions.

All collision calculations use integer arithmetic.  A tuple ``digits`` is the
finite greedy expansion d_beta(1)=t_1...t_p 0^infinity.
"""

from __future__ import annotations

from itertools import product


def q_sequence(digits: tuple[int, ...], n: int) -> list[int]:
    """Return Q_0,...,Q_n for a finite Parry word."""
    p = len(digits)
    if p < 1 or digits[-1] <= 0:
        raise ValueError("the finite Parry word must have positive last digit")
    q = [1]
    for k in range(1, n + 1):
        recurrence = sum(digits[i - 1] * q[k - i] for i in range(1, min(k, p) + 1))
        q.append(recurrence + (1 if k < p else 0))
    return q


def bounded_multiple_order(digits: tuple[int, ...]) -> int:
    """Verify and return the bounded-multiple order of the companion polynomial."""
    d = digits[0]
    if d < 1 or any(not 0 <= digit <= d for digit in digits):
        raise ValueError("digits must lie in the greedy alphabet")
    coefficients = (-digits[-1],) + tuple(-digit for digit in reversed(digits[:-1])) + (1,)
    if coefficients[0] == 0 or max(map(abs, coefficients)) > d:
        raise AssertionError("the companion polynomial does not meet the coefficient bound")
    # Every nonzero element of (P) has degree at least deg(P) in Z[z].
    return len(digits)


def _is_legal_low_to_high(digits: tuple[int, ...], word: tuple[int, ...]) -> bool:
    """Apply Parry's suffix test to a finite word in low-to-high order."""
    period = digits[:-1] + (digits[-1] - 1,)
    high_to_low = word[::-1]
    for start in range(len(high_to_low)):
        suffix = high_to_low[start:]
        boundary = tuple(period[j % len(period)] for j in range(len(suffix)))
        if suffix > boundary:
            return False
    return True


def rank_is_consecutive(digits: tuple[int, ...], m: int) -> bool:
    """Check the colex rank formula against the complete legal language."""
    d = digits[0]
    q = q_sequence(digits, m)
    ranks = [
        sum(word[j] * q[j] for j in range(m))
        for word in product(range(d + 1), repeat=m)
        if _is_legal_low_to_high(digits, word)
    ]
    return sorted(ranks) == list(range(q[m]))


def bad_blocks(
    digits: tuple[int, ...], m: int, output_length: int
) -> list[tuple[int, ...]]:
    """Enumerate all bounded differences that hide their first digit."""
    if m < 1 or output_length < 1:
        raise ValueError("m and output_length must be positive")
    d = digits[0]
    q = q_sequence(digits, m)
    modulus = q[m]
    blocks = []
    for difference in product(range(-d, d + 1), repeat=m + output_length - 1):
        if difference[0] == 0:
            continue
        if all(
            sum(q[j] * difference[t + j] for j in range(m)) % modulus == 0
            for t in range(output_length)
        ):
            blocks.append(difference)
    return blocks


def collision_graph_bad_path_count(
    digits: tuple[int, ...], m: int, output_length: int
) -> int:
    """Count bad paths directly in the length-(m-1) collision graph."""
    if m < 2 or output_length < 1:
        raise ValueError("the collision graph requires m>=2 and positive path length")
    d = digits[0]
    q = q_sequence(digits, m)
    modulus = q[m]
    states = product(range(-d, d + 1), repeat=m - 1)
    frontier: dict[tuple[int, ...], int] = {
        state: 1 for state in states if state[0] != 0
    }
    for _ in range(output_length):
        following: dict[tuple[int, ...], int] = {}
        for state, multiplicity in frontier.items():
            for appended in range(-d, d + 1):
                if (
                    sum(q[j] * state[j] for j in range(m - 1))
                    + q[m - 1] * appended
                ) % modulus:
                    continue
                terminal = state[1:] + (appended,)
                following[terminal] = following.get(terminal, 0) + multiplicity
        frontier = following
    return sum(frontier.values())


def periodic_collision(
    digits: tuple[int, ...], m: int, period: tuple[int, ...]
) -> bool:
    """Return whether a nonzero periodic difference labels an output collision."""
    if m < 1 or not period:
        raise ValueError("the aperture and period must be positive")
    d = digits[0]
    if all(entry == 0 for entry in period):
        return False
    if any(entry < -d or entry > d for entry in period):
        return False
    q = q_sequence(digits, m)
    modulus = q[m]
    return all(
        sum(q[j] * period[(phase + j) % len(period)] for j in range(m))
        % modulus
        == 0
        for phase in range(len(period))
    )


def p_bonacci_claims(p: int) -> dict[str, int]:
    if p < 3:
        raise ValueError("the high-degree family begins at p=3")
    digits = (1,) * p
    q = q_sequence(digits, p + 1)
    return {
        "q_p": q[p],
        "q_p1": q[p + 1],
        "bounded_multiple_order": bounded_multiple_order(digits),
        "one_output_bad": len(bad_blocks(digits, p + 1, 1)),
        "two_output_bad": len(bad_blocks(digits, p + 1, 2)),
    }


def gamma_claims() -> dict[str, list[int] | int | bool]:
    digits = (1, 0, 1)
    counts = [len(bad_blocks(digits, 4, length)) for length in range(1, 5)]
    positive = [
        sum(block[0] == 1 for block in bad_blocks(digits, 4, length))
        for length in range(1, 5)
    ]
    return {
        "bounded_multiple_order": bounded_multiple_order(digits),
        "counts": counts,
        "positive_representatives": positive,
        "aperture_2_periodic_collision": periodic_collision(digits, 2, (1,)),
        "aperture_3_periodic_collision": periodic_collision(
            digits, 3, (1, -1, -1, 1)
        ),
    }


def main() -> int:
    failures = 0
    print("Simple-Parry causal-obstruction verification")
    print("Exact integer arithmetic; difference alphabet [-d,d].")
    print()

    expected_sequences = {
        (1, 1, 1): [1, 2, 4, 7, 13, 24, 44],
        (1, 0, 1): [1, 2, 3, 4, 6, 9, 13],
        (2, 1): [1, 3, 7, 17, 41, 99, 239],
    }
    print("Parry recurrence battery:")
    for digits, expected in expected_sequences.items():
        got = q_sequence(digits, 6)
        status = "PASS" if got == expected else "FAIL"
        print(f"  t={digits}: {got} [{status}]")
        failures += got != expected

    print()
    print("Consecutive colex-rank battery (m=1,...,6):")
    rank_cases = ((1, 1, 1), (1, 0, 1), (2, 1), (2, 2), (2, 0, 1))
    rank_checks = 0
    for digits in rank_cases:
        for m in range(1, 7):
            rank_checks += 1
            if not rank_is_consecutive(digits, m):
                failures += 1
                print(f"  FAIL t={digits}, m={m}")
    print(f"  {rank_checks} finite languages checked")

    print()
    print("Toeplitz / collision-graph equivalence battery:")
    graph_checks = 0
    for digits, m in (((1, 1, 1), 4), ((1, 0, 1), 4), ((2, 1), 3)):
        counts = []
        for output_length in range(1, 5):
            toeplitz_count = len(bad_blocks(digits, m, output_length))
            graph_count = collision_graph_bad_path_count(digits, m, output_length)
            graph_checks += 1
            counts.append(toeplitz_count)
            if graph_count != toeplitz_count:
                failures += 1
                print(
                    f"  FAIL t={digits}, m={m}, L={output_length}: "
                    f"Toeplitz={toeplitz_count}, graph={graph_count}"
                )
        print(f"  t={digits}, m={m}: bad counts {counts}")
    print(f"  {graph_checks} path-length comparisons checked")

    print()
    print("p-bonacci unbounded-separation battery:")
    for p in range(3, 9):
        result = p_bonacci_claims(p)
        expected = {
            "q_p": 2**p - 1,
            "q_p1": 2 ** (p + 1) - 3,
            "bounded_multiple_order": p,
            "one_output_bad": 2,
            "two_output_bad": 0,
        }
        status = "PASS" if result == expected else "FAIL"
        print(f"  p={p}: {result} [{status}]")
        failures += result != expected

    print()
    gamma = gamma_claims()
    gamma_expected = {
        "bounded_multiple_order": 3,
        "counts": [12, 4, 2, 0],
        "positive_representatives": [6, 2, 1, 0],
        "aperture_2_periodic_collision": True,
        "aperture_3_periodic_collision": True,
    }
    status = "PASS" if gamma == gamma_expected else "FAIL"
    print("Cubic reverse-mismatch battery:")
    print(f"  d_beta(1)=1010^infinity, m=4: {gamma} [{status}]")
    failures += gamma != gamma_expected

    print()
    print(f"SUMMARY: {failures} failures")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
