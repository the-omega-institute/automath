#!/usr/bin/env python3
"""Exact finite regression checks for the fixed cubic terminal words."""

from __future__ import annotations

from itertools import product


DIGITS = (-1, 0, 1)


def recurrence(count: int) -> list[int]:
    values = [1, 2, 4]
    while len(values) < count:
        values.append(2 * values[-1] - values[-2] + values[-3])
    return values[:count]


def terminal_word(aperture: int) -> tuple[int, ...]:
    if aperture == 4:
        return (1, -1, -1, -1, 1)
    if aperture % 2 == 1:
        return terminal_word(aperture - 1) + (0,)
    inner = tuple(-entry for entry in terminal_word(aperture - 2))
    return (1, 0) + inner + (0, 0)


def obstruction_vectors(aperture: int, rows: int) -> set[tuple[int, ...]]:
    """Enumerate anchored coefficient words satisfying `rows` congruences."""

    weights = recurrence(aperture + 1)
    modulus = weights[aperture]
    active: set[tuple[int, ...]] = set()
    for body in product(DIGITS, repeat=aperture):
        if body[0] and sum(a * q for a, q in zip(body, weights)) % modulus == 0:
            active.add(body)

    for _ in range(1, rows):
        extended: set[tuple[int, ...]] = set()
        for word in active:
            tail = word[-(aperture - 1) :]
            for digit in DIGITS:
                window = tail + (digit,)
                if sum(a * q for a, q in zip(window, weights)) % modulus == 0:
                    extended.add(word + (digit,))
        active = extended
        if not active:
            break
    return active


def main() -> None:
    assert recurrence(11) == [1, 2, 4, 7, 12, 21, 37, 65, 114, 200, 351]
    passed = 1
    print("PASS recurrence values through Q_10")

    for aperture in range(4, 13):
        causal_length = 2 * (aperture // 2) - 1
        expected_word = terminal_word(aperture)
        penultimate = obstruction_vectors(aperture, causal_length - 1)
        expected = {expected_word, tuple(-entry for entry in expected_word)}
        assert penultimate == expected, (aperture, penultimate, expected)
        passed += 1
        print(
            f"PASS m={aperture} rows={causal_length - 1} "
            "terminal_obstructions=2"
        )

        next_set = obstruction_vectors(aperture, causal_length)
        assert next_set == set(), (aperture, next_set)
        passed += 1
        print(f"PASS m={aperture} rows={causal_length} next_obstructions=0")

        weights = recurrence(len(expected_word))
        modulus = weights[aperture]
        window_sums = [
            sum(weights[j] * expected_word[t + j] for j in range(aperture))
            for t in range(causal_length - 1)
        ]
        assert all(total % modulus == 0 for total in window_sums)
        assert all(entry in DIGITS for entry in expected_word)
        passed += 1
        print(f"PASS m={aperture} recursive_word exact_window_divisibility")

    print(f"PASS: {passed}/{1 + 3 * len(range(4, 13))} fixed-cubic audit cases")


if __name__ == "__main__":
    main()
