#!/usr/bin/env python3
"""Exact finite checks for the reductions in the sharp context-rate proof."""

from fractions import Fraction


def continuant(word: tuple[int, ...]) -> int:
    previous, current = 0, 1
    for digit in word:
        previous, current = current, digit * current + previous
    return current


def compositions(total: int) -> list[tuple[int, ...]]:
    if total == 0:
        return [()]
    words: list[tuple[int, ...]] = []
    for first in range(1, total + 1):
        for suffix in compositions(total - first):
            words.append((first,) + suffix)
    return words


def left_words(max_sum: int) -> list[tuple[int, ...]]:
    return [
        word
        for total in range(max_sum + 1)
        for word in compositions(total)
    ]


def right_words(max_sum: int) -> list[tuple[int, ...]]:
    return [
        word
        for total in range(max_sum + 1)
        for word in compositions(total)
        if not word or word[-1] >= 2
    ]


def left_ratio(word: tuple[int, ...]) -> Fraction:
    return Fraction(0) if not word else Fraction(continuant(word[:-1]), continuant(word))


def right_ratio(word: tuple[int, ...]) -> Fraction:
    return Fraction(0) if not word else Fraction(continuant(word[1:]), continuant(word))


def verify_central_factorization() -> int:
    checked = 0
    for left in left_words(6):
        for right in right_words(6):
            for central in range(1, 10):
                product = continuant(left) * continuant(right)
                observed = Fraction(continuant(left + (central,) + right), product)
                asserted = central + left_ratio(left) + right_ratio(right)
                assert observed == asserted, (left, central, right, observed, asserted)
                checked += 1
    return checked


def verify_balanced_cut() -> tuple[int, int]:
    words_checked = 0
    maximum_sum = 18
    for total in range(4, maximum_sum + 1):
        for word in right_words(total):
            if sum(word) != total or max(word) * 2 > total:
                continue
            prefix_sum = 0
            cut = 0
            while 4 * prefix_sum < total:
                prefix_sum += word[cut]
                cut += 1
            left, right = word[:cut], word[cut:]
            assert total <= 4 * prefix_sum <= 3 * total
            assert total <= 4 * sum(right) <= 3 * total
            assert right and right[-1] >= 2
            assert continuant(word) >= continuant(left) * continuant(right)
            words_checked += 1
    return words_checked, maximum_sum


def main() -> None:
    factorization_count = verify_central_factorization()
    balanced_count, maximum_sum = verify_balanced_cut()
    print(f"central factorizations checked exactly: {factorization_count}")
    print(
        "noncondensed balanced cuts checked exactly: "
        f"{balanced_count} (canonical digit sums 4 through {maximum_sum})"
    )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
