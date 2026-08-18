"""Exhaustive checks for the sharp commutation results in Section 3.

Words are encoded as integers whose bit k-1 is the digit of weight F_{k+1}.
The fold routine computes the full greedy Zeckendorf expansion and only then
truncates it, matching the definition in the paper.
"""

from fractions import Fraction
from functools import cache


def fibonacci(last_index: int) -> list[int]:
    numbers = [0, 1]
    while len(numbers) <= last_index:
        numbers.append(numbers[-1] + numbers[-2])
    return numbers


def fold_mask(value: int, length: int, fib: list[int]) -> int:
    folded = 0
    for position in range(length + 1, 0, -1):
        weight = fib[position + 1]
        if weight <= value:
            if position <= length:
                folded |= 1 << (position - 1)
            value -= weight
    assert value == 0
    return folded


@cache
def tables() -> tuple[list[int], list[list[int]], list[list[int]]]:
    fib = fibonacci(23)
    values = [[0]]
    folds = [[0]]
    for length in range(1, 21):
        top_bit = 1 << (length - 1)
        top_weight = fib[length + 1]
        previous = values[-1]
        layer_values = [0] * (1 << length)
        for word in range(1 << length):
            lower = word & (top_bit - 1)
            layer_values[word] = previous[lower] + (top_weight if word & top_bit else 0)
        values.append(layer_values)
        if length <= 17:
            folds.append([fold_mask(value, length, fib) for value in layer_values])
    return fib, values, folds


def verify_characterization() -> tuple[int, int, int]:
    fib, values, folds = tables()
    checked = 0
    mismatches = 0
    for m in range(1, 17):
        visible_mask = (1 << m) - 1
        for word, value in enumerate(values[m + 1]):
            commutes = (
                folds[m + 1][word] & visible_mask
                == folds[m][word & visible_mask]
            )
            no_wrap = value < fib[m + 3]
            mismatches += commutes != no_wrap
            checked += 1
    return checked, mismatches, 1 << 17


def verify_counts() -> tuple[int, int, int]:
    fib, values, _ = tables()
    mismatches = 0
    control_matches = 0
    for m in range(1, 20):
        observed = sum(value < fib[m + 3] for value in values[m + 1])
        target_numerator = 2 ** (m + 2) + 1
        expected = (target_numerator + 2) // 3
        control = Fraction(2 ** (m + 2) + 2, 3)
        mismatches += observed != expected
        control_matches += Fraction(observed) == control
    return mismatches, control_matches, 19


def verify_all_depths() -> tuple[int, int]:
    _, _, folds = tables()
    checked = 0
    mismatches = 0
    for length in range(2, 18):
        for word in range(1 << length):
            commutes_at_every_prefix = True
            for m in range(1, length):
                visible_mask = (1 << m) - 1
                prefix = word & ((1 << (m + 1)) - 1)
                if (
                    folds[m + 1][prefix] & visible_mask
                    != folds[m][prefix & visible_mask]
                ):
                    commutes_at_every_prefix = False
                    break
            golden_mean = (word & (word >> 1)) == 0
            mismatches += commutes_at_every_prefix != golden_mean
            checked += 1
    return checked, mismatches


def main() -> None:
    checked, mismatches, largest_layer = verify_characterization()
    assert (checked, mismatches, largest_layer) == (262_140, 0, 131_072)

    count_mismatches, control_matches, layers = verify_counts()
    assert (count_mismatches, control_matches, layers) == (0, 9, 19)

    tower_checked, tower_mismatches = verify_all_depths()
    assert (tower_checked, tower_mismatches) == (262_140, 0)

    print(
        "characterization: "
        f"checked={checked}, mismatches={mismatches}, "
        f"words_at_m16={largest_layer}"
    )
    print(
        "count m=1..19: "
        f"mismatches={count_mismatches}, "
        "control=(2^(m+2)+2)/3 "
        f"matches={control_matches}/{layers}"
    )
    print(
        "all-depth corollary, lengths 2..17: "
        f"checked={tower_checked}, mismatches={tower_mismatches}"
    )


if __name__ == "__main__":
    main()
