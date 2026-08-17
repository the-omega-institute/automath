"""Exact check of the scan-error transfer theorem on the competing-runs filter."""

from fractions import Fraction
from itertools import product
import sys


STATES = ("H", "Z", "ZZ")
B = (
    (0, 1, 0),
    (1, 0, 1),
    (1, 0, 0),
)
S = (Fraction(1, 2), Fraction(1, 2), Fraction(0))
T = (Fraction(1, 5), Fraction(2, 5), Fraction(2, 5))
POSTERIOR = {
    "H": Fraction(4, 5),
    "Z": Fraction(3, 5),
    "ZZ": Fraction(2, 5),
}


def advance(state, symbol):
    if state == "S":
        return "H" if symbol else "Z"
    if state == "H":
        return "+" if symbol else "Z"
    if state == "Z":
        return "H" if symbol else "ZZ"
    if state == "ZZ":
        return "H" if symbol else "-"
    return state


def direct_error(depth):
    total = Fraction(0)
    for word in product((0, 1), repeat=depth):
        state = "S"
        for symbol in word:
            state = advance(state, symbol)
        if state in POSTERIOR:
            q = POSTERIOR[state]
            total += min(q, 1 - q) * Fraction(1, 2**depth)
    return total


def row_times_matrix(row, matrix):
    return tuple(
        sum(row[i] * matrix[i][j] for i in range(len(row)))
        for j in range(len(row))
    )


def transfer_error(depth, terminal_weights):
    row = S
    for _ in range(depth - 1):
        row = row_times_matrix(row, B)
    return sum(row[i] * terminal_weights[i] for i in range(len(row))) / 2 ** (
        depth - 1
    )


def main():
    terminal_weights = list(T)
    if "--inject-error" in sys.argv:
        terminal_weights[0] += Fraction(1, 100)

    for depth in range(1, 21):
        direct = direct_error(depth)
        transfer = transfer_error(depth, terminal_weights)
        assert direct == transfer, (
            f"depth {depth}: direct error {direct} != transfer value {transfer}"
        )

    print("verified exact scan-error transfer for depths 1 through 20")


if __name__ == "__main__":
    main()
