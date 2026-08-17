#!/usr/bin/env python3
"""Verify the exact minimal equitable refinement of the window-6 fold.

Run from the paper root:
    python artifacts/verify_hidden_refinement.py

The negative control intentionally corrupts one claimed cell and must fail:
    python artifacts/verify_hidden_refinement.py --inject-error
"""
from itertools import product
import sys


FIB = [0, 1]
while len(FIB) < 100:
    FIB.append(FIB[-1] + FIB[-2])


def zprefix(value, width=6):
    digits = [0] * 100
    remainder = value
    while remainder:
        index = max(i for i in range(1, 90) if FIB[i + 1] <= remainder)
        digits[index - 1] = 1
        remainder -= FIB[index + 1]
    return "".join(map(str, digits[:width]))


def sigma_geo(word):
    bits = list(map(int, word))
    return "".join(
        map(str, [1 - bits[4], bits[1], bits[2], bits[3], 1 - bits[0], bits[5]])
    )


EXPECTED_CELLS = (
    ("000000", "100010"),
    ("010101", "110111"),
    ("001101", "101111"),
    ("001000", "101010"),
    ("011101", "111111"),
    ("000101", "100111"),
    ("011010",),
    ("111100",),
    ("010010",),
    ("110100",),
    ("000011",),
    ("011000", "111010"),
    ("100101",),
    ("010000", "110010"),
    ("001011",),
    ("100000",),
    ("101101",),
    ("000010",),
    ("010111",),
    ("100100",),
    ("111001",),
    ("001111",),
    ("110001",),
    ("001010",),
    ("011111",),
    ("101100",),
    ("000111",),
    ("011100", "111110"),
    ("101001",),
    ("010100", "110110"),
    ("000001", "100011"),
    ("010110",),
    ("111000",),
    ("001110",),
    ("110000",),
    ("001001", "101011"),
    ("011110",),
    ("000110",),
    ("011011",),
    ("101000",),
    ("111101",),
    ("010011",),
    ("110101",),
    ("000100", "100110"),
    ("011001", "111011"),
    ("010001", "110011"),
    ("001100", "101110"),
    ("100001",),
)


def canonical(partition):
    return tuple(sorted(tuple(sorted(cell)) for cell in partition))


def neighbor_signature(word, targets):
    value = int(word, 2)
    counts = {target: 0 for target in targets}
    for coordinate in range(6):
        counts[zprefix(value ^ (1 << coordinate))] += 1
    return tuple(counts[target] for target in targets)


def verify(expected_cells):
    errors = []
    vertices = ["".join(bits) for bits in product("01", repeat=6)]
    targets = sorted({zprefix(int(word, 2)) for word in vertices})

    fibers = {target: [] for target in targets}
    for word in vertices:
        fibers[zprefix(int(word, 2))].append(word)

    signature_cells = []
    for target in targets:
        classes = {}
        for word in fibers[target]:
            signature = neighbor_signature(word, targets)
            classes.setdefault(signature, []).append(word)
        signature_cells.extend(classes.values())

    orbit_cells = []
    unseen = set(vertices)
    while unseen:
        word = min(unseen)
        cell = {word, sigma_geo(word)}
        orbit_cells.append(cell)
        unseen -= cell

    expected = canonical(expected_cells)
    if expected != canonical(signature_cells):
        errors.append("neighbor-signature classes differ from the claimed 48 cells")
    if expected != canonical(orbit_cells):
        errors.append("claimed cells differ from the sigma_geo orbit partition")

    flattened = [word for cell in expected_cells for word in cell]
    if len(flattened) != 64 or set(flattened) != set(vertices):
        errors.append("claimed cells do not partition all 64 vertices exactly once")

    for cell in orbit_cells:
        if len({zprefix(int(word, 2)) for word in cell}) != 1:
            errors.append("a sigma_geo orbit crosses a Fold_6 fiber")

    orbit_partition = [set(cell) for cell in orbit_cells]
    for cell in orbit_partition:
        reference = None
        for word in cell:
            counts = tuple(
                sum((int(word, 2) ^ (1 << coordinate)) in {int(v, 2) for v in target}
                    for coordinate in range(6))
                for target in orbit_partition
            )
            if reference is None:
                reference = counts
            elif counts != reference:
                errors.append("sigma_geo orbit partition is not equitable")

    sizes = sorted(map(len, orbit_partition))
    if sizes != [1] * 32 + [2] * 16:
        errors.append("orbit-size distribution is not 32 singletons and 16 pairs")
    return errors


def main():
    expected = list(EXPECTED_CELLS)
    if "--inject-error" in sys.argv:
        expected[0] = ("000000",)
    errors = verify(expected)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("window6 hidden refinement certificate: all assertions passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
