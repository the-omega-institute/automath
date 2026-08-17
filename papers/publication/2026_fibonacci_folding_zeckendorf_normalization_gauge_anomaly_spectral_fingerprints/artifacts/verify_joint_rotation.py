#!/usr/bin/env python3
"""Verify the joint output-discrepancy rotation polygon and its frontiers."""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import permutations


STATES = ("a", "b", "c", "d")
EDGES = (
    ("a", "a", 0, 0, "00"),
    ("a", "b", 1, 1, "01"),
    ("a", "d", 1, 0, "11"),
    ("b", "c", 0, 1, "10"),
    ("c", "a", 0, 1, "10"),
    ("c", "b", 0, 0, "00"),
    ("c", "b", 1, 0, "11"),
    ("d", "a", 0, 0, "00"),
)

EXPECTED_VECTORS = {
    (Fraction(0), Fraction(0)),
    (Fraction(1, 2), Fraction(0)),
    (Fraction(1, 2), Fraction(1, 2)),
    (Fraction(1, 3), Fraction(1)),
    (Fraction(0), Fraction(1, 2)),
}

EXPECTED_HULL = (
    (Fraction(0), Fraction(0)),
    (Fraction(1, 2), Fraction(0)),
    (Fraction(1, 2), Fraction(1, 2)),
    (Fraction(1, 3), Fraction(1)),
    (Fraction(0), Fraction(1, 2)),
)


def canonical_cycle(edge_ids: tuple[int, ...]) -> tuple[int, ...]:
    rotations = (
        edge_ids[index:] + edge_ids[:index] for index in range(len(edge_ids))
    )
    return min(rotations)


def canonical_labels(labels: tuple[str, ...]) -> tuple[str, ...]:
    rotations = (labels[index:] + labels[:index] for index in range(len(labels)))
    return min(rotations)


def simple_cycles(edges: tuple[tuple[str, str, int, int, str], ...]):
    cycles: dict[tuple[int, ...], tuple[Fraction, Fraction, tuple[str, ...]]] = {}

    for start in STATES:
        def visit(vertex: str, seen: frozenset[str], path: tuple[int, ...]) -> None:
            for edge_id, edge in enumerate(edges):
                source, target, output, discrepancy, label = edge
                if source != vertex:
                    continue
                if target == start:
                    edge_path = path + (edge_id,)
                    key = canonical_cycle(edge_path)
                    length = len(edge_path)
                    cycles[key] = (
                        Fraction(sum(edges[item][2] for item in edge_path), length),
                        Fraction(sum(edges[item][3] for item in edge_path), length),
                        canonical_labels(tuple(edges[item][4] for item in edge_path)),
                    )
                elif target not in seen:
                    visit(target, seen | {target}, path + (edge_id,))

        visit(start, frozenset({start}), ())

    return tuple(cycles.values())


def cross(origin, first, second):
    return (
        (first[0] - origin[0]) * (second[1] - origin[1])
        - (first[1] - origin[1]) * (second[0] - origin[0])
    )


def convex_hull(points):
    ordered = sorted(set(points))
    lower = []
    for point in ordered:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], point) <= 0:
            lower.pop()
        lower.append(point)
    upper = []
    for point in reversed(ordered):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], point) <= 0:
            upper.pop()
        upper.append(point)
    return tuple(lower[:-1] + upper[:-1])


def polynomial_add(left, right):
    size = max(len(left), len(right))
    result = [0] * size
    for index in range(size):
        result[index] = (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
        )
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def polynomial_multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return tuple(result)


def permutation_sign(permutation):
    inversions = sum(
        permutation[left] > permutation[right]
        for left in range(len(permutation))
        for right in range(left + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


def characteristic_polynomial(matrix):
    size = len(matrix)
    total = (0,)
    for permutation in permutations(range(size)):
        term = (permutation_sign(permutation),)
        for row, column in enumerate(permutation):
            entry = (-matrix[row][column], 1) if row == column else (-matrix[row][column],)
            term = polynomial_multiply(term, entry)
        total = polynomial_add(total, term)
    return total


def boolean_product(left, right):
    size = len(left)
    return tuple(
        tuple(
            int(any(left[row][mid] and right[mid][column] for mid in range(size)))
            for column in range(size)
        )
        for row in range(size)
    )


def verify(edges) -> None:
    cycles = simple_cycles(edges)
    vectors = {(output, discrepancy) for output, discrepancy, _ in cycles}
    assert vectors == EXPECTED_VECTORS, (vectors, EXPECTED_VECTORS)

    hull = convex_hull(vectors)
    assert hull == EXPECTED_HULL, (hull, EXPECTED_HULL)

    for output, discrepancy in vectors:
        assert discrepancy <= Fraction(1, 2) + Fraction(3, 2) * output
        assert discrepancy <= 2 - 3 * output

    left_maximizers = {
        labels
        for output, discrepancy, labels in cycles
        if discrepancy - Fraction(3, 2) * output == Fraction(1, 2)
    }
    right_maximizers = {
        labels
        for output, discrepancy, labels in cycles
        if discrepancy + 3 * output == 2
    }
    assert left_maximizers == {("00", "10"), ("01", "10", "10")}
    assert right_maximizers == {("10", "11"), ("01", "10", "10")}

    frontier = (
        (0, 1, 0),
        (0, 0, 1),
        (1, 1, 0),
    )
    assert characteristic_polynomial(frontier) == (-1, -1, 0, 1)
    power = frontier
    assert not all(all(row) for row in power)
    for _ in range(1, 5):
        power = boolean_product(power, frontier)
        if all(all(row) for row in power):
            break
    else:
        raise AssertionError("frontier adjacency matrix is not primitive")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--negative-control",
        action="store_true",
        help="remove one frontier edge so the theorem checks fail",
    )
    arguments = parser.parse_args()

    edges = EDGES
    if arguments.negative_control:
        edges = tuple(edge for edge in EDGES if edge != ("c", "b", 1, 0, "11"))

    verify(edges)
    print("joint rotation polygon and plastic frontiers verified")


if __name__ == "__main__":
    main()
