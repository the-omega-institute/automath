#!/usr/bin/env python3
"""Exact finite checks for eventual acyclicity and path-length indexing.

The theorem is proved algebraically in the article.  This verifier builds
the finite overlap graphs directly and checks representative apertures.
"""

from __future__ import annotations

from collections.abc import Callable
from itertools import product


Vertex = tuple[int, ...]


def recurrence(
    initial: tuple[int, ...], next_value: Callable[[list[int]], int], length: int
) -> list[int]:
    values = list(initial)
    while len(values) < length:
        values.append(next_value(values))
    return values


def overlap_graph(
    weights: list[int], coefficient_bound: int, aperture: int
) -> dict[Vertex, tuple[Vertex, ...]]:
    digits = range(-coefficient_bound, coefficient_bound + 1)
    vertices = list(product(digits, repeat=aperture - 1))
    modulus = weights[aperture]
    adjacency: dict[Vertex, tuple[Vertex, ...]] = {}
    for vertex in vertices:
        prefix_value = sum(
            weights[index] * coefficient
            for index, coefficient in enumerate(vertex)
        )
        targets = []
        for coefficient in digits:
            if (prefix_value + weights[aperture - 1] * coefficient) % modulus == 0:
                targets.append(vertex[1:] + (coefficient,))
        adjacency[vertex] = tuple(targets)
    return adjacency


def exact_longest_nonzero_path(adjacency: dict[Vertex, tuple[Vertex, ...]]) -> int:
    zero = (0,) * len(next(iter(adjacency)))
    predecessors = [source for source, targets in adjacency.items() if zero in targets]
    assert predecessors == [zero], predecessors
    assert adjacency[zero].count(zero) == 1

    active: set[Vertex] = set()
    memo: dict[Vertex, int] = {}

    def longest(vertex: Vertex) -> int:
        if vertex == zero:
            return 0
        if vertex in memo:
            return memo[vertex]
        assert vertex not in active, ("nonzero directed cycle", vertex)
        active.add(vertex)
        lengths = []
        for target in adjacency[vertex]:
            assert target != zero, ("nonzero predecessor of zero", vertex)
            lengths.append(1 + longest(target))
        active.remove(vertex)
        memo[vertex] = max(lengths, default=0)
        return memo[vertex]

    starts = [vertex for vertex in adjacency if vertex[0] != 0]
    return max(longest(vertex) for vertex in starts)


def assert_path_bound(longest_path: int, claimed_bound: int) -> None:
    assert longest_path <= claimed_bound, (longest_path, claimed_bound)


def main() -> None:
    theta_weights = recurrence(
        (1, 2, 4), lambda u: 2 * u[-1] - u[-2] + u[-3], 11
    )
    non_condition_f_weights = recurrence(
        (1, 3, 7), lambda u: 3 * u[-1] - 2 * u[-2] + u[-3], 9
    )

    passed = 0
    for aperture in range(4, 10):
        graph = overlap_graph(theta_weights, 1, aperture)
        longest_path = exact_longest_nonzero_path(graph)
        expected = 2 * (aperture // 2) - 2
        assert longest_path == expected, (aperture, longest_path, expected)
        assert_path_bound(longest_path, aperture)
        passed += 1
        print(
            f"PASS cubic m={aperture} longest={longest_path} "
            "nonzero_cycles=0"
        )

    for aperture in range(5, 8):
        graph = overlap_graph(non_condition_f_weights, 2, aperture)
        longest_path = exact_longest_nonzero_path(graph)
        assert_path_bound(longest_path, aperture)
        passed += 1
        print(
            f"PASS non-Condition-F m={aperture} longest={longest_path} "
            "nonzero_cycles=0"
        )

    # Sensitivity check: the exact cubic value at m=8 is six, so the
    # deliberately false bound five must be rejected by the same assertion.
    mutation_rejected = False
    try:
        assert_path_bound(6, 5)
    except AssertionError:
        mutation_rejected = True
    assert mutation_rejected
    passed += 1
    print("PASS sensitivity mutation longest<=5 at cubic m=8 rejected")
    print(f"PASS: {passed}/10 eventual-acyclicity checks")


if __name__ == "__main__":
    main()
