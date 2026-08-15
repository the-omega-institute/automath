#!/usr/bin/env python3
"""Exact finite verification for the simple-Parry causal obstructions.

All collision calculations use integer arithmetic.  A tuple ``digits`` is the
finite greedy expansion d_beta(1)=t_1...t_p 0^infinity.
"""

from __future__ import annotations

import argparse
import sys
from contextlib import redirect_stdout
from io import StringIO
from itertools import product
from pathlib import Path


def cubic_family_digits(n: int) -> tuple[int, ...]:
    """Return the finite Parry word for the cubic family indexed by ``n``."""
    if n < 4:
        raise ValueError("the cubic family begins at n=4")
    return tuple(
        [n]
        + list(range(1, n - 1))
        + [n, 1, 0]
        + list(range(n - 1, 1, -1))
        + [0, n]
    )


def cubic_family_q_sequence(n: int, maximum: int) -> list[int]:
    """Return the cubic-family language counts through ``maximum``."""
    return q_sequence(cubic_family_digits(n), maximum)


def cubic_family_extremal_vector(n: int, aperture: int) -> tuple[int, ...]:
    """Return the extremal length-(aperture-1) collision path."""
    if n < 4 or not 2 <= aperture <= n - 1:
        raise ValueError("require n>=4 and 2<=aperture<=n-1")
    if aperture == 2:
        return (2, n)
    padding = aperture - 3
    return tuple(
        [-2] * padding + [n - 2, -2, -n, 1] + [0] * padding
    )


def _polynomial_product(left: list[int], right: list[int]) -> list[int]:
    """Multiply low-to-high integer coefficient lists."""
    result = [0] * (len(left) + len(right) - 1)
    for i, left_coefficient in enumerate(left):
        for j, right_coefficient in enumerate(right):
            result[i + j] += left_coefficient * right_coefficient
    return result


def cubic_family_claims(n: int) -> dict[str, bool | int]:
    """Check the Parry factorization and suffix inequalities for one index."""
    digits = cubic_family_digits(n)
    parry = [-digit for digit in reversed(digits)] + [1]
    minimal = [-n, 2 * n, -(n + 2), 1]
    geometric_n = [1] * n
    geometric_n1 = [1] * (n + 1)
    factored = _polynomial_product(
        _polynomial_product(minimal, geometric_n), geometric_n1
    )

    boundary = digits + (0,) * len(digits)
    suffixes_are_smaller = all(
        digits[start:] + (0,) * (len(digits) + start) < boundary
        for start in range(1, len(digits))
    )
    return {
        "parry_factorization": parry == factored,
        "proper_suffixes_are_smaller": suffixes_are_smaller,
        "parry_length": len(digits),
    }


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


def _collision_graph(
    digits: tuple[int, ...], m: int
) -> dict[tuple[int, ...], tuple[tuple[int, ...], ...]]:
    """Build the bounded-difference collision graph at aperture ``m``."""
    if m < 2:
        raise ValueError("the collision graph requires m>=2")
    d = digits[0]
    q = q_sequence(digits, m)
    modulus = q[m]
    vertices = product(range(-d, d + 1), repeat=m - 1)
    adjacency: dict[tuple[int, ...], tuple[tuple[int, ...], ...]] = {}
    for vertex in vertices:
        following = []
        for appended in range(-d, d + 1):
            weighted = sum(q[j] * vertex[j] for j in range(m - 1))
            weighted += q[m - 1] * appended
            if weighted % modulus == 0:
                following.append(vertex[1:] + (appended,))
        adjacency[vertex] = tuple(following)
    return adjacency


def _reachable_cycle(
    adjacency: dict[tuple[int, ...], tuple[tuple[int, ...], ...]],
    starts: list[tuple[int, ...]],
) -> tuple[int, ...] | None:
    """Return the first-coordinate word on a cycle reachable from ``starts``."""
    color: dict[tuple[int, ...], int] = {}
    parent: dict[tuple[int, ...], tuple[int, ...]] = {}

    def visit(vertex: tuple[int, ...]) -> tuple[int, ...] | None:
        color[vertex] = 1
        for following in adjacency[vertex]:
            if color.get(following, 0) == 0:
                parent[following] = vertex
                witness = visit(following)
                if witness is not None:
                    return witness
            elif color[following] == 1:
                reverse_cycle = [vertex]
                while reverse_cycle[-1] != following:
                    reverse_cycle.append(parent[reverse_cycle[-1]])
                cycle = tuple(reversed(reverse_cycle))
                return tuple(state[0] for state in cycle)
        color[vertex] = 2
        return None

    for start in starts:
        if color.get(start, 0) == 0:
            witness = visit(start)
            if witness is not None:
                return witness
    return None


def collision_graph_analysis(
    digits: tuple[int, ...], m: int
) -> dict[str, int | bool | tuple[int, ...] | None]:
    """Return the exact injectivity, causal-depth, and cycle certificates."""
    adjacency = _collision_graph(digits, m)
    zero = (0,) * (m - 1)
    starts = [vertex for vertex in adjacency if vertex[0] != 0]
    zero_predecessors = [vertex for vertex, targets in adjacency.items() if zero in targets]
    periodic_witness = _reachable_cycle(adjacency, starts)
    if periodic_witness is not None and periodic_witness[0] < 0:
        periodic_witness = tuple(-entry for entry in periodic_witness)
    injective = periodic_witness is None

    causal_length = None
    if injective:
        longest_cache: dict[tuple[int, ...], int] = {}

        def longest_path(vertex: tuple[int, ...]) -> int:
            if vertex not in longest_cache:
                longest_cache[vertex] = max(
                    (1 + longest_path(target) for target in adjacency[vertex]),
                    default=0,
                )
            return longest_cache[vertex]

        causal_length = 1 + max(longest_path(start) for start in starts)

    return {
        "injective": injective,
        "causal_length": causal_length,
        "periodic_witness": periodic_witness,
        "zero_predecessor_is_unique": zero_predecessors == [zero],
        "state_bound": len(adjacency) - 1,
    }


def aperture_two_claims(
    digits: tuple[int, ...],
) -> dict[str, int | str | tuple[int, ...] | None]:
    """Classify aperture two by the second-digit boundary parameter."""
    if len(digits) < 2:
        raise ValueError("the aperture-two classification requires Parry order p>=2")
    d = digits[0]
    boundary = digits[1] + (1 if len(digits) > 2 else 0)
    analysis = collision_graph_analysis(digits, 2)
    if boundary == d + 1:
        regime = "local_bijection"
    elif boundary == d:
        regime = "constant_branch_pair"
    else:
        regime = "two_output_inverse"
    return {
        "boundary_parameter": boundary,
        "regime": regime,
        "causal_length": analysis["causal_length"],
        "periodic_witness": analysis["periodic_witness"],
    }


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


def theta_terminal_vector(m: int) -> tuple[int, ...]:
    """Return the positive-first extremal word E_m for the fixed cubic base."""
    if m < 4:
        raise ValueError("the fixed-theta theorem begins at aperture m=4")
    even_aperture = m if m % 2 == 0 else m - 1
    core = (1, -1, -1, -1, 1)
    for aperture in range(6, even_aperture + 1, 2):
        core = (1, 0) + tuple(-entry for entry in core)
        if len(core) != aperture + 1:
            raise AssertionError("the two-step terminal recursion lost its aperture")
    vector = core + (0,) * (even_aperture - 4)
    if m % 2:
        vector += (0,)
    return vector


def theta_terminal_claims(m: int) -> dict[str, int | bool]:
    """Check the exact fixed-theta terminal obstruction at one aperture."""
    if m < 4:
        raise ValueError("the fixed-theta theorem begins at aperture m=4")
    digits = (1, 1, 0, 1)
    causal_length = 2 * (m // 2) - 1
    analysis = collision_graph_analysis(digits, m)
    return {
        "terminal_count": collision_graph_bad_path_count(
            digits, m, causal_length - 1
        ),
        "next_count": collision_graph_bad_path_count(digits, m, causal_length),
        "causal_length": analysis["causal_length"],
        "injective": analysis["injective"],
    }


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


def non_pisot_simple_parry_claims() -> dict[str, object]:
    """Verify the strict non-Pisot witness d_beta(1)=2002 0^infinity."""
    digits = (2, 0, 0, 2)
    boundary = digits + (0,) * len(digits)
    parry_admissible = all(
        digits[start:] + (0,) * (len(digits) + start) < boundary
        for start in range(1, len(digits))
    )

    def bisect_root(function, left: float, right: float) -> float:
        for _ in range(80):
            midpoint = (left + right) / 2
            if function(midpoint) > 0:
                right = midpoint
            else:
                left = midpoint
        return (left + right) / 2

    beta = bisect_root(lambda x: x**4 - 2 * x**3 - 2, 2.0, 2.2)
    negative_root_modulus = bisect_root(lambda x: x**4 + 2 * x**3 - 2, 0.0, 1.0)
    complex_root_modulus = (2 / (beta * negative_root_modulus)) ** 0.5
    aperture_two = collision_graph_analysis(digits, 2)
    return {
        "digits": digits,
        "parry_admissible": parry_admissible,
        "is_pisot": complex_root_modulus < 1,
        "largest_nondominant_modulus": max(
            negative_root_modulus, complex_root_modulus
        ),
        "q_prefix": q_sequence(digits, 6),
        "rank_checks": [rank_is_consecutive(digits, m) for m in range(1, 7)],
        "aperture_two_causal_length": aperture_two["causal_length"],
    }


def _run_verification() -> int:
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
    print("Causal-completeness and aperture-two classification battery:")
    aperture_two_cases = {
        (1, 1, 1): ("local_bijection", 1, None),
        (2, 0, 1): ("two_output_inverse", 2, None),
        (1, 0, 1): ("constant_branch_pair", None, (1,)),
        (2, 1): ("two_output_inverse", 2, None),
        (2, 2): ("constant_branch_pair", None, (2,)),
    }
    for digits, expected in aperture_two_cases.items():
        result = aperture_two_claims(digits)
        got = (result["regime"], result["causal_length"], result["periodic_witness"])
        analysis = collision_graph_analysis(digits, 2)
        passed = got == expected and analysis["zero_predecessor_is_unique"]
        status = "PASS" if passed else "FAIL"
        print(f"  t={digits}: c={result['boundary_parameter']}, {got} [{status}]")
        failures += not passed

    global_cases = (((1, 1, 1), 4), ((1, 0, 1), 3), ((1, 0, 1), 4))
    for digits, m in global_cases:
        result = collision_graph_analysis(digits, m)
        certificate_ok = result["zero_predecessor_is_unique"]
        if result["injective"]:
            certificate_ok &= result["causal_length"] <= result["state_bound"]
        else:
            witness = result["periodic_witness"]
            certificate_ok &= witness is not None
            certificate_ok &= len(witness) <= result["state_bound"]
            certificate_ok &= periodic_collision(digits, m, witness)
        status = "PASS" if certificate_ok else "FAIL"
        print(f"  t={digits}, m={m}: {result} [{status}]")
        failures += not certificate_ok

    print()
    non_pisot = non_pisot_simple_parry_claims()
    non_pisot_passed = (
        non_pisot["parry_admissible"]
        and not non_pisot["is_pisot"]
        and non_pisot["largest_nondominant_modulus"] > 1
        and all(non_pisot["rank_checks"])
        and non_pisot["aperture_two_causal_length"] == 2
    )
    print("Pisot-hypothesis removal battery:")
    print(
        "  d_beta(1)=2002 0^infinity: "
        f"max nondominant modulus={non_pisot['largest_nondominant_modulus']:.12f}, "
        f"m=2 causal={non_pisot['aperture_two_causal_length']} "
        f"[{'PASS' if non_pisot_passed else 'FAIL'}]"
    )
    failures += not non_pisot_passed

    print()
    print("Unbounded cubic causal-depth battery:")
    for n in range(4, 7):
        digits = cubic_family_digits(n)
        aperture = n - 1
        family = cubic_family_claims(n)
        analysis = collision_graph_analysis(digits, aperture)
        terminal_counts = (
            collision_graph_bad_path_count(digits, aperture, aperture - 1),
            collision_graph_bad_path_count(digits, aperture, aperture),
        )
        passed = (
            family["parry_factorization"]
            and family["proper_suffixes_are_smaller"]
            and analysis["injective"]
            and analysis["causal_length"] == aperture
            and terminal_counts == (2, 0)
        )
        status = "PASS" if passed else "FAIL"
        print(
            f"  n={n}, m={aperture}: causal={analysis['causal_length']}, "
            f"terminal paths={terminal_counts} [{status}]"
        )
        failures += not passed

    print()
    print("Fixed binary cubic sharpness battery:")
    for aperture in range(4, 11):
        result = theta_terminal_claims(aperture)
        expected_length = 2 * (aperture // 2) - 1
        passed = result == {
            "terminal_count": 2,
            "next_count": 0,
            "causal_length": expected_length,
            "injective": True,
        }
        status = "PASS" if passed else "FAIL"
        print(
            f"  m={aperture}: causal={result['causal_length']}, "
            f"terminal paths=({result['terminal_count']}, "
            f"{result['next_count']}) [{status}]"
        )
        failures += not passed

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
