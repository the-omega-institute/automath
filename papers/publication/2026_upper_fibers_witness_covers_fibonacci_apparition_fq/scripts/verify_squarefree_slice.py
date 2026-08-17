#!/usr/bin/env python3
"""Verify the squarefree exact-fiber converse and weighted-cover sharpness."""

import argparse
import itertools
from functools import lru_cache
from pathlib import Path
from typing import Callable, Dict, FrozenSet, Iterable, Tuple

from sympy import divisors

try:
    from .verify_deepening_delta import (
        alpha_for_fn_divisor,
        factorint,
        factorint_fibonacci,
        fibonacci,
        upper_fiber_threshold,
    )
except ImportError:
    from verify_deepening_delta import (
        alpha_for_fn_divisor,
        factorint,
        factorint_fibonacci,
        fibonacci,
        upper_fiber_threshold,
    )


Subset = FrozenSet[int]
Cover = FrozenSet[Subset]


def _nonempty_subsets(size: int) -> Tuple[Subset, ...]:
    return tuple(
        frozenset(subset)
        for subset_size in range(1, size + 1)
        for subset in itertools.combinations(range(size), subset_size)
    )


@lru_cache(maxsize=None)
def minimal_covers(size: int) -> Tuple[Cover, ...]:
    """Enumerate irredundant covers of a labelled set of the given size."""
    if size < 1:
        raise ValueError("size must be positive")
    vertex_set = frozenset(range(size))
    subsets = _nonempty_subsets(size)
    covers = []
    for mask in range(1, 1 << len(subsets)):
        cover = frozenset(
            subsets[index]
            for index in range(len(subsets))
            if mask & (1 << index)
        )
        if frozenset().union(*cover) != vertex_set:
            continue
        if all(
            edge - frozenset().union(*(cover - {edge}))
            for edge in cover
        ):
            covers.append(cover)
    return tuple(covers)


def weighted_cover_partition(size: int, weights: Dict[Subset, int]) -> int:
    """Return the weighted partition function over irredundant covers."""
    subsets = _nonempty_subsets(size)
    if set(weights) != set(subsets) or any(weights[subset] < 1 for subset in subsets):
        raise ValueError("weights must be positive on every nonempty subset")
    return sum(
        _product(weights[edge] for edge in cover)
        for cover in minimal_covers(size)
    )


def _product(values: Iterable[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def sharp_mass_lower_bound(size: int, total_mass: int) -> int:
    """Return C_k + total_mass - (2^k - 1)."""
    baseline_mass = 2**size - 1
    if total_mass < baseline_mass:
        raise ValueError("positive weights require total_mass >= 2^size - 1")
    return len(minimal_covers(size)) + total_mass - baseline_mass


def extremal_full_support_profile(size: int, total_mass: int) -> Dict[Subset, int]:
    """Concentrate all mass above one on the full support."""
    subsets = _nonempty_subsets(size)
    baseline_mass = len(subsets)
    if total_mass < baseline_mass:
        raise ValueError("positive weights require total_mass >= 2^size - 1")
    weights = {subset: 1 for subset in subsets}
    weights[frozenset(range(size))] += total_mass - baseline_mass
    return weights


def squarefree_minimal_generators(n: int) -> Tuple[int, ...]:
    """Return the squarefree elements among the verified minimal generators."""
    result = upper_fiber_threshold(n)
    return tuple(
        value
        for value in result.minimal_generators
        if all(exponent == 1 for exponent in factorint(value).values())
    )


def prime_rank(prime: int) -> int:
    """Return the Fibonacci rank of a prime from the standard rank bound."""
    if prime == 2:
        return 3
    if prime == 5:
        return 5
    legendre_value = pow(5, (prime - 1) // 2, prime)
    legendre_symbol = -1 if legendre_value == prime - 1 else legendre_value
    return next(
        index
        for index in divisors(prime - legendre_symbol)
        if fibonacci(index) % prime == 0
    )


def ladder_obstruction_criterion(n: int) -> bool:
    """Return whether the theorem predicts a nonsquarefree member of M_n."""
    factors = {int(prime): int(exponent) for prime, exponent in factorint(n).items()}
    if n % 6 == 0 or factors.get(5, 0) >= 2:
        return True
    return any(
        (n // prime**exponent) % prime_rank(prime) == 0
        for prime, exponent in factors.items()
        if prime not in (2, 5)
    )


def verify_ladder_obstruction(
    n: int,
    obstruction_test: Callable[[int], bool] = ladder_obstruction_criterion,
) -> int:
    """Compare the criterion with direct enumeration; return nonsquarefree count."""
    generators = upper_fiber_threshold(n).minimal_generators
    nonsquarefree_count = sum(
        any(exponent > 1 for exponent in factorint(value).values())
        for value in generators
    )
    predicted = obstruction_test(n)
    if (nonsquarefree_count > 0) != predicted:
        raise AssertionError(
            f"ladder criterion failed at n={n}: "
            f"nonsquarefree_count={nonsquarefree_count}, predicted={predicted}"
        )
    return nonsquarefree_count


def _exact_rank_primes(n: int) -> Dict[int, Tuple[int, ...]]:
    primes_by_rank: Dict[int, list[int]] = {}
    for prime, _ in factorint_fibonacci(n):
        rank = alpha_for_fn_divisor(prime, n)
        primes_by_rank.setdefault(rank, []).append(prime)
    return {
        rank: tuple(sorted(primes))
        for rank, primes in primes_by_rank.items()
    }


def rank_pure_products(n: int) -> Tuple[int, ...]:
    """Construct the rank-pure products directly from exact-rank prime covers."""
    n_factors = factorint(n)
    if any(exponent != 1 for exponent in n_factors.values()):
        raise ValueError("rank-pure converse verifier requires squarefree n")
    coordinates = tuple(sorted(n_factors))
    primes_by_rank = _exact_rank_primes(n)
    products = set()
    for cover in minimal_covers(len(coordinates)):
        ranks = tuple(
            _product(coordinates[index] for index in support)
            for support in cover
        )
        choices = []
        fillable = True
        for rank in ranks:
            primes = primes_by_rank.get(rank, tuple())
            if not primes:
                fillable = False
                break
            choices.append(primes)
        if not fillable:
            continue
        for selected in itertools.product(*choices):
            products.add(_product(selected))
    return tuple(sorted(products))


def run_battery(max_index: int) -> str:
    """Run exhaustive combinatorial checks and squarefree Fibonacci comparisons."""
    if max_index < 30:
        raise ValueError("max_index must be at least 30")
    profile_checks = 0
    for size in range(1, 5):
        baseline_mass = 2**size - 1
        for excess in range(9):
            total_mass = baseline_mass + excess
            profile = extremal_full_support_profile(size, total_mass)
            actual = weighted_cover_partition(size, profile)
            expected = sharp_mass_lower_bound(size, total_mass)
            if actual != expected:
                raise AssertionError(
                    f"sharp profile failed for size={size}, mass={total_mass}"
                )
            profile_checks += 1

    checked_indices = []
    checked_elements = 0
    for n in range(3, max_index + 1):
        if any(exponent != 1 for exponent in factorint(n).values()):
            continue
        expected = squarefree_minimal_generators(n)
        actual = rank_pure_products(n)
        if actual != expected:
            raise AssertionError(
                f"squarefree slice failed at n={n}: {actual} != {expected}"
            )
        checked_indices.append(n)
        checked_elements += len(actual)

    criterion_checks = 0
    obstructed_indices = 0
    nonsquarefree_elements = 0
    for n in range(3, max_index + 1):
        count = verify_ladder_obstruction(n)
        criterion_checks += 1
        obstructed_indices += count > 0
        nonsquarefree_elements += count

    lines = [
        "Squarefree-fiber and weighted-cover verification",
        "=================================================",
        "Weighted minimal-cover equality profiles: sizes 1 <= k <= 4,",
        "  excess masses 0 <= E <= 8",
        f"  exact equality checks = {profile_checks}",
        f"Squarefree Fibonacci indices: 3 <= n <= {max_index}",
        f"  indices checked = {len(checked_indices)}",
        f"  rank-pure/squarefree set equalities = {len(checked_indices)}",
        f"  squarefree minimal generators compared = {checked_elements}",
        f"Squarefree-fiber criterion: 3 <= n <= {max_index}",
        f"  direct/criterion equivalences = {criterion_checks}",
        f"  indices with ladder obstructions = {obstructed_indices}",
        f"  nonsquarefree minimal generators found = {nonsquarefree_elements}",
        "RESULT: PASS (0 failures / 0 counterexamples)",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=210)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/squarefree_slice_verification.txt"),
    )
    args = parser.parse_args()
    report = run_battery(args.max_index)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="ascii", newline="\n")
    print(report, end="")
    print(f"Saved report: {args.output}")


if __name__ == "__main__":
    main()
