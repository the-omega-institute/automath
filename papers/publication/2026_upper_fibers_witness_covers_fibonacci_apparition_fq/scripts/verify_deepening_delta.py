#!/usr/bin/env python3
"""Verify the manuscript's finite claims by exact computations.

The script uses two independent routes on an initial range:

1. enumerate every divisor of F_n and test its rank directly;
2. use B_n = Div(F_n) minus the union of Div(F_{n/p}), compute #B_n by
   inclusion-exclusion, and obtain its minimal elements as minimal threshold
   covers of the prime coordinates of n.

The second route is used on a larger range for the explicit counterexample
search. All arithmetic is exact; no external factor table is used.
"""

from __future__ import annotations

import argparse
import itertools
import math
import platform
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, Optional, Sequence, Tuple

from sympy import __version__ as sympy_version
from sympy import factorint


@dataclass(frozen=True)
class BirthLayerResult:
    n: int
    fibonacci: int
    a_count: int
    minimal_generators: Tuple[int, ...]
    birth_layer: Optional[Tuple[int, ...]] = None


@lru_cache(maxsize=None)
def fibonacci(n: int) -> int:
    """Return F_n by fast doubling."""
    if n < 0:
        raise ValueError("n must be nonnegative")

    def doubling(k: int) -> Tuple[int, int]:
        if k == 0:
            return 0, 1
        a, b = doubling(k // 2)
        c = a * (2 * b - a)
        d = a * a + b * b
        return (d, c + d) if k % 2 else (c, d)

    return doubling(n)[0]


@lru_cache(maxsize=None)
def factorint_fibonacci(n: int) -> Tuple[Tuple[int, int], ...]:
    """Return the exact factorization of F_n as an immutable tuple."""
    return tuple(sorted((int(p), int(e)) for p, e in factorint(fibonacci(n)).items()))


def _factorization_text(factors: Sequence[Tuple[int, int]]) -> str:
    if not factors:
        return "1"
    return "*".join(
        str(prime) if exponent == 1 else f"{prime}^{exponent}"
        for prime, exponent in factors
    )


def write_factorization_archive(path: Path, max_n: int) -> None:
    """Write the exact Fibonacci factorizations used by the verification."""
    if max_n < 2:
        raise ValueError("max_n must be at least 2")
    lines = [
        "# python_version\tsympy_version",
        f"# {platform.python_version()}\t{sympy_version}",
        "n\tF_n\tfactorization",
    ]
    for n in range(2, max_n + 1):
        lines.append(
            f"{n}\t{fibonacci(n)}\t{_factorization_text(factorint_fibonacci(n))}"
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="ascii", newline="\n")


def load_factorization_archive(
    path: Path, expected_max_n: int
) -> Dict[int, Tuple[Tuple[int, int], ...]]:
    """Load an archive and verify every factorization against F_n."""
    rows: Dict[int, Tuple[Tuple[int, int], ...]] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("#") or line.startswith("n\t"):
            continue
        n_text, value_text, factors_text = line.split("\t")
        n = int(n_text)
        factors = []
        if factors_text != "1":
            for item in factors_text.split("*"):
                if "^" in item:
                    prime_text, exponent_text = item.split("^", 1)
                    factors.append((int(prime_text), int(exponent_text)))
                else:
                    factors.append((int(item), 1))
        frozen = tuple(factors)
        reconstructed = math.prod(prime**exponent for prime, exponent in frozen)
        if int(value_text) != fibonacci(n) or reconstructed != fibonacci(n):
            raise ValueError(f"invalid factorization archive row for n={n}")
        rows[n] = frozen
    expected = set(range(2, expected_max_n + 1))
    if set(rows) != expected:
        raise ValueError("factorization archive does not contain the expected range")
    return rows


def factor_dict(items: Sequence[Tuple[int, int]]) -> Dict[int, int]:
    return dict(items)


def omega(n: int) -> int:
    """Return the number of distinct prime factors of n."""
    if n <= 1:
        return 0
    return len(factorint(n))


def omega_big(factors: Sequence[Tuple[int, int]]) -> int:
    """Return Omega(N) from the factorization of N."""
    return sum(e for _, e in factors)


def prime_divisors(n: int) -> Tuple[int, ...]:
    return tuple(sorted(int(p) for p in factorint(n)))


def valuation(value: int, prime: int) -> int:
    """Return the prime-adic valuation of a positive integer."""
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def divisors_from_factorization(
    factors: Sequence[Tuple[int, int]],
) -> Tuple[int, ...]:
    divisors = [1]
    for prime, exponent in factors:
        powers = [prime**e for e in range(exponent + 1)]
        divisors = [d * power for d in divisors for power in powers]
    return tuple(sorted(divisors))


def alpha_for_fn_divisor(q: int, n: int) -> int:
    """Compute alpha(q), given q | F_n, by testing the divisors of n."""
    if q == 1:
        return 1
    for d in divisors_from_factorization(tuple(sorted(factorint(n).items()))):
        if fibonacci(d) % q == 0:
            return d
    raise AssertionError(f"{q} does not divide F_{n}")


def minimal_elements(values: Iterable[int]) -> Tuple[int, ...]:
    minima = []
    for value in sorted(set(values)):
        if not any(value % earlier == 0 for earlier in minima):
            minima.append(value)
    return tuple(minima)


@lru_cache(maxsize=None)
def upper_fiber_exhaustive(n: int) -> BirthLayerResult:
    """Enumerate Div(F_n), compute B_n by ranks, and minimize it."""
    if n < 2:
        raise ValueError("birth layers in this paper require n >= 2")
    fn = fibonacci(n)
    divisors = divisors_from_factorization(factorint_fibonacci(n))
    birth_layer = tuple(
        q for q in divisors if q >= 2 and alpha_for_fn_divisor(q, n) == n
    )

    # Independently check the upper-fiber identity on every divisor.
    maximal_proper_fibonacci = tuple(fibonacci(n // p) for p in prime_divisors(n))
    upper_fiber = tuple(
        q
        for q in divisors
        if q >= 2 and all(previous % q != 0 for previous in maximal_proper_fibonacci)
    )
    if birth_layer != upper_fiber:
        raise AssertionError(f"upper-fiber identity failed at n={n}")

    return BirthLayerResult(
        n=n,
        fibonacci=fn,
        a_count=len(birth_layer),
        minimal_generators=minimal_elements(birth_layer),
        birth_layer=birth_layer,
    )


def divisor_count_inside_fn(value: int, fn_factors: Sequence[Tuple[int, int]]) -> int:
    """Return tau(value), knowing value divides the factored F_n."""
    count = 1
    remaining = value
    for prime, _ in fn_factors:
        exponent = valuation(remaining, prime)
        if exponent:
            remaining //= prime**exponent
        count *= exponent + 1
    if remaining != 1:
        raise AssertionError("value contains a prime absent from F_n")
    return count


@lru_cache(maxsize=None)
def upper_fiber_threshold(n: int) -> BirthLayerResult:
    """Compute #B_n and M_n from the upper-fiber threshold constraints."""
    if n < 2:
        raise ValueError("birth layers in this paper require n >= 2")
    fn = fibonacci(n)
    fn_factors = factorint_fibonacci(n)
    coordinates = prime_divisors(n)
    if not fn_factors:
        return BirthLayerResult(n, fn, 0, tuple(), None)

    # A(n) by inclusion-exclusion over the covering ideals D_{n/p}.
    a_count = 0
    for size in range(len(coordinates) + 1):
        for chosen in itertools.combinations(coordinates, size):
            divisor = math.prod(chosen)
            index = n // divisor
            term = divisor_count_inside_fn(fibonacci(index), fn_factors)
            a_count += -term if size % 2 else term

    # For each coordinate ell | n, q lies outside D_{n/ell} exactly when
    # one prime exponent of q exceeds its exponent in F_{n/ell}.
    choices = []
    for ell in coordinates:
        previous = fibonacci(n // ell)
        coordinate_choices = []
        for prime, exponent in fn_factors:
            threshold = valuation(previous, prime) + 1
            if threshold <= exponent:
                coordinate_choices.append((prime, threshold))
        if not coordinate_choices:
            raise AssertionError(f"coordinate {ell} has no witness at n={n}")
        choices.append(tuple(coordinate_choices))

    candidates = set()
    for selection in itertools.product(*choices):
        exponents: Dict[int, int] = {}
        for prime, threshold in selection:
            exponents[prime] = max(exponents.get(prime, 0), threshold)
        candidate = math.prod(prime**exponent for prime, exponent in exponents.items())
        candidates.add(candidate)

    minima = minimal_elements(candidates)
    return BirthLayerResult(n, fn, a_count, minima, None)


def _support_pairs(m: int, n: int):
    n_factorization = factor_dict(tuple(sorted((int(p), int(e)) for p, e in factorint(n).items())))
    coordinates = tuple(n_factorization)
    pairs = []
    for prime, exponent in sorted((int(p), int(e)) for p, e in factorint(m).items()):
        theta = prime**exponent
        lowered = prime ** (exponent - 1)
        rank = alpha_for_fn_divisor(theta, n)
        lower_rank = alpha_for_fn_divisor(lowered, n)
        full = frozenset(
            i
            for i, ell in enumerate(coordinates)
            if valuation(rank, ell) == n_factorization[ell]
        )
        essential = frozenset(
            i
            for i in full
            if valuation(lower_rank, coordinates[i]) < n_factorization[coordinates[i]]
        )
        pairs.append((essential, full))
    return tuple(pairs)


def _normalized_pairs(pairs) -> Tuple[Tuple[Tuple[int, ...], Tuple[int, ...]], ...]:
    return tuple(
        sorted((tuple(sorted(essential)), tuple(sorted(full))) for essential, full in pairs)
    )


def classify_support_three(m: int, n: int) -> str:
    """Classify a support-three minimal generator into Gamma_1,...,Gamma_9."""
    if omega(n) != 3:
        raise ValueError("support-three classification requires omega(n) = 3")
    actual = _normalized_pairs(_support_pairs(m, n))
    templates = {
        "Gamma_1": [({0, 1, 2}, {0, 1, 2})],
        "Gamma_2": [({0, 1}, {0, 1, 2})],
        "Gamma_3": [({0}, {0, 1, 2})],
        "Gamma_4": [({0, 1}, {0, 1}), ({1, 2}, {1, 2})],
        "Gamma_5": [({0}, {0, 1}), ({1, 2}, {1, 2})],
        "Gamma_6": [({0}, {0, 1}), ({2}, {1, 2})],
        "Gamma_7": [({0}, {0}), ({1, 2}, {1, 2})],
        "Gamma_8": [({0}, {0}), ({1}, {1, 2})],
        "Gamma_9": [({0}, {0}), ({1}, {1}), ({2}, {2})],
    }
    matches = []
    for label, template in templates.items():
        for permutation in itertools.permutations(range(3)):
            permuted = [
                (
                    frozenset(permutation[i] for i in essential),
                    frozenset(permutation[i] for i in full),
                )
                for essential, full in template
            ]
            if _normalized_pairs(permuted) == actual:
                matches.append(label)
                break
    if len(matches) != 1:
        raise AssertionError(f"expected one Gamma type for m={m}, n={n}; got {matches}")
    return matches[0]


def bell_number(k: int) -> int:
    """Return the kth Bell number using the Bell triangle."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    row = [1]
    for _ in range(k):
        next_row = [row[-1]]
        for value in row:
            next_row.append(next_row[-1] + value)
        row = next_row
    return row[0]


def private_cover_lower_bound(k: int) -> int:
    """Return the universal private-coordinate construction bound.

    Two coordinates are reserved to avoid the exceptional ranks 2, 6, and 12.
    For k >= 3, floor(k/2) safe private coordinates remain available.
    """
    if k < 0:
        raise ValueError("k must be nonnegative")
    if k < 3:
        return 1
    private = k // 2
    return (2**private - 1) ** (k - private)


def private_cover_upper_bound(k: int, multiplicity: int) -> int:
    """Count all private-coordinate encodings with slot multiplicity bounded."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    if multiplicity < 1:
        raise ValueError("multiplicity must be positive")
    return sum(
        math.comb(k, size)
        * (2 * multiplicity) ** size
        * 2 ** (size * (k - size))
        for size in range(1, k + 1)
    )


@lru_cache(maxsize=None)
def atomic_family_multiplicity(n: int) -> int:
    """Return max #A_{I,J}(n) over nonempty essential/full supports."""
    if n < 3:
        raise ValueError("atomic multiplicity is used here only for n >= 3")
    n_factors = factor_dict(
        tuple(sorted((int(p), int(e)) for p, e in factorint(n).items()))
    )
    coordinates = tuple(n_factors)
    family_counts: Dict[Tuple[frozenset, frozenset], int] = {}

    for prime, top_exponent in factorint_fibonacci(n):
        for exponent in range(1, top_exponent + 1):
            rank = alpha_for_fn_divisor(prime**exponent, n)
            lower_rank = alpha_for_fn_divisor(prime ** (exponent - 1), n)
            if rank == lower_rank:
                continue
            full = frozenset(
                i
                for i, ell in enumerate(coordinates)
                if valuation(rank, ell) == n_factors[ell]
            )
            essential = frozenset(
                i
                for i in full
                if valuation(lower_rank, coordinates[i]) < n_factors[coordinates[i]]
            )
            if essential:
                key = (essential, full)
                family_counts[key] = family_counts.get(key, 0) + 1

    if not family_counts:
        raise AssertionError(f"no effective atomic family at n={n}")
    return max(family_counts.values())


def run_battery(exhaustive_max: int, scalable_max: int) -> str:
    if exhaustive_max < 30:
        raise ValueError("exhaustive_max must be at least 30")
    if scalable_max < exhaustive_max:
        raise ValueError("scalable_max must be at least exhaustive_max")

    failures = []
    counterexamples = []
    results = {}
    birth_layer_set_equalities = 0
    minimal_generator_set_equalities = 0

    for n in range(2, scalable_max + 1):
        threshold = upper_fiber_threshold(n)
        results[n] = threshold
        if n <= exhaustive_max:
            exhaustive = upper_fiber_exhaustive(n)
            birth_layer_set_equalities += 1
            if exhaustive.a_count != threshold.a_count:
                failures.append(
                    f"n={n}: A mismatch {exhaustive.a_count} != {threshold.a_count}"
                )
            if exhaustive.minimal_generators != threshold.minimal_generators:
                failures.append(f"n={n}: minimal-generator methods disagree")
            else:
                minimal_generator_set_equalities += 1

        if n >= 3:
            count = len(threshold.minimal_generators)
            k = omega(n)
            multiplicity = atomic_family_multiplicity(n)
            big_omega = omega_big(factorint_fibonacci(n))
            subset_bound = sum(
                math.comb(big_omega, r)
                for r in range(0, min(k, big_omega) + 1)
            )
            if count > subset_bound:
                counterexamples.append(
                    f"n={n}: #M={count} exceeds subset bound {subset_bound}"
                )
            if count > n**k:
                counterexamples.append(f"n={n}: #M={count} exceeds n^omega={n**k}")
            if n % 2 == 1 and count < bell_number(k):
                counterexamples.append(
                    f"n={n}: #M={count} below Bell({k})={bell_number(k)}"
                )
            if k >= 3 and count < private_cover_lower_bound(k):
                counterexamples.append(
                    f"n={n}: #M={count} below private-cover bound "
                    f"{private_cover_lower_bound(k)}"
                )
            private_upper = private_cover_upper_bound(k, multiplicity)
            if count > private_upper:
                counterexamples.append(
                    f"n={n}: #M={count} exceeds private-cover upper bound "
                    f"{private_upper} with R(n)={multiplicity}"
                )

    expected_m30 = (20, 22, 31, 244, 671)
    n30 = results[30]
    if n30.a_count != 52 or n30.minimal_generators != expected_m30:
        failures.append(
            f"n=30 correction failed: A={n30.a_count}, M={n30.minimal_generators}"
        )
    realized_types = tuple(sorted(classify_support_three(m, 30) for m in expected_m30))
    expected_types = ("Gamma_1", "Gamma_4", "Gamma_5", "Gamma_7", "Gamma_8")
    if realized_types != expected_types:
        failures.append(f"n=30 type mismatch: {realized_types}")
    excluded_types = ("Gamma_3", "Gamma_6", "Gamma_9")
    if not set(excluded_types).isdisjoint(realized_types):
        counterexamples.append("n=30 realizes a claimed excluded type")

    checkpoints = sorted(
        set([30, exhaustive_max, scalable_max] + list(range(50, scalable_max + 1, 50)))
    )
    growth_lines = []
    for bound in checkpoints:
        if bound > scalable_max:
            continue
        values = [
            (n, len(results[n].minimal_generators)) for n in range(3, bound + 1)
        ]
        max_n, max_count = max(values, key=lambda item: item[1])
        mean_log = sum(math.log(count) for _, count in values) / len(values)
        high_support = [
            n for n, _ in values if omega(n) >= 3
        ]
        entropy_constant = math.log(2) / 4
        if high_support:
            cumulative_ratio = sum(
                math.log(len(results[n].minimal_generators)) for n in high_support
            ) / sum(entropy_constant * omega(n) ** 2 for n in high_support)
            ratio_text = f"; private-entropy ratio = {cumulative_ratio:.6f}"
        else:
            ratio_text = "; private-entropy ratio = n/a"
        growth_lines.append(
            f"  n <= {bound:>3}: max #M_n = {max_count} at n={max_n}; "
            f"mean(log #M_n) = {mean_log:.6f}{ratio_text}"
        )

    multiplicities = {
        n: atomic_family_multiplicity(n) for n in range(3, scalable_max + 1)
    }
    max_r_n = max(multiplicities, key=multiplicities.get)
    support_four = results.get(210)

    lines = [
        "Finite verification report",
        "==========================",
        f"Exact exhaustive divisor/rank range: 2 <= n <= {exhaustive_max}",
        f"Finite claim-check range: 2 <= n <= {scalable_max}",
        f"Python version: {platform.python_version()}",
        f"SymPy version: {sympy_version}",
        "Factorization algorithm: SymPy factorint over exact Python integers",
        "Set comparisons on the exhaustive range:",
        f"  B_n direct = B_n upper fiber: {birth_layer_set_equalities}/"
        f"{exhaustive_max - 1} set equalities",
        f"  M_n direct = M_n witness: {minimal_generator_set_equalities}/"
        f"{exhaustive_max - 1} set equalities",
        "",
        "Table checkpoint at n=30:",
        f"  A(30) = {n30.a_count}",
        f"  M_30 = {n30.minimal_generators}",
        "",
        "Support-bound checks:",
        "  private-cover lower bound (k>=3): #M_n >= "
        "(2^floor(k/2)-1)^ceil(k/2)",
        "  private-cover upper bound: sum_{r<=k} binom(k,r) "
        "(2R(n))^r 2^{r(k-r)}",
        *growth_lines,
        f"  max rank-window multiplicity R(n) = {multiplicities[max_r_n]} "
        f"at n={max_r_n}",
        *(
            [
                f"  support-four checkpoint n=210: #M_210 = "
                f"{len(support_four.minimal_generators)}, R(210) = "
                f"{multiplicities[210]}, lower bound = "
                f"{private_cover_lower_bound(4)}"
            ]
            if support_four is not None
            else []
        ),
        "",
        "Finite claim checks:",
        f"  failures = {len(failures)}",
        f"  counterexamples = {len(counterexamples)}",
    ]
    if failures:
        lines.extend(f"  FAILURE: {failure}" for failure in failures)
    if counterexamples:
        lines.extend(f"  COUNTEREXAMPLE: {item}" for item in counterexamples)
    lines.extend(
        [
            "",
            "RESULT: "
            + (
                "PASS (0 failures / 0 counterexamples)"
                if not failures and not counterexamples
                else "FAIL"
            ),
        ]
    )
    report = "\n".join(lines) + "\n"
    if failures or counterexamples:
        raise AssertionError(report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-max", type=int, default=60)
    parser.add_argument("--scalable-max", type=int, default=210)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/finite_verification.txt"),
    )
    parser.add_argument(
        "--factorizations-output",
        type=Path,
        default=Path("artifacts/fibonacci_factorizations_2_210.tsv"),
    )
    args = parser.parse_args()

    report = run_battery(args.exhaustive_max, args.scalable_max)
    write_factorization_archive(args.factorizations_output, args.scalable_max)
    load_factorization_archive(args.factorizations_output, args.scalable_max)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="ascii", newline="\n")
    print(report, end="")
    print(f"Saved report: {args.output}")
    print(f"Saved factorization archive: {args.factorizations_output}")


if __name__ == "__main__":
    main()
