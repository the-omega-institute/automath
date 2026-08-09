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
import time
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


@dataclass(frozen=True)
class RankPureSectorResult:
    n: int
    coordinate_count: int
    exceptional_support_count: int
    minimal_cover_count: int
    admissible_cover_count: int
    connected_admissible_cover_count: int
    canonical_product_count: int
    weighted_product_count: int
    canonical_products: Tuple[int, ...]


@dataclass(frozen=True)
class RankWindowDeaggregationData:
    n: int
    visible_rank_maximum: int
    prime_window_maximum: int
    multiplicity: int
    exponent_product: int
    exponent_cost: float


@dataclass(frozen=True)
class FibotomicRankEntropyData:
    rank: int
    fibotomic_value: int
    exact_rank_primes: Tuple[int, ...]
    exact_rank_radical: int
    entropy_lower_bound: float
    binet_error: float


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
    path.write_text("\n".join(lines) + "\n", encoding="ascii")


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


def _rank_supports(m: int, n: int) -> Tuple[frozenset, ...]:
    """Return the positive-coordinate supports in the rank hypergraph."""
    coordinates = prime_divisors(n)
    supports = []
    for prime, exponent in sorted(
        (int(p), int(e)) for p, e in factorint(m).items()
    ):
        rank = alpha_for_fn_divisor(prime**exponent, n)
        supports.append(
            frozenset(i for i, ell in enumerate(coordinates) if rank % ell == 0)
        )
    return tuple(supports)


def _supports_are_connected(supports: Sequence[frozenset], k: int) -> bool:
    if k == 1:
        return True
    adjacency = [set() for _ in range(k)]
    for support in supports:
        for vertex in support:
            adjacency[vertex].update(support - {vertex})
    reached = {0}
    frontier = [0]
    while frontier:
        vertex = frontier.pop()
        for neighbor in adjacency[vertex] - reached:
            reached.add(neighbor)
            frontier.append(neighbor)
    return len(reached) == k


@lru_cache(maxsize=None)
def support_spectra(n: int) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    """Compute the total and connected omega-spectra of M_n exactly."""
    if n < 3:
        raise ValueError("support spectra are stated here only for n >= 3")
    k = omega(n)
    total = set()
    connected = set()
    for m in upper_fiber_threshold(n).minimal_generators:
        size = omega(m)
        total.add(size)
        if _supports_are_connected(_rank_supports(m, n), k):
            connected.add(size)
    return tuple(sorted(total)), tuple(sorted(connected))


def expected_support_spectrum(n: int) -> Tuple[int, ...]:
    """Return the theorem's predicted total support spectrum."""
    if n < 3:
        raise ValueError("support spectra are stated here only for n >= 3")
    factors = factor_dict(
        tuple(sorted((int(p), int(e)) for p, e in factorint(n).items()))
    )
    k = len(factors)
    has_extremal_slice = not (2 in factors and all(e == 1 for e in factors.values()))
    return tuple(range(1, k + 1 if has_extremal_slice else k))


def expected_connected_support_spectrum(n: int) -> Tuple[int, ...]:
    """Return the theorem's predicted connected support spectrum."""
    if n < 3:
        raise ValueError("support spectra are stated here only for n >= 3")
    factors = factor_dict(
        tuple(sorted((int(p), int(e)) for p, e in factorint(n).items()))
    )
    k = len(factors)
    if k == 1:
        return (1,)
    squarefree = all(e == 1 for e in factors.values())
    rank_six_orientation_obstruction = (
        factors.get(2) == 2
        and factors.get(3) == 1
        and all(e == 1 for p, e in factors.items() if p not in (2, 3))
    )
    has_connected_extremal_slice = (
        not squarefree and not rank_six_orientation_obstruction
    )
    return tuple(range(1, k + 1 if has_connected_extremal_slice else k))


@lru_cache(maxsize=None)
def extremal_support_product_count(n: int) -> int:
    """Count the product of the k singleton diagonal atomic families."""
    if n < 3:
        raise ValueError("the extremal slice is stated here only for n >= 3")
    k = omega(n)
    counts = [0] * k
    for prime, top_exponent in factorint_fibonacci(n):
        for exponent in range(1, top_exponent + 1):
            theta = prime**exponent
            if alpha_for_fn_divisor(theta, n) == alpha_for_fn_divisor(
                prime ** (exponent - 1), n
            ):
                continue
            essential, full = _support_pairs(theta, n)[0]
            if essential == full and len(full) == 1:
                counts[next(iter(full))] += 1
    return math.prod(counts)


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


@lru_cache(maxsize=None)
def minimal_cover_counts_by_size(k: int) -> Tuple[int, ...]:
    """Return the Hearne--Wagner counts C_{k,s}, for 1 <= s <= k."""
    if k < 1:
        return tuple()
    stirling = [[0] * (k + 1) for _ in range(k + 1)]
    stirling[0][0] = 1
    for n in range(1, k + 1):
        for s in range(1, n + 1):
            stirling[n][s] = stirling[n - 1][s - 1] + s * stirling[n - 1][s]
    return tuple(
        sum(
            math.comb(k, j)
            * stirling[j][s]
            * (2**s - s - 1) ** (k - j)
            for j in range(s, k + 1)
        )
        for s in range(1, k + 1)
    )


@lru_cache(maxsize=None)
def minimal_cover_count(k: int) -> int:
    """Return the number C_k of minimal covers of a labelled k-set."""
    if k == 0:
        return 1
    if k < 0:
        raise ValueError("k must be nonnegative")
    return sum(minimal_cover_counts_by_size(k))


@lru_cache(maxsize=None)
def bicolored_graph_count(k: int) -> int:
    """Return b_k = sum_s binom(k,s) 2^(s(k-s))."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return sum(math.comb(k, s) * 2 ** (s * (k - s)) for s in range(k + 1))


def theta_constant(parity: int) -> float:
    """Return the parity-dependent base-2 Jacobi theta constant."""
    if parity not in (0, 1):
        raise ValueError("parity must be 0 or 1")
    shift = 0.5 * parity
    return sum(2.0 ** (-(r + shift) ** 2) for r in range(-20, 21))


def theta_normalized_cover_ratio(k: int) -> float:
    """Normalize C_k by its parity-dependent theta asymptotic."""
    if k < 1:
        raise ValueError("k must be positive")
    log_scale = (
        math.log(theta_constant(k % 2))
        + math.log(math.comb(k, k // 2))
        + (k * k / 4) * math.log(2)
    )
    return math.exp(math.log(minimal_cover_count(k)) - log_scale)


def local_limit_probability(k: int, displacement: int) -> Tuple[float, float]:
    """Return the exact central cover mass and its discrete-theta limit."""
    if k < 1:
        raise ValueError("k must be positive")
    size = k // 2 + displacement
    counts = minimal_cover_counts_by_size(k)
    actual = counts[size - 1] / minimal_cover_count(k) if 1 <= size <= k else 0.0
    shift = 0.5 * (k % 2)
    limit = 2.0 ** (-(displacement - shift) ** 2) / theta_constant(k % 2)
    return actual, limit


@lru_cache(maxsize=None)
def connected_minimal_cover_count(k: int) -> int:
    """Return the connected count obtained by labelled exponential inversion."""
    if k < 1:
        return 0
    return minimal_cover_count(k) - sum(
        math.comb(k - 1, j - 1)
        * connected_minimal_cover_count(j)
        * minimal_cover_count(k - j)
        for j in range(1, k)
    )


@lru_cache(maxsize=None)
def _minimal_covers(k: int) -> Tuple[Tuple[int, ...], ...]:
    """Enumerate minimal covers as bitmask families for the finite k <= 4 check."""
    if not 1 <= k <= 4:
        raise ValueError("finite rank-pure enumeration requires 1 <= k <= 4")
    subsets = tuple(range(1, 1 << k))
    full = (1 << k) - 1
    covers = []
    for family_mask in range(1, 1 << len(subsets)):
        family = tuple(
            subset
            for index, subset in enumerate(subsets)
            if family_mask & (1 << index)
        )
        union = 0
        for subset in family:
            union |= subset
        if union != full:
            continue
        if all(
            any(
                subset & (1 << vertex)
                and all(
                    not (other & (1 << vertex))
                    for other in family
                    if other != subset
                )
                for vertex in range(k)
            )
            for subset in family
        ):
            covers.append(family)
    return tuple(covers)


def _cover_is_connected(family: Sequence[int], k: int) -> bool:
    reached = family[0]
    while True:
        enlarged = reached
        for subset in family:
            if subset & reached:
                enlarged |= subset
        if enlarged == reached:
            return reached == (1 << k) - 1
        reached = enlarged


def _mobius(value: int) -> int:
    factors = factorint(value)
    if any(int(exponent) > 1 for exponent in factors.values()):
        return 0
    return -1 if len(factors) % 2 else 1


@lru_cache(maxsize=None)
def exact_rank_prime_count(rank: int) -> int:
    """Return #Pi_alpha(rank) by exact Mobius inversion."""
    if rank < 1:
        raise ValueError("rank must be positive")
    divisors = divisors_from_factorization(
        tuple(sorted((int(p), int(e)) for p, e in factorint(rank).items()))
    )
    return sum(
        _mobius(rank // divisor) * len(factorint_fibonacci(divisor))
        for divisor in divisors
    )


def fibotomic_error_bound(terms: int = 64) -> float:
    """Return a rigorous numerical upper bound for the Binet error constant."""
    if terms < 1:
        raise ValueError("terms must be positive")
    golden_ratio = (1.0 + math.sqrt(5.0)) / 2.0
    ratio = golden_ratio**-2
    partial = sum(
        abs(math.log1p(-((-ratio) ** index)))
        for index in range(1, terms + 1)
    )
    tail = ratio ** (terms + 1) / (1.0 - ratio) ** 2
    return partial + tail


@lru_cache(maxsize=None)
def fibotomic_rank_entropy_data(rank: int) -> FibotomicRankEntropyData:
    """Compute the finite data in the fibotomic rank-entropy inequality."""
    if rank < 3:
        raise ValueError("fibotomic rank entropy is stated only for rank >= 3")
    rank_divisors = divisors_from_factorization(
        tuple(sorted((int(p), int(e)) for p, e in factorint(rank).items()))
    )
    fibotomic_exponents: Dict[int, int] = {}
    for divisor in rank_divisors:
        coefficient = _mobius(rank // divisor)
        for prime, exponent in factorint_fibonacci(divisor):
            fibotomic_exponents[prime] = (
                fibotomic_exponents.get(prime, 0) + coefficient * exponent
            )
    if any(exponent < 0 for exponent in fibotomic_exponents.values()):
        raise AssertionError(f"nonintegral fibotomic factor at rank={rank}")
    fibotomic_value = math.prod(
        prime**exponent
        for prime, exponent in fibotomic_exponents.items()
        if exponent
    )
    exact_rank_primes = tuple(
        sorted(
            prime
            for prime, _ in factorint_fibonacci(rank)
            if alpha_for_fn_divisor(prime, rank) == rank
        )
    )
    exact_rank_radical = math.prod(exact_rank_primes)
    count = len(exact_rank_primes)
    half_count = count // 2
    entropy_lower_bound = (
        count * math.log(2.0 * rank / 3.0)
        + 2.0 * math.lgamma(half_count + 1)
        + (count - 2 * half_count) * math.log(half_count + 1)
    )
    golden_ratio = (1.0 + math.sqrt(5.0)) / 2.0
    totient = rank
    for prime in factorint(rank):
        totient = totient // int(prime) * (int(prime) - 1)
    return FibotomicRankEntropyData(
        rank=rank,
        fibotomic_value=fibotomic_value,
        exact_rank_primes=exact_rank_primes,
        exact_rank_radical=exact_rank_radical,
        entropy_lower_bound=entropy_lower_bound,
        binet_error=math.log(fibotomic_value) - totient * math.log(golden_ratio),
    )


@lru_cache(maxsize=None)
def rank_pure_sector(n: int) -> RankPureSectorResult:
    """Verify the rank-pure cover embedding on one finite arithmetic layer."""
    if n < 3:
        raise ValueError("rank-pure sectors are used only for n >= 3")
    coordinates = prime_divisors(n)
    k = len(coordinates)
    covers = _minimal_covers(k)
    n_factors = factor_dict(tuple(sorted((int(p), int(e)) for p, e in factorint(n).items())))

    support_rank = {
        support: math.prod(
            prime ** n_factors[prime]
            for index, prime in enumerate(coordinates)
            if support & (1 << index)
        )
        for support in range(1, 1 << k)
    }
    exceptional = {
        support for support, rank in support_rank.items() if rank in {2, 6, 12}
    }
    if len(exceptional) > 2 or any(support.bit_count() > 2 for support in exceptional):
        raise AssertionError("exceptional support bound failed")

    primes_by_rank: Dict[int, Tuple[int, ...]] = {}
    mutable_primes: Dict[int, list[int]] = {}
    for prime, _ in factorint_fibonacci(n):
        rank = alpha_for_fn_divisor(prime, n)
        mutable_primes.setdefault(rank, []).append(prime)
    primes_by_rank = {
        rank: tuple(sorted(primes)) for rank, primes in mutable_primes.items()
    }

    for rank in support_rank.values():
        mobius_count = exact_rank_prime_count(rank)
        if mobius_count != len(primes_by_rank.get(rank, tuple())):
            raise AssertionError(f"exact-rank prime count failed at n={n}, rank={rank}")

    canonical_products = []
    weighted_product_count = 0
    connected_count = 0
    admissible_count = 0
    for family in covers:
        if any(support in exceptional for support in family):
            continue
        prime_choices = [primes_by_rank[support_rank[support]] for support in family]
        if any(not choices for choices in prime_choices):
            raise AssertionError(f"unexpected empty exact-rank class at n={n}")
        admissible_count += 1
        weighted_product_count += math.prod(len(choices) for choices in prime_choices)
        canonical_products.append(math.prod(choices[0] for choices in prime_choices))
        if _cover_is_connected(family, k):
            connected_count += 1

    if len(set(canonical_products)) != len(canonical_products):
        raise AssertionError(f"rank-pure product collision at n={n}")
    return RankPureSectorResult(
        n=n,
        coordinate_count=k,
        exceptional_support_count=len(exceptional),
        minimal_cover_count=len(covers),
        admissible_cover_count=admissible_count,
        connected_admissible_cover_count=connected_count,
        canonical_product_count=len(canonical_products),
        weighted_product_count=weighted_product_count,
        canonical_products=tuple(sorted(canonical_products)),
    )


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


def refined_private_cover_upper_bound(k: int, multiplicity: int) -> int:
    """Count private-coordinate encodings with one total ladder choice."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    if multiplicity < 1:
        raise ValueError("multiplicity must be positive")
    return sum(
        math.comb(k, size)
        * (multiplicity * 2 ** (k - size) + 1) ** size
        for size in range(1, k + 1)
    )


@lru_cache(maxsize=None)
def atomic_family_multiplicity(n: int) -> int:
    """Return max #A_{I,J}(n) over nonempty essential/full supports."""
    if n == 2:
        return 1
    if n < 2:
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


@lru_cache(maxsize=None)
def rank_window_deaggregation_data(n: int) -> RankWindowDeaggregationData:
    """Return the finite quantities in the rank-window deaggregation bounds."""
    if n < 3:
        raise ValueError("rank-window deaggregation is used only for n >= 3")
    n_factors = {
        int(prime): int(exponent) for prime, exponent in factorint(n).items()
    }
    divisors = divisors_from_factorization(tuple(sorted(n_factors.items())))
    window_totals: Dict[frozenset[int], int] = {}
    visible_counts = []
    for divisor in divisors:
        full_support = frozenset(
            prime
            for prime, exponent in n_factors.items()
            if valuation(divisor, prime) == exponent
        )
        if not full_support:
            continue
        count = exact_rank_prime_count(divisor)
        visible_counts.append(count)
        window_totals[full_support] = window_totals.get(full_support, 0) + count
    return RankWindowDeaggregationData(
        n=n,
        visible_rank_maximum=max([1, *visible_counts]),
        prime_window_maximum=max(window_totals.values(), default=0),
        multiplicity=atomic_family_multiplicity(n),
        exponent_product=math.prod(n_factors.values()),
        exponent_cost=sum(math.log(exponent) for exponent in n_factors.values()),
    )


def run_battery(exhaustive_max: int, scalable_max: int) -> str:
    if exhaustive_max < 30:
        raise ValueError("exhaustive_max must be at least 30")
    if scalable_max < exhaustive_max:
        raise ValueError("scalable_max must be at least exhaustive_max")

    started = time.time()
    failures = []
    counterexamples = []
    results = {}
    birth_layer_set_equalities = 0
    minimal_generator_set_equalities = 0
    rank_pure_layers = 0
    rank_pure_membership_layers = 0
    odd_rank_pure_layers = 0
    odd_complete_realizations = 0
    deaggregation_layers = 0
    deaggregation_checks = 0
    squarefree_layers = 0
    squarefree_pigeonhole_checks = 0
    refined_private_bound_checks = 0
    fibotomic_layers = 0
    fibotomic_entropy_checks = 0
    fibotomic_radical_checks = 0
    jarden_layers = 0
    jarden_checks = 0
    support_spectrum_checks = 0
    connected_support_spectrum_checks = 0
    extremal_slice_checks = 0
    error_bound = fibotomic_error_bound()

    cover_formula_checks = 0
    connected_cover_checks = 0
    for k in range(1, 5):
        covers = _minimal_covers(k)
        if len(covers) == minimal_cover_count(k):
            cover_formula_checks += 1
        else:
            failures.append(f"k={k}: minimal-cover formula disagrees with enumeration")
        connected = sum(_cover_is_connected(family, k) for family in covers)
        if connected == connected_minimal_cover_count(k):
            connected_cover_checks += 1
        else:
            failures.append(f"k={k}: connected-cover inversion disagrees with enumeration")

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
            total_spectrum, connected_spectrum = support_spectra(n)
            if total_spectrum == expected_support_spectrum(n):
                support_spectrum_checks += 1
            else:
                failures.append(
                    f"n={n}: total support spectrum {total_spectrum} disagrees "
                    f"with {expected_support_spectrum(n)}"
                )
            if connected_spectrum == expected_connected_support_spectrum(n):
                connected_support_spectrum_checks += 1
            else:
                failures.append(
                    f"n={n}: connected support spectrum {connected_spectrum} "
                    f"disagrees with {expected_connected_support_spectrum(n)}"
                )
            extremal = tuple(
                m for m in threshold.minimal_generators if omega(m) == k
            )
            diagonal_pairs = tuple(
                ((i,), (i,)) for i in range(k)
            )
            if (
                len(extremal) == extremal_support_product_count(n)
                and all(
                    _normalized_pairs(_support_pairs(m, n)) == diagonal_pairs
                    for m in extremal
                )
            ):
                extremal_slice_checks += 1
            else:
                failures.append(
                    f"n={n}: extremal slice fails the singleton-family "
                    "product classification"
                )
            fibotomic_layers += 1
            entropy_data = fibotomic_rank_entropy_data(n)
            congruences_hold = all(
                prime in (2, 5)
                or (prime - 1) % n == 0
                or (prime + 1) % n == 0
                for prime in entropy_data.exact_rank_primes
            )
            candidate_bounds_hold = all(
                prime >= n * math.ceil(index / 2) - 1
                for index, prime in enumerate(
                    entropy_data.exact_rank_primes, start=1
                )
            )
            if (
                entropy_data.entropy_lower_bound
                <= math.log(entropy_data.fibotomic_value) + 1e-12
                and abs(entropy_data.binet_error) <= error_bound
                and congruences_hold
                and candidate_bounds_hold
            ):
                fibotomic_entropy_checks += 1
            else:
                failures.append(f"n={n}: fibotomic rank-entropy bound failed")
            if (
                len(entropy_data.exact_rank_primes)
                == exact_rank_prime_count(n)
                and entropy_data.fibotomic_value
                % entropy_data.exact_rank_radical
                == 0
            ):
                fibotomic_radical_checks += 1
            else:
                failures.append(
                    f"n={n}: exact-rank radical does not divide fibotomic value"
                )
            if n % 10 == 0:
                jarden_prime = n // 10
                jarden_factorization = factorint(jarden_prime)
                if (
                    jarden_prime > 5
                    and jarden_factorization == {jarden_prime: 1}
                ):
                    jarden_layers += 1
                    if exact_rank_prime_count(n) >= 2:
                        jarden_checks += 1
                    else:
                        failures.append(f"n={n}: Jarden exact-rank consequence failed")
            deaggregation_layers += 1
            deaggregation = rank_window_deaggregation_data(n)
            log_gap = math.log(deaggregation.multiplicity) - math.log(
                deaggregation.visible_rank_maximum
            )
            if (
                deaggregation.prime_window_maximum
                <= deaggregation.multiplicity
                <= deaggregation.prime_window_maximum + 1
                and deaggregation.visible_rank_maximum
                <= deaggregation.multiplicity
                <= 1
                + deaggregation.visible_rank_maximum
                * deaggregation.exponent_product
                and -1e-12 <= log_gap
                <= math.log(2) + deaggregation.exponent_cost + 1e-12
            ):
                deaggregation_checks += 1
            else:
                failures.append(f"n={n}: rank-window deaggregation bound failed")

            refined_upper = refined_private_cover_upper_bound(
                k, deaggregation.multiplicity
            )
            if count <= refined_upper:
                refined_private_bound_checks += 1
            else:
                counterexamples.append(
                    f"n={n}: #M={count} exceeds refined private-cover "
                    f"upper bound {refined_upper}"
                )

            n_factorization = factorint(n)
            if all(int(exponent) == 1 for exponent in n_factorization.values()):
                squarefree_layers += 1
                exact_rank_total = sum(
                    exact_rank_prime_count(divisor)
                    for divisor in divisors_from_factorization(
                        tuple(
                            sorted(
                                (int(p), int(e))
                                for p, e in n_factorization.items()
                            )
                        )
                    )
                )
                if (
                    exact_rank_total == len(factorint_fibonacci(n))
                    and deaggregation.multiplicity
                    >= exact_rank_total / (2**k - 1)
                ):
                    squarefree_pigeonhole_checks += 1
                else:
                    failures.append(
                        f"n={n}: squarefree exact-rank pigeonhole bound failed"
                    )
            if k <= 4:
                rank_pure_layers += 1
                try:
                    sector = rank_pure_sector(n)
                except AssertionError as error:
                    failures.append(str(error))
                else:
                    if set(sector.canonical_products).issubset(
                        threshold.minimal_generators
                    ):
                        rank_pure_membership_layers += 1
                    else:
                        failures.append(
                            f"n={n}: a rank-pure product is absent from M_n"
                        )
                    if n % 2 == 1:
                        odd_rank_pure_layers += 1
                        if (
                            sector.admissible_cover_count
                            == sector.minimal_cover_count
                            == minimal_cover_count(k)
                        ):
                            odd_complete_realizations += 1
                        else:
                            failures.append(
                                f"n={n}: odd rank-pure sector misses a minimal cover"
                            )
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

    elapsed = time.time() - started
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
        "Rank-pure universality checks:",
        f"  Minimal-cover formula = direct enumeration (k <= 4): "
        f"{cover_formula_checks}/4",
        f"  Connected-cover inversion = direct enumeration (k <= 4): "
        f"{connected_cover_checks}/4",
        f"  Rank-pure layers checked: {rank_pure_layers}",
        f"  Exact-rank Mobius counts checked on every nonempty support",
        f"  Rank-pure canonical products in M_n: {rank_pure_membership_layers}/"
        f"{rank_pure_layers} layer checks",
        f"  Odd layers realizing all minimal covers: {odd_complete_realizations}/"
        f"{odd_rank_pure_layers}",
        f"  Exact total support spectra: {support_spectrum_checks}/"
        f"{deaggregation_layers}",
        f"  Exact connected support spectra: {connected_support_spectrum_checks}/"
        f"{deaggregation_layers}",
        f"  Extremal atomic-product counts: {extremal_slice_checks}/"
        f"{deaggregation_layers}",
        "  Exact minimal-cover values C_k (1 <= k <= 6): "
        + str(tuple(minimal_cover_count(k) for k in range(1, 7))),
        "  Connected-cover ratios D_k/C_k at k=20,40,80: "
        + ", ".join(
            f"{connected_minimal_cover_count(k) / minimal_cover_count(k):.12f}"
            for k in (20, 40, 80)
        ),
        "  Theta-normalized C_k ratios at k=20,40,80: "
        + ", ".join(
            f"{theta_normalized_cover_ratio(k):.12f}" for k in (20, 40, 80)
        ),
        "  Central local-limit errors at k=40,80 (d=0): "
        + ", ".join(
            f"{abs(local_limit_probability(k, 0)[0] - local_limit_probability(k, 0)[1]):.3e}"
            for k in (40, 80)
        ),
        f"  Rank-window deaggregation inequalities: {deaggregation_checks}/"
        f"{deaggregation_layers}",
        f"  Squarefree BLMS pigeonhole inequalities: "
        f"{squarefree_pigeonhole_checks}/{squarefree_layers}",
        f"  Refined private-cover upper bounds: {refined_private_bound_checks}/"
        f"{deaggregation_layers}",
        f"  Fibotomic rank-entropy inequalities: {fibotomic_entropy_checks}/"
        f"{fibotomic_layers}",
        f"  Fibotomic exact-rank radical divisibilities: "
        f"{fibotomic_radical_checks}/{fibotomic_layers}",
        f"  Jarden a(10p) >= 2 checks: {jarden_checks}/{jarden_layers}",
        "",
        "Corrected n=30 data:",
        f"  A(30) = {n30.a_count}",
        f"  M_30 = {n30.minimal_generators}",
        f"  realized types = {realized_types}",
        f"  excluded types = {excluded_types}",
        "",
        "Growth-law checks:",
        "  finite upper bound: #M_n <= sum_{r<=omega(n)} binom(Omega(F_n), r)",
        "  simplified upper bound: #M_n <= n^omega(n)",
        "  odd-layer lower bound: #M_n >= Bell(omega(n))",
        "  private-cover lower bound (k>=3): #M_n >= "
        "(2^floor(k/2)-1)^ceil(k/2)",
        "  private-cover upper bound: sum_{r<=k} binom(k,r) "
        "(2R(n))^r 2^{r(k-r)}",
        *growth_lines,
        f"  max rank-window multiplicity R(n) = {multiplicities[max_r_n]} "
        f"at n={max_r_n}",
        *(
            [
                f"  first support-four layer n=210: #M_210 = "
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
            f"  elapsed_seconds = {elapsed:.3f}",
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
    args.output.write_text(report, encoding="ascii")
    print(report, end="")
    print(f"Saved report: {args.output}")
    print(f"Saved factorization archive: {args.factorizations_output}")


if __name__ == "__main__":
    main()
