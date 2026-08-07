#!/usr/bin/env python3
"""Finite checks for recurrent-numeration pumping and local obstructions.

This is not a proof of language immunity.  It checks the exact matrix identity
used in the proof on explicit recurrences, synchronized multi-block return
periods, a local prime-layer isolation certificate, prescribed-depth quotient
congruences, and a finite induced divisibility tree.  It also searches for the
singular-modulus obstruction at a prime dividing a nonunit trailing coefficient.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import product
from math import gcd, lcm
from typing import Iterable, Sequence


Matrix = tuple[tuple[int, ...], ...]
Word = tuple[int, ...]


@dataclass(frozen=True)
class LinearSystem:
    name: str
    polynomial: str
    recurrence: tuple[int, ...]  # U_(n+d) = sum recurrence[j] U_(n+j)
    initials: tuple[int, ...]
    max_digit: int

    @property
    def dimension(self) -> int:
        return len(self.recurrence)

    @property
    def trailing_coefficient(self) -> int:
        return self.recurrence[0]


SYSTEMS = (
    LinearSystem("fibonacci", "x^2-x-1", (1, 1), (1, 2), 1),
    LinearSystem("pell", "x^2-2x-1", (1, 2), (1, 2), 2),
    LinearSystem("tribonacci", "x^3-x^2-x-1", (1, 1, 1), (1, 2, 4), 1),
    LinearSystem("quadratic_nonunit", "x^2-2x-2", (2, 2), (1, 3), 2),
    LinearSystem("integer_base_2", "x-2", (2,), (1,), 1),
)


class NonInvertibleAction(ValueError):
    pass


@dataclass(frozen=True)
class PumpWitness:
    system: str
    original_word: str
    original_value: int
    cuts: tuple[int, int, int, int]
    return_time: int
    pump_exponent: int
    pumped_length: int
    pumped_value: int
    quotient_mod_original: int
    canonical_before: bool
    canonical_after: bool


def system_by_name(name: str) -> LinearSystem:
    return next(system for system in SYSTEMS if system.name == name)


def identity(size: int) -> Matrix:
    return tuple(
        tuple(1 if row == column else 0 for column in range(size))
        for row in range(size)
    )


def matmul(left: Matrix, right: Matrix, modulus: int | None = None) -> Matrix:
    rows = len(left)
    inner = len(right)
    columns = len(right[0])
    entries = []
    for row in range(rows):
        out_row = []
        for column in range(columns):
            value = sum(left[row][k] * right[k][column] for k in range(inner))
            out_row.append(value if modulus is None else value % modulus)
        entries.append(tuple(out_row))
    return tuple(entries)


def matvec(matrix: Matrix, vector: Sequence[int]) -> tuple[int, ...]:
    return tuple(
        sum(matrix[row][column] * vector[column] for column in range(len(vector)))
        for row in range(len(matrix))
    )


def determinant(matrix: Matrix) -> int:
    size = len(matrix)
    if size == 1:
        return matrix[0][0]
    total = 0
    for column, entry in enumerate(matrix[0]):
        minor = tuple(
            tuple(row[j] for j in range(size) if j != column)
            for row in matrix[1:]
        )
        total += (-1) ** column * entry * determinant(minor)
    return total


def digit_matrix(system: LinearSystem, digit: int) -> Matrix:
    if not 0 <= digit <= system.max_digit:
        raise ValueError(f"digit {digit} is outside {system.name}'s alphabet")
    d = system.dimension
    rows = [[0] * (d + 1) for _ in range(d + 1)]
    rows[0][0] = 1
    rows[0][1] = digit
    for index in range(d - 1):
        rows[index + 1][index + 2] = 1
    for index, coefficient in enumerate(system.recurrence):
        rows[d][index + 1] = coefficient
    return tuple(tuple(row) for row in rows)


def block_matrix(system: LinearSystem, word: Sequence[int]) -> Matrix:
    matrix = identity(system.dimension + 1)
    for digit in word:
        matrix = matmul(digit_matrix(system, digit), matrix)
    return matrix


def weights(system: LinearSystem, count: int) -> list[int]:
    values = list(system.initials)
    while len(values) < count:
        values.append(
            sum(
                coefficient * values[-system.dimension + index]
                for index, coefficient in enumerate(system.recurrence)
            )
        )
    return values[:count]


def value(system: LinearSystem, word: Sequence[int]) -> int:
    return sum(digit * weight for digit, weight in zip(word, weights(system, len(word))))


def greedy_word(system: LinearSystem, number: int) -> Word:
    if number <= 0:
        return ()
    available = list(system.initials)
    while available[-1] <= number:
        available.append(
            sum(
                coefficient * available[-system.dimension + index]
                for index, coefficient in enumerate(system.recurrence)
            )
        )
    if available[-1] > number:
        available.pop()
    digits_msd = []
    remainder = number
    for weight in reversed(available):
        digit, remainder = divmod(remainder, weight)
        if digit > system.max_digit:
            raise ValueError(f"digit bound too small for {system.name}")
        digits_msd.append(digit)
    if remainder:
        raise ValueError(f"greedy expansion failed for {system.name}")
    return tuple(reversed(digits_msd))


def is_canonical(system: LinearSystem, word: Sequence[int]) -> bool:
    if not word or word[-1] == 0:
        return False
    if system.name == "fibonacci":
        return all(left + right <= 1 for left, right in zip(word, word[1:]))
    return tuple(word) == greedy_word(system, value(system, word))


def matrix_order(matrix: Matrix, modulus: int, limit: int = 2_000_000) -> int:
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    if gcd(determinant(matrix), modulus) != 1:
        raise NonInvertibleAction(
            f"determinant {determinant(matrix)} is not a unit modulo {modulus}"
        )
    reduced = tuple(tuple(entry % modulus for entry in row) for row in matrix)
    target = identity(len(matrix))
    power = target
    for exponent in range(1, limit + 1):
        power = matmul(reduced, power, modulus)
        if power == target:
            return exponent
    raise RuntimeError(f"matrix order exceeded search limit {limit}")


def pumped_word(word: Word, cuts: tuple[int, int, int, int], exponent: int) -> Word:
    a, b, c, d = cuts
    if not 0 <= a <= b <= c <= d <= len(word):
        raise ValueError("cuts must be ordered positions in the word")
    u, v, x, y, z = word[:a], word[a:b], word[b:c], word[c:d], word[d:]
    if not v and not y:
        raise ValueError("at least one pumped block must be nonempty")
    return u + v * exponent + x + y * exponent + z


def pump_disjoint_blocks(
    word: Word, spans: Sequence[tuple[int, int]], exponent: int
) -> Word:
    if exponent < 0:
        raise ValueError("the pumping exponent must be nonnegative")
    previous = 0
    pieces: list[int] = []
    nonempty = False
    for start, stop in spans:
        if not previous <= start <= stop <= len(word):
            raise ValueError("pumped spans must be ordered and disjoint")
        pieces.extend(word[previous:start])
        block = word[start:stop]
        pieces.extend(block * exponent)
        nonempty = nonempty or bool(block)
        previous = stop
    if not nonempty:
        raise ValueError("at least one pumped block must be nonempty")
    pieces.extend(word[previous:])
    return tuple(pieces)


def tail_action_state(
    recurrence: Sequence[int],
    weight_values: Sequence[int],
    prefix: Word,
    suffix: Word,
) -> tuple[int, ...]:
    """Apply suffix matrices to the state seeded after a fixed prefix."""
    dimension = len(recurrence)
    start = len(prefix)
    required = start + len(suffix) + dimension
    if dimension < 1 or len(weight_values) < required:
        raise ValueError("insufficient recurrence or weight data for the suffix")
    for index in range(start, len(weight_values) - dimension):
        expected = sum(
            recurrence[offset] * weight_values[index + offset]
            for offset in range(dimension)
        )
        if weight_values[index + dimension] != expected:
            raise ValueError("the supplied recurrence is not valid after the prefix")

    max_digit = max(prefix + suffix, default=0)
    tail_system = LinearSystem(
        name="tail_action",
        polynomial="",
        recurrence=tuple(recurrence),
        initials=tuple(weight_values[start : start + dimension]),
        max_digit=max_digit,
    )
    prefix_value = sum(
        digit * weight for digit, weight in zip(prefix, weight_values)
    )
    seed = (prefix_value,) + tuple(weight_values[start : start + dimension])
    return matvec(block_matrix(tail_system, suffix), seed)


def linear_mcfg_ray_word(
    prefix: Word,
    constants: Sequence[Word],
    left_pumps: Sequence[Word],
    middles: Sequence[Word],
    right_pumps: Sequence[Word],
    exponent: int,
) -> Word:
    """Evaluate the word produced after ``exponent`` ray recursions."""
    if exponent < 0:
        raise ValueError("the ray exponent must be nonnegative")
    fan_out = len(left_pumps)
    if not (
        len(constants) == fan_out + 1
        and len(middles) == fan_out
        and len(right_pumps) == fan_out
    ):
        raise ValueError("inconsistent synchronized-ray block counts")
    if not any(left_pumps) and not any(right_pumps):
        raise ValueError("at least one synchronized pump must be nonempty")

    word = list(prefix)
    for index in range(fan_out):
        word.extend(constants[index])
        word.extend(left_pumps[index] * exponent)
        word.extend(middles[index])
        word.extend(right_pumps[index] * exponent)
    word.extend(constants[-1])
    return tuple(word)


def check_synchronized_orbit(
    system: LinearSystem,
    word: Word,
    spans: Sequence[tuple[int, int]],
    moduli: Iterable[int],
    parameters: Iterable[int],
) -> int:
    blocks = tuple(word[start:stop] for start, stop in spans if start < stop)
    if not blocks:
        raise ValueError("at least one pumped block must be nonempty")
    tested = 0
    parameter_values = tuple(parameters)
    for modulus in moduli:
        orders = tuple(
            matrix_order(block_matrix(system, block), modulus) for block in blocks
        )
        return_time = lcm(*orders)
        for parameter in parameter_values:
            current = value(system, pump_disjoint_blocks(word, spans, parameter))
            returned = value(
                system,
                pump_disjoint_blocks(word, spans, parameter + return_time),
            )
            if returned % modulus != current % modulus:
                raise AssertionError(
                    f"synchronized congruence failed for {system.name}, "
                    f"q={modulus}, t={parameter}"
                )
            tested += 1
    return tested


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    divisor = 3
    while divisor * divisor <= number:
        if number % divisor == 0:
            return False
        divisor += 2
    return True


def prime_factors(number: int) -> tuple[int, ...]:
    if number < 1:
        raise ValueError("prime factorization is defined here only for positive integers")
    factors = []
    candidate = 2
    remaining = number
    while candidate * candidate <= remaining:
        if remaining % candidate == 0:
            factors.append(candidate)
            while remaining % candidate == 0:
                remaining //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if remaining > 1:
        factors.append(remaining)
    return tuple(factors)


def valuation(number: int, prime: int) -> int:
    exponent = 0
    while number % prime == 0:
        number //= prime
        exponent += 1
    return exponent


def omega_outside(number: int, excluded_primes: Iterable[int]) -> int:
    excluded = set(excluded_primes)
    return sum(prime not in excluded for prime in prime_factors(number))


def in_local_prime_layer(
    number: int,
    maximum_outside_primes: int,
    excluded_primes: Iterable[int],
    valuation_bounds: dict[int, int],
) -> bool:
    excluded = tuple(excluded_primes)
    return (
        number >= 1
        and omega_outside(number, excluded) <= maximum_outside_primes
        and all(valuation(number, prime) <= valuation_bounds[prime] for prime in excluded)
    )


def local_layer_isolation_modulus(
    number: int,
    excluded_primes: Iterable[int],
    valuation_bounds: dict[int, int],
) -> int:
    excluded = tuple(excluded_primes)
    if not in_local_prime_layer(
        number, omega_outside(number, excluded), excluded, valuation_bounds
    ):
        raise ValueError("the point violates an excluded-prime valuation bound")

    outside = tuple(
        prime for prime in prime_factors(number) if prime not in set(excluded)
    )
    outside_core = product_power = 1
    prime_power_modulus = 1
    for prime in outside:
        exponent = valuation(number, prime)
        product_power *= prime**exponent
        prime_power_modulus *= prime ** (exponent + 1)
    outside_core = product_power

    smooth_factors = [1]
    for prime in excluded:
        smooth_factors = [
            factor * prime**exponent
            for factor in smooth_factors
            for exponent in range(valuation_bounds[prime] + 1)
        ]
    candidates = tuple(outside_core * factor for factor in smooth_factors)
    differences = tuple(abs(candidate - number) for candidate in candidates if candidate != number)

    auxiliary = 2
    forbidden = set(excluded) | set(outside)
    while (
        not is_prime(auxiliary)
        or auxiliary in forbidden
        or any(difference % auxiliary == 0 for difference in differences)
    ):
        auxiliary += 1
    return prime_power_modulus * auxiliary


def construct_deep_congruence_chain(
    initial: int, specifications: Sequence[tuple[int, int]]
) -> tuple[int, ...]:
    if initial < 1:
        raise ValueError("the initial value must be positive")
    chain = [initial]
    for modulus_factor, depth in specifications:
        if modulus_factor < 1 or depth < 1:
            raise ValueError("modulus factors and depths must be positive")
        current = chain[-1]
        quotient = 1 + modulus_factor * current**depth
        chain.append(current * quotient)
    return tuple(chain)


def construct_divisibility_tree(
    root: int,
    nodes: Sequence[tuple[int, ...]],
    thresholds: dict[tuple[int, ...], int],
) -> tuple[dict[tuple[int, ...], int], dict[tuple[int, ...], int]]:
    if not nodes or nodes[0] != () or root < 1:
        raise ValueError("nodes must begin with the root and the root value must be positive")
    values = {(): root}
    edge_quotients: dict[tuple[int, ...], int] = {}
    for node in nodes[1:]:
        parent = node[:-1]
        if parent not in values:
            raise ValueError("every parent must precede its children")
        threshold = thresholds[node]
        small_prime_product = 1
        for candidate in range(2, threshold + 1):
            if is_prime(candidate):
                small_prime_product *= candidate
        previous_product = root * small_prime_product
        for quotient in edge_quotients.values():
            previous_product *= quotient
        parent_value = values[parent]
        quotient = 1 + parent_value * previous_product
        values[node] = parent_value * quotient
        edge_quotients[node] = quotient
    return values, edge_quotients


def verify_pump_witness(
    system: LinearSystem,
    word: Word,
    cuts: tuple[int, int, int, int],
    require_canonical: bool = False,
) -> PumpWitness:
    original = value(system, word)
    if not is_prime(original):
        raise ValueError("the original word must represent a prime")
    if original and system.trailing_coefficient % original == 0:
        raise NonInvertibleAction("the represented prime divides the trailing coefficient")
    a, b, c, d = cuts
    v, y = word[a:b], word[c:d]
    orders = [
        matrix_order(block_matrix(system, block), original * original)
        for block in (v, y)
        if block
    ]
    return_time = lcm(*orders)
    exponent = 1 + return_time
    result_word = pumped_word(word, cuts, exponent)
    result_value = value(system, result_word)
    before = is_canonical(system, word)
    after = is_canonical(system, result_word)
    if require_canonical and not (before and after):
        raise AssertionError("the selected pumping does not preserve canonical syntax")
    if result_value % (original * original) != original:
        raise AssertionError("square-modulus pumping congruence failed")
    return PumpWitness(
        system=system.name,
        original_word="".join(map(str, word)),
        original_value=original,
        cuts=cuts,
        return_time=return_time,
        pump_exponent=exponent,
        pumped_length=len(result_word),
        pumped_value=result_value,
        quotient_mod_original=(result_value // original) % original,
        canonical_before=before,
        canonical_after=after,
    )


def check_affine_action(system: LinearSystem, max_length: int = 5) -> int:
    cases = 0
    initial_state = (0,) + system.initials
    for length in range(max_length + 1):
        for word in product(range(system.max_digit + 1), repeat=length):
            transformed = matvec(block_matrix(system, word), initial_state)
            expected_weights = weights(system, length + system.dimension)[length:]
            expected = (value(system, word),) + tuple(expected_weights)
            if transformed != expected:
                raise AssertionError(
                    f"affine action mismatch for {system.name}, word={word}: "
                    f"{transformed} != {expected}"
                )
            cases += 1
    return cases


def search_singular_counterexample() -> dict[str, int | str | bool]:
    system = system_by_name("quadratic_nonunit")
    matrix = block_matrix(system, (0,))
    modulus = 2
    return {
        "system": system.name,
        "polynomial": system.polynomial,
        "modulus": modulus,
        "trailing_coefficient": system.trailing_coefficient,
        "block": "0",
        "determinant": determinant(matrix),
        "invertible": gcd(determinant(matrix), modulus) == 1,
    }


def verify_inflated_fibonacci_separation(
    primes: Sequence[int] = (2, 3, 5, 7, 11, 13),
    maximum_power: int = 4,
    maximum_index: int = 24,
) -> dict[str, int]:
    """Check the ambient/reachable determinant separation for Fibonacci tails."""
    fibonacci = [1, 2]
    while len(fibonacci) <= maximum_index + 3:
        fibonacci.append(fibonacci[-1] + fibonacci[-2])

    reachable_state = (1, 2, 3)
    reachable_next = (2, 3, 5)
    reachable_action = ((0, 1), (1, 1))
    reachable_determinant = determinant(reachable_action)
    saturation_minors = (
        reachable_state[0] * reachable_next[1]
        - reachable_state[1] * reachable_next[0],
        reachable_state[0] * reachable_next[2]
        - reachable_state[2] * reachable_next[0],
        reachable_state[1] * reachable_next[2]
        - reachable_state[2] * reachable_next[1],
    )

    cases = 0
    failures = 0

    def check(condition: bool) -> None:
        nonlocal cases, failures
        cases += 1
        failures += int(not condition)

    check(gcd(*saturation_minors) == 1)
    check(reachable_determinant == -1)

    for prime in primes:
        inflated = LinearSystem(
            name=f"inflated_fibonacci_{prime}",
            polynomial=f"(x-{prime})(x^2-x-1)",
            recurrence=(-prime, 1 - prime, prime + 1),
            initials=reachable_state,
            max_digit=1,
        )
        companion = tuple(
            tuple(row[1:]) for row in digit_matrix(inflated, 0)[1:]
        )
        check(determinant(companion) == -prime)
        check(matvec(companion, reachable_state) == reachable_next)
        twice = matvec(companion, reachable_next)
        check(
            tuple(
                twice[index] - reachable_next[index] - reachable_state[index]
                for index in range(3)
            )
            == (0, 0, 0)
        )

        for index in range(maximum_index + 1):
            check(
                fibonacci[index + 3]
                == -prime * fibonacci[index]
                + (1 - prime) * fibonacci[index + 1]
                + (prime + 1) * fibonacci[index + 2]
            )

        for power in range(1, maximum_power + 1):
            modulus = prime**power
            check(gcd(determinant(companion), modulus) != 1)
            check(gcd(reachable_determinant, modulus) == 1)
            state = tuple(entry % modulus for entry in reachable_state)
            for _ in range(maximum_index + 1):
                following = tuple(entry % modulus for entry in matvec(companion, state))
                twice = tuple(entry % modulus for entry in matvec(companion, following))
                check(
                    all(
                        (twice[index] - following[index] - state[index]) % modulus
                        == 0
                        for index in range(3)
                    )
                )
                check(any(entry % modulus for entry in state))
                state = following

    return {
        "cases": cases,
        "failures": failures,
        "reachable_rank": 2,
        "reachable_determinant": reachable_determinant,
    }


def run_verification() -> dict[str, object]:
    affine_cases = sum(check_affine_action(system) for system in SYSTEMS)
    examples = (
        ("fibonacci", (0, 1, 0, 0, 0, 0, 1), (2, 3, 4, 5)),
        ("pell", (1, 0, 0, 1), (1, 2, 2, 3)),
        ("tribonacci", (0, 0, 0, 1), (0, 1, 1, 2)),
        ("quadratic_nonunit", (1, 0, 0, 1), (1, 2, 2, 3)),
        ("integer_base_2", (1, 0, 0, 0, 1), (1, 2, 2, 3)),
    )
    witnesses = []
    failures = 0
    for name, word, cuts in examples:
        try:
            witnesses.append(
                asdict(
                    verify_pump_witness(
                        system_by_name(name), word, cuts, require_canonical=True
                    )
                )
            )
        except AssertionError:
            failures += 1

    synchronized_orbit_cases = check_synchronized_orbit(
        system_by_name("fibonacci"),
        (0, 1, 0, 0, 0, 0, 1),
        ((2, 3), (4, 5)),
        moduli=range(2, 21),
        parameters=range(6),
    )
    synchronized_orbit_cases += check_synchronized_orbit(
        system_by_name("quadratic_nonunit"),
        (1, 0, 0, 1),
        ((1, 2), (2, 3)),
        moduli=range(3, 20, 2),
        parameters=range(5),
    )

    layer_point = 2 * 3 * 5**2 * 7
    excluded_primes = (2, 3)
    valuation_bounds = {2: 2, 3: 1}
    isolation_modulus = local_layer_isolation_modulus(
        layer_point, excluded_primes, valuation_bounds
    )
    layer_matches = [
        number
        for number in range(1, 50_001)
        if in_local_prime_layer(number, 2, excluded_primes, valuation_bounds)
        and (number - layer_point) % isolation_modulus == 0
    ]
    local_layer_isolation_failures = int(layer_matches != [layer_point])

    specifications = ((6, 1), (30, 2), (210, 1))
    chain = construct_deep_congruence_chain(2, specifications)
    deep_chain_failures = sum(
        following % current != 0
        or (following // current) % (modulus_factor * current**depth) != 1
        for current, following, (modulus_factor, depth) in zip(
            chain, chain[1:], specifications
        )
    )

    tree_nodes = ((), (0,), (1,), (0, 0), (0, 1), (1, 0))
    thresholds = {(0,): 3, (1,): 5, (0, 0): 7, (0, 1): 11, (1, 0): 13}
    tree_values, tree_edges = construct_divisibility_tree(2, tree_nodes, thresholds)
    divisibility_tree_failures = sum(
        (tree_values[right] % tree_values[left] == 0)
        != (right[: len(left)] == left)
        for left in tree_nodes
        for right in tree_nodes
    )
    edge_values = tuple(tree_edges.values())
    divisibility_tree_failures += sum(
        gcd(left, right) != 1
        for index, left in enumerate(edge_values)
        for right in edge_values[index + 1 :]
    )
    divisibility_tree_failures += sum(
        quotient % prime == 0
        for edge, quotient in tree_edges.items()
        for prime in range(2, thresholds[edge] + 1)
        if is_prime(prime)
    )
    inflated_fibonacci = verify_inflated_fibonacci_separation()

    transient_weights = (1, 3, 6, 12, 24, 48, 96, 192)
    transient_prefix = (2,)
    tail_prefix_cases = 0
    tail_prefix_failures = 0
    for suffix_length in range(6):
        for suffix in product((0, 1), repeat=suffix_length):
            transformed = tail_action_state(
                (-10, 7), transient_weights, transient_prefix, suffix
            )
            full_word = transient_prefix + suffix
            expected = (
                sum(
                    digit * weight
                    for digit, weight in zip(full_word, transient_weights)
                ),
                *transient_weights[
                    len(full_word) : len(full_word) + 2
                ],
            )
            tail_prefix_cases += 1
            tail_prefix_failures += int(transformed != expected)

    base_two = system_by_name("integer_base_2")
    geometric_ray_cases = 13
    geometric_ray_failures = sum(
        value(
            base_two,
            linear_mcfg_ray_word(
                prefix=(),
                constants=((), (1,)),
                left_pumps=((0,),),
                middles=((),),
                right_pumps=((),),
                exponent=exponent,
            ),
        )
        != 2**exponent
        for exponent in range(geometric_ray_cases)
    )
    return {
        "systems_checked": len(SYSTEMS),
        "affine_cases": affine_cases,
        "pump_witnesses": len(witnesses),
        "congruence_failures": failures,
        "synchronized_orbit_cases": synchronized_orbit_cases,
        "local_layer_isolation_failures": local_layer_isolation_failures,
        "deep_chain_failures": deep_chain_failures,
        "divisibility_tree_failures": divisibility_tree_failures,
        "inflated_fibonacci_cases": inflated_fibonacci["cases"],
        "inflated_fibonacci_failures": inflated_fibonacci["failures"],
        "tail_prefix_cases": tail_prefix_cases,
        "tail_prefix_failures": tail_prefix_failures,
        "geometric_ray_cases": geometric_ray_cases,
        "geometric_ray_failures": geometric_ray_failures,
        "witnesses": witnesses,
        "counterexample": search_singular_counterexample(),
    }


def _format_report(report: dict[str, object]) -> str:
    lines = [
        "LINEAR PISOT PUMPING VERIFICATION",
        f"systems checked: {report['systems_checked']}",
        f"affine action cases: {report['affine_cases']}",
        f"valid canonical pump witnesses: {report['pump_witnesses']}",
        f"congruence failures: {report['congruence_failures']}",
        f"synchronized orbit cases: {report['synchronized_orbit_cases']}",
        "local layer isolation failures: "
        f"{report['local_layer_isolation_failures']}",
        f"deep chain failures: {report['deep_chain_failures']}",
        f"divisibility tree failures: {report['divisibility_tree_failures']}",
        f"inflated Fibonacci cases: {report['inflated_fibonacci_cases']}",
        f"inflated Fibonacci failures: {report['inflated_fibonacci_failures']}",
        f"tail-prefix action cases: {report['tail_prefix_cases']}",
        f"tail-prefix action failures: {report['tail_prefix_failures']}",
        f"geometric ray cases: {report['geometric_ray_cases']}",
        f"geometric ray failures: {report['geometric_ray_failures']}",
    ]
    for witness in report["witnesses"]:
        lines.append(
            "PASS {system}: p={original_value}, k={pump_exponent}, "
            "pumped_length={pumped_length}, N(k) mod p^2=p, "
            "(N(k)/p) mod p={quotient_mod_original}".format(**witness)
        )
    counterexample = report["counterexample"]
    lines.append(
        "EXPECTED INTERFACE FAILURE {system}: polynomial={polynomial}, "
        "block={block}, modulus={modulus}, determinant={determinant}, "
        "invertible={invertible}".format(**counterexample)
    )
    failure_keys = (
        "congruence_failures",
        "local_layer_isolation_failures",
        "deep_chain_failures",
        "divisibility_tree_failures",
        "inflated_fibonacci_failures",
        "tail_prefix_failures",
        "geometric_ray_failures",
    )
    lines.append(
        "OVERALL: PASS"
        if all(report[key] == 0 for key in failure_keys)
        else "OVERALL: FAIL"
    )
    return "\n".join(lines)


if __name__ == "__main__":
    print(_format_report(run_verification()))
