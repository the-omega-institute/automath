#!/usr/bin/env python3
"""Numerical audit of real-tilt pressure, freezing, and Legendre rates."""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter
from pathlib import Path

import mpmath


def fibonacci_through(n: int) -> list[int]:
    values = [0, 1]
    while len(values) <= n:
        values.append(values[-1] + values[-2])
    return values


def extend_coefficients(coefficients: list[int], weight: int) -> list[int]:
    result = [0] * (len(coefficients) + weight)
    for index, value in enumerate(coefficients):
        result[index] += value
        result[index + weight] += value
    return result


def log_partition_derivatives(
    levels: Counter[int], tilt: float
) -> tuple[float, float, float]:
    terms = [
        (math.log(count) + tilt * math.log(level), math.log(level))
        for level, count in levels.items()
    ]
    maximum = max(term for term, _ in terms)
    weights = [math.exp(term - maximum) for term, _ in terms]
    normalizer = sum(weights)
    mean = sum(weight * log_level for weight, (_, log_level) in zip(weights, terms))
    mean /= normalizer
    variance = sum(
        weight * (log_level - mean) ** 2
        for weight, (_, log_level) in zip(weights, terms)
    ) / normalizer
    return maximum + math.log(normalizer), mean, variance


def totients_through(n: int) -> list[int]:
    values = list(range(n + 1))
    for prime in range(2, n + 1):
        if values[prime] == prime:
            for multiple in range(prime, n + 1, prime):
                values[multiple] -= values[multiple] // prime
    return values


def weinstein_psi_through(n: int) -> list[int]:
    totients = totients_through(n)
    psi = [0] * (n + 1)
    psi[1] = 1
    for value in range(2, n + 1):
        psi[value] = sum(
            psi[value // divisor] * totients[divisor]
            for divisor in range(2, value + 1)
            if value % divisor == 0
        )
    return psi


def ordinary_partition_values(limit: int, weights: list[int]) -> list[int]:
    values = [0] * (limit + 1)
    values[0] = 1
    for weight in weights:
        for index in range(limit, weight - 1, -1):
            values[index] += values[index - weight]
    return values


def compositions(total: int):
    """Yield all ordered compositions of a positive integer."""
    for mask in range(1 << (total - 1)):
        parts = []
        current = 1
        for index in range(total - 1):
            if mask & (1 << index):
                parts.append(current)
                current = 1
            else:
                current += 1
        parts.append(current)
        yield tuple(parts)


def negative_continuant(entries: tuple[int, ...]) -> int:
    previous_previous = 1
    previous = entries[0]
    for entry in entries[1:]:
        previous_previous, previous = previous, entry * previous - previous_previous
    return previous


def negative_continued_fraction_value(
    composition: tuple[int, ...],
) -> tuple[int, int]:
    """Return p, q for the negative continued fraction with a_i=e_i+1."""
    entries = tuple(part + 1 for part in composition)
    denominator = negative_continuant(entries)
    numerator = 1 if len(entries) == 1 else negative_continuant(entries[1:])
    common = math.gcd(numerator, denominator)
    return numerator // common, denominator // common


def regular_partial_quotient_sum(numerator: int, denominator: int) -> int:
    """Sum the canonical regular partial quotients of p/q in (0, 1)."""
    if not 0 < numerator < denominator or math.gcd(numerator, denominator) != 1:
        raise ValueError("expected a reduced fraction in (0, 1)")
    total = 0
    left, right = denominator, numerator
    while right:
        quotient, remainder = divmod(left, right)
        total += quotient
        left, right = right, remainder
    return total


def dyadic_generator_cost_counters(max_exponent: int) -> list[Counter[int]]:
    """Count free generator words by total dyadic exponent and layer cost."""
    if max_exponent < 1:
        raise ValueError("max_exponent must be positive")
    letters = [Counter() for _ in range(max_exponent + 1)]
    for exponent in range(1, max_exponent + 1):
        denominator = 2**exponent
        for numerator in range(1, denominator, 2):
            cost = 2 * regular_partial_quotient_sum(numerator, denominator) - 1
            letters[exponent][cost] += 1

    generators = [Counter() for _ in range(max_exponent + 1)]
    generators[0][0] = 1
    for exponent in range(1, max_exponent + 1):
        for letter_exponent in range(1, exponent + 1):
            for prefix_cost, prefix_count in generators[
                exponent - letter_exponent
            ].items():
                for letter_cost, letter_count in letters[letter_exponent].items():
                    generators[exponent][prefix_cost + letter_cost] += (
                        prefix_count * letter_count
                    )
    return generators


def dyadic_finite_window_count(m: int, cost_counter: Counter[int]) -> int:
    """Apply the adjacent-layer orbit weights to a dyadic cost counter."""
    total = 0
    for cost, count in cost_counter.items():
        if cost <= m - 1:
            weight = 4
        elif cost == m:
            weight = 3
        elif cost == m + 1:
            weight = 1
        else:
            weight = 0
        total += weight * count
    return total


def stern_brocot_layer_denominators(depth: int) -> list[int]:
    """Denominators in the new Stern--Brocot layer of composition depth d."""
    if depth < 1:
        raise ValueError("depth must be positive")
    return [
        negative_continuant(tuple(part + 1 for part in composition))
        for composition in compositions(depth)
    ]


def critical_slope_partial(
    sigma: float, max_denominator: int
) -> tuple[float, float, float]:
    """Truncate the two absolutely convergent critical slope moments."""
    numerator_sum = 0.0
    denominator_sum = 0.0
    for denominator in range(2, max_denominator + 1):
        weight = denominator ** (-sigma)
        log_denominator = math.log(denominator)
        for numerator in range(1, denominator):
            if math.gcd(numerator, denominator) != 1:
                continue
            digit_sum = regular_partial_quotient_sum(numerator, denominator)
            cost = 2 * digit_sum - 1
            numerator_sum += weight * log_denominator
            denominator_sum += weight * cost
    return numerator_sum, denominator_sum, numerator_sum / denominator_sum


def weighted_generator_counters(max_layer: int) -> list[Counter[int]]:
    """Return exact multiplicity counters for generator weights at each cost."""
    letters = [Counter() for _ in range(max_layer + 1)]
    for cost_sum in range(1, (max_layer - 1) // 2 + 1):
        cost = 2 * cost_sum + 1
        for composition in compositions(cost_sum):
            denominator = negative_continuant(
                tuple(part + 1 for part in composition)
            )
            letters[cost][denominator] += 1

    generators = [Counter() for _ in range(max_layer + 1)]
    generators[0][1] = 1
    for total_cost in range(1, max_layer + 1):
        for letter_cost in range(1, total_cost + 1):
            for denominator, letter_count in letters[letter_cost].items():
                for weight, word_count in generators[
                    total_cost - letter_cost
                ].items():
                    generators[total_cost][denominator * weight] += (
                        letter_count * word_count
                    )
    return generators


def marked_window_counter(
    m: int, generators: list[Counter[int]]
) -> Counter[tuple[int, int]]:
    """Count nonunit fibers jointly by generator cost and multiplicity."""
    if m < 1 or len(generators) <= m + 1:
        raise ValueError("generator table must include costs through m + 1")
    marked: Counter[tuple[int, int]] = Counter()
    for cost, generator_levels in enumerate(generators):
        if cost <= m - 1:
            orbit_weight = 4
        elif cost == m:
            orbit_weight = 3
        elif cost == m + 1:
            orbit_weight = 1
        else:
            orbit_weight = 0
        if orbit_weight == 0:
            continue
        for level, word_count in generator_levels.items():
            if level > 1:
                marked[cost, level] += orbit_weight * word_count
    return marked


def conditional_marked_scan(
    windows: tuple[int, ...],
    generators: list[Counter[int]],
    bands: tuple[tuple[float, float], ...],
) -> list[tuple[int, float, float, int, float, float]]:
    """Return exact finite-window conditional energy and generator-cost means."""
    if not windows or min(windows) < 1 or len(generators) <= max(windows) + 1:
        raise ValueError("generator table must cover every requested window")
    rows = []
    for m in windows:
        marked = marked_window_counter(m, generators)
        for alpha, epsilon in bands:
            if not 0.0 < epsilon < alpha:
                raise ValueError("each band must satisfy 0 < epsilon < alpha")
            selected = [
                (cost, math.log(level), count)
                for (cost, level), count in marked.items()
                if abs(math.log(level) / m - alpha) < epsilon
            ]
            total = sum(count for _, _, count in selected)
            if total == 0:
                rows.append((m, alpha, epsilon, 0, math.nan, math.nan))
                continue
            mean_energy = sum(log_level * count for _, log_level, count in selected)
            mean_cost = sum(cost * count for cost, _, count in selected)
            rows.append(
                (
                    m,
                    alpha,
                    epsilon,
                    total,
                    mean_energy / (m * total),
                    mean_cost / (m * total),
                )
            )
    return rows


def weighted_renewal_counterexample_search(
    max_layer: int, fib: list[int], sigma: float, beta_star: float
) -> tuple[list[int], int, int]:
    """Check the weighted renewal identity coefficientwise and at real tilts."""
    limit = fib[max_layer + 2] - 2
    ordinary = ordinary_partition_values(
        limit, [fib[index] for index in range(2, max_layer + 2)]
    )
    generators = weighted_generator_counters(max_layer)
    failed_layers = []
    symbolic_checks = 0
    real_tilt_checks = 0
    real_tilts = [
        -4.0,
        -1.0,
        0.0,
        1.0,
        2.0,
        beta_star,
        (beta_star + sigma) / 2.0,
        sigma,
        3.0,
        5.0,
    ]

    for layer in range(1, max_layer + 1):
        actual = Counter(
            ordinary[fib[layer + 1] - 1 : fib[layer + 2] - 1]
        )
        predicted = Counter({1: 1})
        predicted.update(generators[layer])
        for generator_cost in range(1, layer):
            for level, count in generators[generator_cost].items():
                predicted[level] += 2 * count
        symbolic_checks += 1
        if predicted != actual:
            failed_layers.append(layer)

    for tilt in real_tilts:
        generator_weights = [
            sum(count * level ** (-tilt) for level, count in counter.items())
            for counter in generators
        ]
        for m in range(1, max_layer):
            actual = sum(
                level ** (-tilt)
                for level in ordinary[
                    fib[m + 1] - 1 : fib[m + 3] - 1
                ]
            )
            predicted = (
                4.0 * sum(generator_weights[:m])
                + 3.0 * generator_weights[m]
                + generator_weights[m + 1]
                - 2.0
            )
            real_tilt_checks += 1
            tolerance = 2.0e-11 * max(1.0, abs(actual))
            if abs(actual - predicted) > tolerance and m not in failed_layers:
                failed_layers.append(m)

    return sorted(set(failed_layers)), symbolic_checks, real_tilt_checks


def layer_bound_counterexample_search(max_layer: int, fib: list[int]) -> tuple[int, int]:
    limit = fib[max_layer + 2] - 2
    ordinary = ordinary_partition_values(
        limit, [fib[index] for index in range(2, max_layer + 2)]
    )
    maximum_level = max(ordinary)
    psi = weinstein_psi_through(maximum_level)
    failures = 0
    stability_checks = 0
    for layer in range(2, max_layer + 1):
        counts = Counter(
            ordinary[fib[layer + 1] - 1 : fib[layer + 2] - 1]
        )
        if counts[1] != 1:
            failures += 1
        failures += sum(
            count > 2 * psi[level]
            for level, count in counts.items()
            if level > 1
        )
        if layer >= 4:
            stability_checks += 1
            failures += counts[2] != 2 * psi[2]
        for level in range(3, min(maximum_level, layer // 2) + 1):
            stability_checks += 1
            failures += counts[level] != 2 * psi[level]
    return failures, stability_checks


def orbit_padding_counterexample_search(
    max_source: int, max_target: int, fib: list[int]
) -> tuple[list[str], int, int]:
    """Audit the two exact counting inequalities used by orbit padding."""
    if max_source < 1 or max_target <= max_source + 1:
        raise ValueError("expected 1 <= max_source < max_target - 1")
    if len(fib) <= max_target + 2:
        raise ValueError("Fibonacci table is too short for the requested layers")

    limit = fib[max_target + 2] - 2
    ordinary = ordinary_partition_values(
        limit, [fib[index] for index in range(2, max_target + 2)]
    )
    generators = weighted_generator_counters(max_target)
    cumulative_generators: list[Counter[int]] = []
    running: Counter[int] = Counter()
    for counter in generators:
        running.update(counter)
        cumulative_generators.append(running.copy())

    failures: list[str] = []
    capacity_checks = 0
    padding_checks = 0
    for source in range(1, max_source + 1):
        source_levels = Counter(
            ordinary[fib[source + 1] - 1 : fib[source + 3] - 1]
        )
        available = cumulative_generators[source + 1]
        for level, source_count in source_levels.items():
            if level == 1:
                continue
            capacity_checks += 1
            if source_count > 4 * available[level]:
                failures.append(
                    f"capacity(source={source},level={level},"
                    f"states={source_count},generators={available[level]})"
                )

        for target in range(source + 2, max_target + 1):
            target_layer = Counter(
                ordinary[fib[target + 1] - 1 : fib[target + 2] - 1]
            )
            for level, generator_count in available.items():
                if level == 1 or generator_count == 0:
                    continue
                padding_checks += 1
                if target_layer[level] < generator_count:
                    failures.append(
                        f"padding(source={source},target={target},level={level},"
                        f"target_states={target_layer[level]},"
                        f"generators={generator_count})"
                    )
    return failures, capacity_checks, padding_checks


def coexistence_local_counterexample_search(
    windows: tuple[int, ...],
    fib: list[int],
    sigma: float,
    bands: tuple[tuple[float, float], ...],
) -> tuple[list[str], int, list[tuple[int, float, float, int, float, float, float]]]:
    """Audit the critical local-count bound and record coexistence entropies."""
    if not windows or min(windows) < 1 or tuple(sorted(windows)) != windows:
        raise ValueError("windows must be a nonempty increasing tuple")
    if len(fib) <= max(windows) + 2:
        raise ValueError("Fibonacci table is too short for the requested windows")
    if sigma <= 0.0 or not bands:
        raise ValueError("sigma and the local bands must be positive")

    failures: list[str] = []
    rows: list[tuple[int, float, float, int, float, float, float]] = []
    coefficients = [1]
    selected = set(windows)
    for m in range(1, max(windows) + 1):
        coefficients = extend_coefficients(coefficients, fib[m])
        if m not in selected:
            continue
        levels = Counter(coefficients)
        log_critical_sum = log_partition_derivatives(levels, -sigma)[0]
        for alpha, epsilon in bands:
            if not 0.0 < epsilon < alpha:
                raise ValueError("each band must satisfy 0 < epsilon < alpha")
            count = sum(
                multiplicity
                for level, multiplicity in levels.items()
                if abs(math.log(level) / m - alpha) < epsilon
            )
            log_count = math.log(count) if count else -math.inf
            critical_margin = (
                log_critical_sum
                - log_count
                + sigma * m * (alpha + epsilon)
            )
            if count == 0 or critical_margin < -1.0e-12:
                failures.append(
                    f"window={m},alpha={alpha},epsilon={epsilon},"
                    f"count={count},critical_margin={critical_margin}"
                )
            rows.append(
                (
                    m,
                    alpha,
                    epsilon,
                    count,
                    log_count / m,
                    sigma * alpha,
                    critical_margin,
                )
            )
    return failures, len(rows), rows


def exact_maximum_fiber(m: int, fib: list[int]) -> int:
    if m <= 1:
        return 1
    if m % 2 == 0:
        return fib[m // 2 + 2]
    return 2 * fib[(m - 1) // 2 + 1]


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=32)
    parser.add_argument("--max-layer", type=int, default=22)
    parser.add_argument(
        "--pressure-csv",
        type=Path,
        default=Path(__file__).with_name("real_tilt_pressure.csv"),
    )
    parser.add_argument(
        "--rate-csv",
        type=Path,
        default=Path(__file__).with_name("real_tilt_rate.csv"),
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=Path(__file__).with_name("real_tilt_verification.txt"),
    )
    args = parser.parse_args()
    if args.max_m < 24:
        parser.error("--max-m must be at least 24")

    fib = fibonacci_through(max(args.max_m + 3, args.max_layer + 3))
    sigma = float(
        mpmath.findroot(
            lambda value: mpmath.zeta(value - 1) / mpmath.zeta(value) - 2,
            (2.2, 3.0),
        )
    )
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    beta_star = math.log(phi) / math.log(2.0 / phi)
    snapshot_indices = sorted({12, 16, 20, 24, 28, args.max_m})
    selected_tilts = [
        -8.0,
        -6.0,
        -5.0,
        -4.0,
        -3.0,
        -sigma,
        -2.0,
        -1.0,
        0.0,
        1.0,
        2.0,
        5.0,
        10.0,
    ]
    derivative_grid = [value / 4 for value in range(-32, 41)]
    rate_tilts = [value / 10 for value in range(-80, 121)]

    snapshots: dict[int, Counter[int]] = {}
    coefficients = [1]
    for m in range(1, args.max_m + 1):
        coefficients = extend_coefficients(coefficients, fib[m])
        if m in snapshot_indices:
            snapshots[m] = Counter(coefficients)

    layer_failures, layer_stability_checks = layer_bound_counterexample_search(
        args.max_layer, fib
    )
    failures = layer_failures
    padding_failures, orbit_capacity_checks, orbit_padding_checks = (
        orbit_padding_counterexample_search(
            min(args.max_layer - 2, 16), args.max_layer, fib
        )
    )
    failures += len(padding_failures)
    coexistence_failures, coexistence_checks, coexistence_rows = (
        coexistence_local_counterexample_search(
            tuple(snapshot_indices),
            fib,
            sigma,
            ((0.04, 0.02), (0.08, 0.02), (0.12, 0.02)),
        )
    )
    failures += len(coexistence_failures)
    renewal_failed_layers, renewal_symbolic_checks, renewal_real_tilt_checks = (
        weighted_renewal_counterexample_search(
            args.max_layer, fib, sigma, beta_star
        )
    )
    failures += len(renewal_failed_layers)
    marked_generators = weighted_generator_counters(args.max_layer)
    marked_windows = tuple(
        window for window in (12, 16, 20) if window + 1 <= args.max_layer
    )
    marked_fixed_rows = conditional_marked_scan(
        marked_windows, marked_generators, ((0.08, 0.02),)
    )
    marked_diagonal_rows = [
        conditional_marked_scan(
            (window,), marked_generators, ((0.08, 1.0 / window),)
        )[0]
        for window in marked_windows
        if 1.0 / window < 0.08
    ]
    marked_failures = sum(
        count == 0
        or not alpha - epsilon < mean_energy < alpha + epsilon
        or not 0.0 < mean_cost <= 1.0
        for _, alpha, epsilon, count, mean_energy, mean_cost
        in marked_fixed_rows + marked_diagonal_rows
    )
    failures += marked_failures
    dyadic_counters = dyadic_generator_cost_counters(8)
    dyadic_total_checks = [
        sum(dyadic_counters[exponent].values()) == 3 ** (exponent - 1)
        for exponent in range(1, len(dyadic_counters))
    ]
    dyadic_window_checks = [
        dyadic_finite_window_count(m, dyadic_counters[exponent])
        == snapshots[m][2**exponent]
        for m in snapshot_indices
        for exponent in range(2, len(dyadic_counters))
    ]
    dyadic_failures = sum(
        not check for check in dyadic_total_checks + dyadic_window_checks
    )
    failures += dyadic_failures
    dyadic_mean_costs = [
        (
            exponent,
            sum(
                cost * count
                for cost, count in dyadic_counters[exponent].items()
            )
            / (exponent * 3 ** (exponent - 1)),
        )
        for exponent in range(1, len(dyadic_counters))
    ]
    heavy_letter_checks = []
    for denominator in range(2, 101):
        cost = 2 * regular_partial_quotient_sum(1, denominator) - 1
        heavy_letter_checks.append(cost == 2 * denominator - 1)
    heavy_letter_checks.extend(
        [
            abs(199.0 / 100.0 - 2.0) < 0.02,
            math.log(100.0) / 100.0 < 0.05,
        ]
    )
    heavy_letter_failures = sum(not check for check in heavy_letter_checks)
    failures += heavy_letter_failures
    maximum_fiber = max(
        exact_maximum_fiber(m, fib) for m in range(1, args.max_m + 1)
    )
    psi = weinstein_psi_through(maximum_fiber)
    pressure_rows: list[dict[str, object]] = []
    rate_rows: list[dict[str, object]] = []
    messages = [
        "REAL-TILT PRESSURE / LDP NUMERICAL VERIFICATION",
        f"sigma_0={sigma:.15f}",
        f"window_battery={snapshot_indices}",
        f"tilt_grid=[{derivative_grid[0]:.2f},{derivative_grid[-1]:.2f}] step=0.25",
        f"layer_bound_counterexample_search=2..{args.max_layer}",
        f"layer_stability_checks={layer_stability_checks}",
        f"layer_bound_counterexamples={layer_failures}",
        "ORBIT_PADDING capacity_checks={} padding_checks={} failures={}".format(
            orbit_capacity_checks, orbit_padding_checks, padding_failures
        ),
        "COEXISTENCE_LOCAL checks={} failures={} final_rows={}".format(
            coexistence_checks,
            coexistence_failures,
            [
                (
                    alpha,
                    count,
                    round(entropy, 9),
                    round(predicted, 9),
                    round(margin, 9),
                )
                for m, alpha, _, count, entropy, predicted, margin
                in coexistence_rows
                if m == snapshot_indices[-1]
            ],
        ),
        "WEIGHTED_RENEWAL symbolic_checks={} real_tilt_checks={} "
        "failed_layers={}".format(
            renewal_symbolic_checks,
            renewal_real_tilt_checks,
            renewal_failed_layers,
        ),
        "MARKED_CONDITIONAL fixed_rows={} diagonal_rows={} failures={}".format(
            marked_fixed_rows, marked_diagonal_rows, marked_failures
        ),
        "DYADIC_EXACT exponents=1..{} total_checks={} window_checks={} "
        "mean_cost_over_exponent={} failures={}".format(
            len(dyadic_counters) - 1,
            len(dyadic_total_checks),
            len(dyadic_window_checks),
            dyadic_mean_costs,
            dyadic_failures,
        ),
        "HEAVY_LETTER q=2..100 exact_cost_checks={} energy_over_q={:.9f} "
        "failures={}".format(
            len(heavy_letter_checks) - 2,
            math.log(100.0) / 100.0,
            heavy_letter_failures,
        ),
    ]

    previous_logs: dict[float, tuple[int, float]] = {}
    local_spectrum_checks = 0
    pressure_bound_checks = 0
    for m, levels in sorted(snapshots.items()):
        local_spectrum_checks += 1
        failures += levels[1] != 2
        for level, count in levels.items():
            if level >= 2:
                local_spectrum_checks += 1
                failures += count > 4 * psi[level]
        for level in range(2, min(max(levels), m // 2) + 1):
            local_spectrum_checks += 1
            failures += levels[level] != 4 * psi[level]

        derivatives = []
        curvatures = []
        for tilt in derivative_grid:
            log_sum, first, second = log_partition_derivatives(levels, tilt)
            derivatives.append(first / m)
            curvatures.append(second / m)
        derivative_violations = sum(
            right < left - 1.0e-12
            for left, right in zip(derivatives, derivatives[1:])
        )
        curvature_violations = sum(value < -1.0e-13 for value in curvatures)
        failures += derivative_violations + curvature_violations

        messages.append(
            "ANALYTIC_CONVEXITY m={} derivative_monotonicity_violations={} "
            "negative_curvatures={} min_curvature={:.3e}".format(
                m,
                derivative_violations,
                curvature_violations,
                min(curvatures),
            )
        )
        for tilt in selected_tilts:
            log_sum, first, second = log_partition_derivatives(levels, tilt)
            increment = math.nan
            if tilt in previous_logs:
                previous_m, previous_log = previous_logs[tilt]
                increment = (log_sum - previous_log) / (m - previous_m)
            previous_logs[tilt] = (m, log_sum)
            pressure_rows.append(
                {
                    "m": m,
                    "t": f"{tilt:.15f}",
                    "P_m": f"{log_sum / m:.15f}",
                    "P_m_prime": f"{first / m:.15f}",
                    "P_m_second": f"{second / m:.15f}",
                    "log_sum_increment": ""
                    if math.isnan(increment)
                    else f"{increment:.15f}",
                }
            )

        for exponent in (0.5, 1.0, 2.0, sigma - 0.01):
            log_sum, _, _ = log_partition_derivatives(levels, -exponent)
            log_cardinality = math.log(fib[m + 2])
            jensen_lower = log_cardinality - exponent * (
                m * math.log(2.0) - log_cardinality
            )
            a = sigma + 1.0
            psi_series = 1.0 / (
                2.0 - float(mpmath.zeta(a - 1) / mpmath.zeta(a))
            ) - 1.0
            upper = math.log(
                2.0 + 4.0 * max(levels) ** (a - exponent) * psi_series
            )
            pressure_bound_checks += 2
            failures += log_sum + 1.0e-11 < jensen_lower
            failures += log_sum > min(log_cardinality, upper) + 1.0e-11

        log_cardinality = math.log(fib[m + 2])
        cgfs = []
        for tilt in rate_tilts:
            log_sum, _, _ = log_partition_derivatives(levels, tilt)
            cgfs.append((log_sum - log_cardinality) / m)
        _, mean_log, _ = log_partition_derivatives(levels, 0.0)
        mean_alpha = mean_log / m
        alpha_max = math.log(max(levels)) / m
        alphas = sorted(
            set([alpha_max * index / 100 for index in range(101)] + [mean_alpha])
        )
        rates = [
            max(tilt * alpha - cgf for tilt, cgf in zip(rate_tilts, cgfs))
            for alpha in alphas
        ]
        secants = [
            (right_rate - left_rate) / (right_alpha - left_alpha)
            for left_alpha, right_alpha, left_rate, right_rate in zip(
                alphas, alphas[1:], rates, rates[1:]
            )
        ]
        rate_violations = sum(
            right < left - 1.0e-9 for left, right in zip(secants, secants[1:])
        )
        negative_rates = sum(rate < -1.0e-10 for rate in rates)
        mean_rate = rates[alphas.index(mean_alpha)]
        failures += rate_violations + negative_rates + (abs(mean_rate) > 1.0e-9)
        messages.append(
            "LEGENDRE_RATE m={} convexity_violations={} negative_rates={} "
            "I_m(mean)={:.3e} alpha_mean={:.9f} alpha_max={:.9f}".format(
                m,
                rate_violations,
                negative_rates,
                mean_rate,
                mean_alpha,
                alpha_max,
            )
        )
        for alpha, rate in zip(alphas, rates):
            rate_rows.append(
                {
                    "m": m,
                    "alpha": f"{alpha:.15f}",
                    "I_m": f"{rate:.15f}",
                }
            )

    final_m = max(snapshots)
    final_levels = snapshots[final_m]
    frozen_lines = []
    for tilt in (-8.0, -6.0, -5.0, -4.0, -3.0):
        log_sum, first, second = log_partition_derivatives(final_levels, tilt)
        frozen_lines.append(
            "t={:.1f}: log(S_t)={:.9f}, P_m={:.9f}, P_m'={:.3e}, P_m''={:.3e}".format(
                tilt, log_sum, log_sum / final_m, first / final_m, second / final_m
            )
        )
    messages.append("FROZEN_PHASE_FINITE_WINDOW m={}: {}".format(final_m, "; ".join(frozen_lines)))
    messages.append(
        "COUNTEREXAMPLE_TO_REQUESTED_GLOBAL_STRICT_CONVEXITY="
        "analytic theorem gives P(t)=0 for all t<=-sigma_0 while P(0)=log(phi)"
    )

    kappa = float(
        -mpmath.diff(
            lambda value: mpmath.zeta(value - 1) / mpmath.zeta(value), sigma
        )
    )
    rho = max(
        float(root.real)
        for root in mpmath.polyroots([1.0, -2.0, -2.0, 2.0])
        if abs(float(root.imag)) < 1.0e-12
    )
    constant_checks = [
        abs(sigma - 2.4787507857339603) < 1.0e-14,
        abs(kappa - 2.589184379946924) < 1.0e-13,
        abs(beta_star - 2.270559453959664) < 1.0e-13,
        abs(rho - 2.481194304092016) < 1.0e-13,
    ]
    failures += sum(not check for check in constant_checks)
    messages.append(
        "LOCAL_SPECTRUM checks={} failures_so_far={}".format(
            local_spectrum_checks, failures
        )
    )
    messages.append(
        "CRITICAL_CONSTANTS kappa={:.15f} beta_star={:.15f} "
        "strip_width={:.15f} rho={:.15f}".format(
            kappa, beta_star, sigma - beta_star, rho
        )
    )

    maximum_depth = (args.max_layer - 1) // 2
    all_real_layer_checks = 0
    all_real_layer_failures = 0
    for depth in range(1, maximum_depth + 1):
        denominators = stern_brocot_layer_denominators(depth)
        checks = [
            len(denominators) == 2 ** (depth - 1),
            min(denominators) >= depth + 1,
            max(denominators) <= fib[depth + 2],
            sum(denominators) == 2 * 3 ** (depth - 1),
        ]
        for composition in compositions(depth):
            numerator, denominator = negative_continued_fraction_value(composition)
            checks.append(
                regular_partial_quotient_sum(numerator, denominator) - 1
                == depth
            )
        all_real_layer_checks += len(checks)
        all_real_layer_failures += sum(not check for check in checks)

    exact_root_checks = [
        abs((1.0 / phi) ** 3 / (1.0 - 2.0 / phi**2) - 1.0)
        < 1.0e-14,
        abs(2.0 * 0.5**3 / (1.0 - 3.0 * 0.5**2) - 1.0)
        < 1.0e-14,
        1.0 / phi < 1.0 / math.sqrt(2.0),
        0.5 < 1.0 / math.sqrt(3.0),
    ]
    b_at_sigma = float(mpmath.zeta(sigma - 1) / mpmath.zeta(sigma) - 1)
    b_below_sigma = float(
        mpmath.zeta(sigma - 0.05 - 1) / mpmath.zeta(sigma - 0.05) - 1
    )
    b_above_sigma = float(
        mpmath.zeta(sigma + 0.05 - 1) / mpmath.zeta(sigma + 0.05) - 1
    )
    root_phase_checks = [
        abs(b_at_sigma - 1.0) < 1.0e-13,
        b_below_sigma > 1.0,
        b_above_sigma < 1.0,
    ]
    slope_rows = []
    for cutoff in (100, 300, 1000):
        slope_numerator, slope_denominator, slope = critical_slope_partial(
            sigma, cutoff
        )
        slope_rows.append((cutoff, slope_numerator, slope_denominator, slope))
    slope_checks = [
        all(
            math.isfinite(value) and value > 0.0
            for _, numerator, denominator, slope in slope_rows
            for value in (numerator, denominator, slope)
        ),
        all(
            right[1] > left[1] and right[2] > left[2]
            for left, right in zip(slope_rows, slope_rows[1:])
        ),
    ]
    all_real_failures = (
        all_real_layer_failures
        + sum(not check for check in exact_root_checks)
        + sum(not check for check in root_phase_checks)
        + sum(not check for check in slope_checks)
    )
    failures += all_real_failures
    messages.append(
        "ALL_REAL_LAYER_AUDIT depths=1..{} checks={} failures={}".format(
            maximum_depth, all_real_layer_checks, all_real_layer_failures
        )
    )
    messages.append(
        "ALL_REAL_ROOT_AUDIT exact_special_checks={} phase_values={} "
        "failures={}".format(
            exact_root_checks,
            (b_below_sigma, b_at_sigma, b_above_sigma),
            sum(not check for check in exact_root_checks + root_phase_checks),
        )
    )
    messages.append(
        "CRITICAL_SLOPE partial_rows={} checks={} failures={}".format(
            slope_rows, slope_checks, sum(not check for check in slope_checks)
        )
    )

    critical_rows = []
    for delta in (1.0e-2, 1.0e-3, 1.0e-4):
        exponent = sigma + delta

        def spectral_zeta(value: float) -> mpmath.mpf:
            return 4.0 / (
                2.0 - mpmath.zeta(value - 1) / mpmath.zeta(value)
            ) - 2.0

        normalizer = spectral_zeta(exponent)
        log_normalizer = lambda value: mpmath.log(spectral_zeta(value))
        mean_log = -mpmath.diff(log_normalizer, exponent)
        variance_log = mpmath.diff(log_normalizer, exponent, 2)
        critical_rows.append(
            (
                delta,
                float(normalizer * kappa * delta / 4.0),
                float(mean_log * delta),
                float(variance_log * delta * delta),
            )
        )
    pole_ratio, mean_ratio, variance_ratio = critical_rows[-1][1:]
    failures += abs(pole_ratio - 1.0) > 1.0e-3
    failures += abs(mean_ratio - 1.0) > 1.0e-3
    failures += abs(variance_ratio - 1.0) > 1.0e-3
    messages.append(f"CRITICAL_GIBBS scaled_rows={critical_rows}")

    tauber_x = min(maximum_fiber, 2000)
    cumulative = sum(psi[1 : tauber_x + 1])
    weighted = sum(
        psi[level] / level**sigma for level in range(2, tauber_x + 1)
    )
    predicted_cumulative = tauber_x**sigma / (sigma * kappa)
    predicted_weighted = math.log(tauber_x) / kappa
    messages.append(
        "TAUBER_FINITE_SCAN x={} cumulative_ratio={:.9f} "
        "critical_weight_ratio={:.9f}".format(
            tauber_x,
            cumulative / predicted_cumulative,
            weighted / predicted_weighted,
        )
    )
    messages.append(f"PRESSURE_BOUND finite_checks={pressure_bound_checks}")

    write_csv(
        args.pressure_csv,
        ["m", "t", "P_m", "P_m_prime", "P_m_second", "log_sum_increment"],
        pressure_rows,
    )
    write_csv(args.rate_csv, ["m", "alpha", "I_m"], rate_rows)
    messages.extend(
        [
            f"pressure_csv={args.pressure_csv.resolve()}",
            f"rate_csv={args.rate_csv.resolve()}",
            f"failures={failures}",
            "RESULT: 0 numerical failures / full-LDP orbit-padding audit passed"
            if failures == 0
            else "RESULT: VERIFICATION FAILED",
        ]
    )
    report = "\n".join(messages) + "\n"
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(report, encoding="ascii")
    print(report, end="")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
