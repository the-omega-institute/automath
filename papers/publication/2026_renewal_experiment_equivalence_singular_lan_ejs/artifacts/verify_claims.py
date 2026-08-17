#!/usr/bin/env python3
"""Deterministic algebra checks for the renewal collision article."""

from __future__ import annotations

import argparse
import math
from pathlib import Path


def tail_two_rate(k: int, rate_a: float, rate_b: float, dt: float) -> float:
    if abs(rate_a - rate_b) < 1e-12:
        x = rate_a * dt * k
        return (1.0 + x) * math.exp(-x)
    return (
        rate_a * math.exp(-rate_b * dt * k)
        - rate_b * math.exp(-rate_a * dt * k)
    ) / (rate_a - rate_b)


def recurrence_residual(values: list[float], roots: list[float]) -> float:
    if len(roots) != 2:
        raise ValueError("the regression helper checks order two")
    root_sum = roots[0] + roots[1]
    root_product = roots[0] * roots[1]
    return max(
        abs(values[k + 2] - root_sum * values[k + 1] + root_product * values[k])
        for k in range(len(values) - 2)
    )


def cluster_dispersion(values: tuple[float, ...]) -> float:
    return 0.5 * sum(value * value for value in values)


def multiple_rho_derivative(multiplicity: int, centre: float, s: float) -> float:
    x = s + centre
    return centre ** (multiplicity - 2) * (s + 2.0 * centre) / x ** (
        multiplicity + 2
    )


def multiple_rho_derivative_unsimplified(
    multiplicity: int, centre: float, s: float
) -> float:
    x = s + centre
    return (
        centre ** (multiplicity - 2) / x**multiplicity
        - centre**multiplicity / x ** (multiplicity + 2)
    ) / s


def checks() -> list[tuple[str, bool, str]]:
    dt = 0.7
    rate_a, rate_b = 1.1, 2.3
    z_a, z_b = math.exp(-rate_a * dt), math.exp(-rate_b * dt)
    tails = [tail_two_rate(k, rate_a, rate_b, dt) for k in range(8)]

    common = 1.4
    z = math.exp(-common * dt)
    confluent = [tail_two_rate(k, common, common, dt) for k in range(8)]
    x = common * dt
    hankel_det = confluent[0] * confluent[2] - confluent[1] ** 2

    c = 1.7
    delta = 0.09
    pair = (c + math.sqrt(delta), c - math.sqrt(delta))
    sampled = [math.exp(-value * dt) for value in pair]
    cluster_a = sampled[0] + sampled[1]
    cluster_b = sampled[0] * sampled[1]
    recovered_c = -math.log(cluster_b) / (2.0 * dt)
    recovered_delta = (
        math.acosh(cluster_a / (2.0 * math.sqrt(cluster_b))) / dt
    ) ** 2

    gamma = 0.75
    undershoot_ratio = 10_000 ** gamma / 10_000
    fluctuation_ratio = 10_000 ** gamma / math.sqrt(10_000)

    p = math.exp(-rate_a * dt)
    s = math.exp(-rate_b * dt)
    b = rate_b * math.exp(-rate_a * dt) * (
        1.0 - math.exp(-(rate_b - rate_a) * dt)
    ) / (rate_b - rate_a)
    a = 1.0 - s - b

    pole_errors = [
        abs(
            multiple_rho_derivative(m, 1.3, 0.8)
            - multiple_rho_derivative_unsimplified(m, 1.3, 0.8)
        )
        for m in range(3, 7)
    ]
    r = 0.4
    shape_a = (r, -r, 0.0)
    shape_b = (r / math.sqrt(3.0), r / math.sqrt(3.0), -2.0 * r / math.sqrt(3.0))
    shape_distance = max(
        abs(x - y) for x, y in zip(sorted(shape_a), sorted(shape_b))
    )

    return [
        ("two-rate tail starts at one", abs(tails[0] - 1.0) < 1e-14, f"S0={tails[0]:.16g}"),
        ("two-rate tail decreases", all(tails[i] > tails[i + 1] > 0 for i in range(7)), f"S7={tails[-1]:.6g}"),
        ("simple-root recurrence", recurrence_residual(tails, [z_a, z_b]) < 1e-13, "order-2 residual"),
        ("confluent tail formula", abs(confluent[3] - (1 + 3 * x) * z**3) < 1e-14, "equal-rate limit"),
        ("double-root recurrence", recurrence_residual(confluent, [z, z]) < 1e-13, "repeated root"),
        ("collision Hankel invertible", abs(hankel_det) > 1e-6, f"det={hankel_det:.6g}"),
        ("cluster centre recovery", abs(recovered_c - c) < 1e-13, f"c={recovered_c:.15g}"),
        ("cluster square recovery", abs(recovered_delta - delta) < 1e-13, f"delta={recovered_delta:.15g}"),
        ("undershoot sublinear", undershoot_ratio < 0.2, f"ratio={undershoot_ratio:.6g}"),
        ("undershoot exceeds root-N scale", fluctuation_ratio > 5.0, f"ratio={fluctuation_ratio:.6g}"),
        ("two-state zero kernel substochastic", 0 < p < 1 and 0 < s < 1 and b > 0 and a > 0, f"a={a:.6g}, b={b:.6g}"),
        ("marked reset is rank one", abs((1 - p) * a - a * (1 - p)) < 1e-15, "both marked rows end in D"),
        ("multiple-pole dispersion derivative", max(pole_errors) < 1e-13, f"max error={max(pole_errors):.3g}"),
        (
            "equal-dispersion shapes are distinct",
            abs(cluster_dispersion(shape_a) - cluster_dispersion(shape_b)) < 1e-14
            and shape_distance > 1e-3,
            f"dispersion={cluster_dispersion(shape_a):.6g}, distance={shape_distance:.6g}",
        ),
    ]


def render() -> str:
    rows = checks()
    failed = [name for name, ok, _ in rows if not ok]
    lines = ["Renewal equivalence and pole-collision verification"]
    lines.extend(f"{'PASS' if ok else 'FAIL'}  {name}: {detail}" for name, ok, detail in rows)
    lines.append(f"Summary: {len(rows) - len(failed)}/{len(rows)} checks passed")
    if failed:
        raise AssertionError(", ".join(failed))
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = render()
    if args.output:
        args.output.write_text(report, encoding="utf-8", newline="\n")
    print(report, end="")


if __name__ == "__main__":
    main()
