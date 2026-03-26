#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Directed rewrite normalization for Fold_infty on configuration space.

Outputs:
- artifacts/export/fold_infty_rewrite_stats.json (default)
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir
from common_phi_fold import Progress, fib_upto, zeckendorf_digits


def _ensure_len(a: List[int], idx: int) -> None:
    if idx >= len(a):
        a.extend([0] * (idx + 1 - len(a)))


def _trim(a: List[int]) -> List[int]:
    i = len(a)
    while i > 0 and a[i - 1] == 0:
        i -= 1
    return a[:i]


def config_val(a: List[int]) -> int:
    if not a:
        return 0
    fib = fib_upto(len(a) + 2)  # F_1..F_{m+2}
    total = 0
    for k, ak in enumerate(a, start=1):
        if ak:
            total += ak * fib[k]  # F_{k+1}
    return total


def canonical_digits_from_val(N: int) -> List[int]:
    if N <= 0:
        return []
    fib = [1, 1]
    while fib[-1] <= N:
        fib.append(fib[-1] + fib[-2])
    m = len(fib) - 2  # max index k with weight F_{k+1} <= N
    return zeckendorf_digits(N, m)


def is_normal_form(a: List[int]) -> bool:
    for i, ai in enumerate(a):
        if ai not in (0, 1):
            return False
        if i + 1 < len(a) and ai == 1 and a[i + 1] == 1:
            return False
    return True


def apply_one_step(a: List[int]) -> Tuple[str | None, List[int]]:
    n = len(a)
    # (R_adj) adjacent merge
    for k in range(1, n):
        if a[k - 1] >= 1 and a[k] >= 1:
            a[k - 1] -= 1
            a[k] -= 1
            _ensure_len(a, k + 1)
            a[k + 1] += 1
            return "R_adj", a
    # (R_1)
    if n >= 1 and a[0] >= 2:
        a[0] -= 2
        _ensure_len(a, 1)
        a[1] += 1
        return "R_1", a
    # (R_2)
    if n >= 2 and a[1] >= 2:
        a[1] -= 2
        a[0] += 1
        _ensure_len(a, 2)
        a[2] += 1
        return "R_2", a
    # (R_k), k >= 3
    for k in range(3, n + 1):
        if a[k - 1] >= 2:
            a[k - 1] -= 2
            a[k - 3] += 1
            _ensure_len(a, k)
            a[k] += 1
            return "R_k", a
    return None, a


def normalize_config(a: List[int], max_steps: int) -> Tuple[List[int], int, Dict[str, int]]:
    steps = 0
    rule_counts: Dict[str, int] = {"R_adj": 0, "R_1": 0, "R_2": 0, "R_k": 0}
    a = list(a)
    while True:
        rule, a = apply_one_step(a)
        if rule is None:
            break
        rule_counts[rule] += 1
        steps += 1
        if steps > max_steps:
            raise RuntimeError("Exceeded max_steps; rewrite did not terminate in time.")
    return a, steps, rule_counts


def percentile(values: List[int], p: float) -> float:
    if not values:
        return 0.0
    data = sorted(values)
    idx = int(round(p * (len(data) - 1)))
    return float(data[idx])


@dataclass
class Case:
    config: List[int]
    norm: List[int]
    val: int
    steps: int


def run_experiment(
    m: int,
    samples: int,
    max_count: int,
    seed: int,
    max_steps: int,
    output: Path,
) -> None:
    rng = random.Random(seed)
    progress = Progress("fold_rewrite")

    total_steps = 0
    steps_list: List[int] = []
    rule_totals: Dict[str, int] = {"R_adj": 0, "R_1": 0, "R_2": 0, "R_k": 0}
    step_hist: Dict[str, int] = {}
    mismatches: List[Case] = []
    max_case: Case | None = None

    for i in range(samples):
        config = [rng.randint(0, max_count) for _ in range(m)]
        val = config_val(config)
        norm, steps, rule_counts = normalize_config(config, max_steps)
        norm_trim = _trim(norm)
        canonical = _trim(canonical_digits_from_val(val))
        if norm_trim != canonical:
            mismatches.append(Case(config, norm_trim, val, steps))
            if len(mismatches) >= 5:
                break
        if max_case is None or steps > max_case.steps:
            max_case = Case(config, norm_trim, val, steps)
        total_steps += steps
        steps_list.append(steps)
        step_hist[str(steps)] = step_hist.get(str(steps), 0) + 1
        for k, v in rule_counts.items():
            rule_totals[k] += v
        progress.tick(f"sample={i+1}/{samples} steps={steps} val={val}")

    if mismatches:
        raise RuntimeError("Normalization mismatch detected; see collected cases.")

    mean_steps = total_steps / samples if samples else 0.0
    summary = {
        "samples": samples,
        "m": m,
        "max_count": max_count,
        "seed": seed,
        "max_steps": max_steps,
        "mean_steps": mean_steps,
        "median_steps": percentile(steps_list, 0.5),
        "p90_steps": percentile(steps_list, 0.9),
        "p99_steps": percentile(steps_list, 0.99),
        "rule_counts": rule_totals,
    }
    max_case_dict = None
    if max_case is not None:
        max_case_dict = {
            "config": max_case.config,
            "val": max_case.val,
            "norm": max_case.norm,
            "steps": max_case.steps,
        }

    output.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "params": {
            "m": m,
            "samples": samples,
            "max_count": max_count,
            "seed": seed,
            "max_steps": max_steps,
        },
        "summary": summary,
        "max_case": max_case_dict,
        "step_histogram": step_hist,
    }
    output.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[fold_rewrite] wrote {output}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate directed rewrite normalization for Fold_infty.",
    )
    parser.add_argument("--m", type=int, default=30, help="Max index for config length.")
    parser.add_argument("--samples", type=int, default=2000, help="Number of random samples.")
    parser.add_argument("--max-count", type=int, default=3, help="Max count per slot.")
    parser.add_argument("--seed", type=int, default=20260201, help="RNG seed.")
    parser.add_argument("--max-steps", type=int, default=200000, help="Safety cap on steps.")
    parser.add_argument(
        "--output",
        type=Path,
        default=export_dir() / "fold_infty_rewrite_stats.json",
        help="Output JSON path.",
    )
    args = parser.parse_args()

    run_experiment(
        m=args.m,
        samples=args.samples,
        max_count=args.max_count,
        seed=args.seed,
        max_steps=args.max_steps,
        output=args.output,
    )


if __name__ == "__main__":
    main()
