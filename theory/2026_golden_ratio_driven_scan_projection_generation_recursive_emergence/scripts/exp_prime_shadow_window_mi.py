#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Mutual information between primality and Zeckendorf windows.

Outputs:
- artifacts/export/prime_shadow_window_mi.json
- sections/generated/tab_prime_shadow_window_mi.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, zeckendorf_digits


@dataclass(frozen=True)
class Result:
    m: int
    categories: int
    prime_count: int
    total: int
    mutual_info_bits: float


def prime_sieve(n: int) -> List[bool]:
    if n < 2:
        return [False] * (n + 1)
    is_prime = [True] * (n + 1)
    is_prime[0] = False
    is_prime[1] = False
    p = 2
    while p * p <= n:
        if is_prime[p]:
            for k in range(p * p, n + 1, p):
                is_prime[k] = False
        p += 1
    return is_prime


def zeckendorf_full_digits(n: int) -> List[int]:
    if n <= 0:
        return []
    fib = [1, 1]
    while fib[-1] <= n:
        fib.append(fib[-1] + fib[-2])
    m_full = len(fib) - 2
    return zeckendorf_digits(n, m_full)


def window_key(digits: List[int], m: int) -> str:
    if len(digits) < m:
        digits = digits + [0] * (m - len(digits))
    window = digits[:m]
    return "".join("1" if b else "0" for b in window)


def mutual_info(n_max: int, m: int, is_prime: List[bool], digits_cache: Dict[int, List[int]]) -> Result:
    joint: Dict[tuple[int, str], int] = {}
    count_p = {0: 0, 1: 0}
    count_w: Dict[str, int] = {}

    for n in range(2, n_max + 1):
        p = 1 if is_prime[n] else 0
        w = window_key(digits_cache[n], m)
        joint[(p, w)] = joint.get((p, w), 0) + 1
        count_p[p] += 1
        count_w[w] = count_w.get(w, 0) + 1

    total = n_max - 1
    mi = 0.0
    for (p, w), c in joint.items():
        if c == 0:
            continue
        pw = c / total
        pp = count_p[p] / total
        pwm = count_w[w] / total
        mi += pw * math.log(pw / (pp * pwm), 2)
    return Result(
        m=m,
        categories=len(count_w),
        prime_count=count_p[1],
        total=total,
        mutual_info_bits=mi,
    )


def write_table(results: List[Result], n_max: int, out_path: Path) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{素数性与 Zeckendorf 低位窗口的互信息（$n=2,\\dots,%d$；$W_m$ 为最低 $m$ 位）。}"
        % n_max
    )
    lines.append("\\label{tab:prime_shadow_window_mi}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $|X_m|$ & $I(\\mathbf{1}_{\\mathrm{prime}};W_m)$ (bits)\\\\")
    lines.append("\\midrule")
    for r in results:
        lines.append(f"{r.m} & {r.categories} & {r.mutual_info_bits:.6f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-max", type=int, default=1000)
    parser.add_argument("--m-list", type=str, default="6,10,12")
    parser.add_argument(
        "--output",
        type=str,
        default="artifacts/export/prime_shadow_window_mi.json",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    n_max = max(2, args.n_max)
    m_list = [int(x.strip()) for x in args.m_list.split(",") if x.strip()]
    m_list = sorted({m for m in m_list if m > 0})
    if not m_list:
        raise ValueError("m_list must contain positive integers")

    is_prime = prime_sieve(n_max)
    digits_cache: Dict[int, List[int]] = {}
    progress = Progress("prime_shadow_mi")
    for n in range(2, n_max + 1):
        digits_cache[n] = zeckendorf_full_digits(n)
        progress.tick(f"precompute n={n}/{n_max}")

    results: List[Result] = []
    for m in m_list:
        results.append(mutual_info(n_max, m, is_prime, digits_cache))

    payload = {
        "params": {"n_max": n_max, "m_list": m_list, "window": "lowest_m_digits"},
        "results": [
            {
                "m": r.m,
                "categories": r.categories,
                "prime_count": r.prime_count,
                "total": r.total,
                "mutual_info_bits": r.mutual_info_bits,
            }
            for r in results
        ],
    }
    out_path = Path(args.output)
    if not out_path.is_absolute():
        out_path = Path.cwd() / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    table_path = generated_dir() / "tab_prime_shadow_window_mi.tex"
    write_table(results, n_max, table_path)


if __name__ == "__main__":
    main()
