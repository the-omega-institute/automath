#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Binary-interval → Zeckendorf-prefix folding saturation experiment.

All code is English-only by repository convention.

We study the map:
  Fold_bin_m : {0,1,...,2^m-1} → X_m
  n ↦ first m Zeckendorf digits of n (weights F_{k+1}, no adjacent 1s)

This script:
- verifies the sharp saturation criterion for the maximal fiber (w=0^m),
- computes exact fiber sizes by an O(m) Fibonacci-digit DP,
- outputs a small LaTeX table for m≤m_max with all saturation points.

Artifacts:
- artifacts/export/fold_binary_saturation.json
- sections/generated/tab_fold_binary_saturation_points.tex
"""

from __future__ import annotations

import bisect
import json
import time
from dataclasses import dataclass
from functools import lru_cache
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fib_upto, zeckendorf_digits


def fib_precompute_up_to_limit(limit: int) -> List[int]:
    """Return Fibonacci numbers F_1..F_J (F_1=F_2=1) with F_J > limit."""
    fib: List[int] = [1, 1]
    while fib[-1] <= limit:
        fib.append(fib[-1] + fib[-2])
    return fib


def F(fib: Sequence[int], n: int) -> int:
    """F_n with F_1=F_2=1, given fib list storing F_1..F_J."""
    if n <= 0:
        return 0
    return fib[n - 1]


def K_of_m(fib: Sequence[int], m: int) -> int:
    """Unique K with F_{K+1} <= 2^m-1 < F_{K+2}."""
    target = (1 << m) - 1
    j = bisect.bisect_right(fib, target) + 1  # smallest index j with F_j > target
    # Now F_{j-1} <= target < F_j, hence K+2=j.
    return j - 2


def V_m_of_w(fib: Sequence[int], w: Sequence[int]) -> int:
    """Zeckendorf value V_m(w) = sum_{k=1}^m w_k F_{k+1}."""
    s = 0
    for k, bit in enumerate(w, start=1):
        if bit:
            s += F(fib, k + 1)
    return s


def count_tail_leq(
    fib: Sequence[int], *, limit: int, m: int, K: int, w_m: int
) -> int:
    """Count tails (c_{m+1}..c_K) with:
    - c_k in {0,1}
    - no adjacency: c_k c_{k+1} = 0
    - boundary: w_m c_{m+1} = 0
    - value constraint: sum_{k=m+1}^K c_k F_{k+1} <= limit

    Uses O(K-m) digit DP against Zeckendorf digits of 'limit'.
    """
    if limit < 0:
        return 0
    if K <= m:
        return 1  # empty tail

    # Zeckendorf digits b_1..b_K for limit, weights F_{k+1}.
    b = zeckendorf_digits(limit, K)

    @lru_cache(None)
    def dp(pos: int, prev1: int, tight: int) -> int:
        if pos == 0:
            return 1

        bpos = b[pos - 1]

        # Forced zeros below/at m and boundary at m+1.
        if pos <= m or (pos == m + 1 and w_m == 1):
            digit = 0
            next_tight = tight and (digit == bpos)
            return dp(pos - 1, digit, 1 if next_tight else 0)

        total = 0
        for digit in (0, 1):
            if digit == 1 and prev1 == 1:
                continue
            if tight and digit > bpos:
                continue
            next_tight = tight and (digit == bpos)
            total += dp(pos - 1, digit, 1 if next_tight else 0)
        return total

    return dp(K, 0, 1)


def S_max_tail_sum(fib: Sequence[int], *, m: int, K: int) -> int:
    """Maximum admissible tail sum over weights F_{m+2}..F_{K+1} with no adjacency."""
    L = K - m
    if L <= 0:
        return 0
    # Closed form:
    # - if L odd:   S_max = F_{K+2} - F_{m+1}
    # - if L even:  S_max = F_{K+2} - F_{m+2}
    if L % 2 == 1:
        return F(fib, K + 2) - F(fib, m + 1)
    return F(fib, K + 2) - F(fib, m + 2)


@dataclass(frozen=True)
class SatRow:
    m: int
    K: int
    L: int
    upper: int
    d_max: int
    S_max: int
    target: int
    slack: int


def write_table(rows: List[SatRow], m_max: int, saturated_ms: List[int]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{二进制区间折叠 $\\mathrm{Fold}^{\\mathrm{bin}}_m$ 的“上界饱和点”（扫描 $m\\le %d$）。表中给出 $K(m)$（满足 $F_{K(m)+1}\\le 2^m-1 < F_{K(m)+2}$）、尾长 $L=K-m$、组合上界 $F_{L+2}$、精确最大纤维 $d_{\\max}(m)=|\\mathrm{Fold}^{\\mathrm{bin}}_m{}^{-1}(0^m)|$（digit DP）、以及最大尾和 $S_{\\max}(m)$ 与阈值 $2^m-1$ 的裕量。}"
        % m_max
    )
    lines.append("\\label{tab:fold_binary_saturation_points}")
    lines.append("\\begin{tabular}{rrrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $K(m)$ & $L$ & $F_{L+2}$ & $d_{\\max}(m)$ & $S_{\\max}(m)$ & $2^m-1$ & $(2^m-1)-S_{\\max}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.K} & {r.L} & {r.upper} & {r.d_max} & {r.S_max} & {r.target} & {r.slack}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\vspace{4pt}")
    lines.append(
        "\\\\饱和点集合（$m\\le %d$）：$\\{ %s \\}$."
        % (m_max, ",\\,".join(str(x) for x in saturated_ms))
    )
    lines.append("\\end{table}")

    out = generated_dir() / "tab_fold_binary_saturation_points.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_bin_sat")

    m_max = 400
    max_target = (1 << m_max) - 1
    fib = fib_precompute_up_to_limit(max_target)

    saturated_ms: List[int] = []
    sat_rows: List[SatRow] = []

    for m in range(1, m_max + 1):
        prog.tick(f"scan m={m}/{m_max}")
        target = (1 << m) - 1
        K = K_of_m(fib, m)
        L = K - m
        upper = F(fib, L + 2) if L >= 0 else 1

        S_max = S_max_tail_sum(fib, m=m, K=K)
        crit = target >= S_max

        # Exact via DP for w=0^m (so V=0, boundary w_m=0).
        d_max = count_tail_leq(fib, limit=target, m=m, K=K, w_m=0)

        if crit != (d_max == upper):
            raise RuntimeError(
                f"criterion mismatch at m={m}: crit={crit} d_max={d_max} upper={upper}"
            )

        if d_max == upper:
            saturated_ms.append(m)
            sat_rows.append(
                SatRow(
                    m=m,
                    K=K,
                    L=L,
                    upper=upper,
                    d_max=d_max,
                    S_max=S_max,
                    target=target,
                    slack=target - S_max,
                )
            )

    export_dir().mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "m_max": m_max,
        "saturated_ms": saturated_ms,
        "sat_rows": [r.__dict__ for r in sat_rows],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_binary_saturation.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    write_table(sat_rows, m_max=m_max, saturated_ms=saturated_ms)
    print(
        f"[fold_bin_sat] OK saturated={len(saturated_ms)} wall={time.time() - t0:.2f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()

