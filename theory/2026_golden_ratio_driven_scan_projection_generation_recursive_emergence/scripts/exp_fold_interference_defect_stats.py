#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Defect-set statistics for the interference-graph independent-set lower bound.

This script operationalizes the paper's structure:
  d_m(x) >= #Ind(G(x)) = product_over_blocks I(J_block),
and, within each block, a two-letter DP step (sigma in {2,3}) where sigma=3 is a
local "defect" (dense triple) step.

We sample stable words x from either:
  - source=micro_uniform: uniform microstates omega in {0,1}^m, pushed forward by Fold_m
    (equivalently, sampling from the output distribution pi_m(x)=d_m(x)/2^m),
  - source=parry: the maximal-entropy Parry baseline on the golden-mean shift.

For each m we report:
  - mean (1/m) * ln #Ind(G(x_{1..m}))  (a numerical estimator for Lambda_Ind),
  - J-density |J(x)|/m,
  - defect-step rate (fraction of sigma_t=3 among local steps),
  - histograms for block sizes and defect-gap statistics (t-space).

Outputs:
  - artifacts/export/fold_interference_defect_stats.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import DefaultDict, Dict, List, Literal, Tuple

import numpy as np

from common_interference_graph import defect_gap_list, j_positions_100, log_independent_sets_via_blocks
from common_paths import export_dir

Source = Literal["micro_uniform", "parry"]


def fib_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F[: n + 1]


def zeckendorf_digits_fixed(N: int, length: int, F: List[int]) -> List[int]:
    """Greedy Zeckendorf digits of length `length` for weights F_{k+1}, k=1..length."""
    if N < 0:
        raise ValueError("N must be >= 0")
    if length < 0:
        raise ValueError("length must be >= 0")
    if length == 0:
        return []
    # Need weights up to F_{length+1}.
    if len(F) <= length + 1:
        raise ValueError("F list too short for requested length")
    rem = int(N)
    out = [0] * length
    prev_one = False
    for k in range(length, 0, -1):
        w = int(F[k + 1])  # F_{k+1}
        if (not prev_one) and rem >= w:
            out[k - 1] = 1
            rem -= w
            prev_one = True
        else:
            out[k - 1] = 0
            prev_one = False
    if rem != 0:
        raise RuntimeError("Zeckendorf greedy failed to exhaust remainder")
    return out


def fold_micro_bits_to_stable_word(micro_bits: np.ndarray, F: List[int]) -> str:
    """Fold micro bits (0/1 array) to a stable word in X_m."""
    if micro_bits.ndim != 1:
        raise ValueError("micro_bits must be a 1D array")
    m = int(micro_bits.shape[0])
    # Compute N = sum_{k=1}^m omega_k F_{k+1}.
    N = 0
    # micro_bits is 0-indexed, corresponding to positions k=1..m.
    # Weight at position k is F_{k+1}, i.e. F[k+1] with 0-indexed F_0.. list.
    for idx in range(m):
        if int(micro_bits[idx]) & 1:
            N += int(F[idx + 2])
    # One extra digit captures the overflow bit at weight F_{m+2}.
    digits = zeckendorf_digits_fixed(N, length=m + 1, F=F)
    stable = digits[:m]
    return "".join("1" if x else "0" for x in stable)


def sample_parry_word(m: int, rng: np.random.Generator) -> str:
    """Sample a golden-mean legal word from the Parry (max entropy) measure."""
    phi = (1.0 + 5.0**0.5) / 2.0
    pi1 = 1.0 / (phi * phi + 1.0)
    pi0 = 1.0 - pi1
    p00 = 1.0 / phi
    p01 = 1.0 / (phi * phi)
    # Start in stationarity.
    x0 = 1 if rng.random() < pi1 else 0
    out = [x0]
    prev = x0
    for _ in range(1, m):
        if prev == 1:
            nxt = 0
        else:
            nxt = 0 if (rng.random() < p00) else 1
        out.append(nxt)
        prev = nxt
    return "".join("1" if b else "0" for b in out)


@dataclass(frozen=True)
class MRow:
    m: int
    n_samples: int
    source: str
    mean_log_ind_per_m: float
    mean_J_density: float
    mean_blocks_per_m: float
    defect_step_rate: float
    block_size_hist: Dict[int, int]
    defect_gap_hist: Dict[int, int]
    defect_count_per_block_hist: Dict[int, int]


def _hist_add(hist: DefaultDict[int, int], key: int, inc: int = 1) -> None:
    hist[int(key)] += int(inc)


def run_for_m(m: int, n_samples: int, source: Source, seed: int) -> MRow:
    rng = np.random.default_rng(int(seed) + 1000003 * int(m))

    # Precompute Fibonacci numbers for the fold (micro_uniform only).
    F: List[int] = []
    if source == "micro_uniform":
        # Need F_{m+2} for weight at position (m+1).
        F = fib_upto(m + 2)

    sum_log_ind = 0.0
    sum_J = 0
    sum_blocks = 0
    sigma2 = 0
    sigma3 = 0

    block_size_hist: DefaultDict[int, int] = defaultdict(int)
    defect_gap_hist: DefaultDict[int, int] = defaultdict(int)
    defect_count_per_block_hist: DefaultDict[int, int] = defaultdict(int)

    for _ in range(int(n_samples)):
        if source == "micro_uniform":
            micro = rng.integers(0, 2, size=m, dtype=np.uint8)
            word = fold_micro_bits_to_stable_word(micro, F=F)
        elif source == "parry":
            word = sample_parry_word(m, rng=rng)
        else:
            raise ValueError(f"unknown source: {source}")

        # ln #Ind(G(word)) and per-block stats.
        log_ind, stats = log_independent_sets_via_blocks(word)
        sum_log_ind += float(log_ind)

        # J(x) density (compute once; stats contain blocks, but J is cheap).
        J = j_positions_100(word)
        sum_J += int(len(J))

        # Block-level aggregates.
        sum_blocks += int(len(stats))
        for st in stats:
            k = int(len(st.vertices))
            _hist_add(block_size_hist, k)
            _hist_add(defect_count_per_block_hist, int(len(st.defect_steps)))
            for g in defect_gap_list(st.defect_steps):
                _hist_add(defect_gap_hist, g)
            for s in st.sigmas:
                if int(s) == 2:
                    sigma2 += 1
                elif int(s) == 3:
                    sigma3 += 1
                else:
                    raise RuntimeError("unexpected sigma value")

    mean_log_ind_per_m = (sum_log_ind / float(n_samples)) / float(m) if n_samples > 0 else float("nan")
    mean_J_density = (float(sum_J) / float(n_samples)) / float(m) if n_samples > 0 else float("nan")
    mean_blocks_per_m = (float(sum_blocks) / float(n_samples)) / float(m) if n_samples > 0 else float("nan")
    denom = float(sigma2 + sigma3)
    defect_step_rate = float(sigma3) / denom if denom > 0 else 0.0

    # Convert histograms to plain dicts for JSON.
    return MRow(
        m=int(m),
        n_samples=int(n_samples),
        source=str(source),
        mean_log_ind_per_m=float(mean_log_ind_per_m),
        mean_J_density=float(mean_J_density),
        mean_blocks_per_m=float(mean_blocks_per_m),
        defect_step_rate=float(defect_step_rate),
        block_size_hist={int(k): int(v) for k, v in sorted(block_size_hist.items())},
        defect_gap_hist={int(k): int(v) for k, v in sorted(defect_gap_hist.items())},
        defect_count_per_block_hist={int(k): int(v) for k, v in sorted(defect_count_per_block_hist.items())},
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Interference-graph defect statistics for the Fold_m independent-set lower bound.")
    parser.add_argument("--m-min", type=int, default=32)
    parser.add_argument("--m-max", type=int, default=128)
    parser.add_argument("--samples-per-m", type=int, default=2000)
    parser.add_argument("--source", type=str, default="micro_uniform", choices=["micro_uniform", "parry"])
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_interference_defect_stats.json"),
    )
    args = parser.parse_args()

    if args.m_min < 3 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 3")
    if args.samples_per_m < 1:
        raise SystemExit("Require --samples-per-m >= 1")

    rows: List[MRow] = []
    for m in range(int(args.m_min), int(args.m_max) + 1):
        row = run_for_m(
            m=int(m),
            n_samples=int(args.samples_per_m),
            source=args.source,  # type: ignore[arg-type]
            seed=int(args.seed),
        )
        rows.append(row)
        print(
            f"[fold-interference-defects] m={row.m} source={row.source} "
            f"mean_logInd_per_m={row.mean_log_ind_per_m:.6f} "
            f"Jdens={row.mean_J_density:.6f} defect_rate={row.defect_step_rate:.6f}",
            flush=True,
        )

    payload = {
        "m_min": int(args.m_min),
        "m_max": int(args.m_max),
        "samples_per_m": int(args.samples_per_m),
        "source": str(args.source),
        "seed": int(args.seed),
        "rows": [asdict(r) for r in rows],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-interference-defects] wrote {jout}", flush=True)


if __name__ == "__main__":
    main()

