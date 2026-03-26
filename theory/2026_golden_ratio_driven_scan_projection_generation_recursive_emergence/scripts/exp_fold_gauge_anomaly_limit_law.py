#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: limiting constant law for the fold-aware restriction gauge anomaly.

This script is English-only by repository convention.

We study, under the uniform micro baseline:
  omega ~ Unif(Omega_{m+1}) = {0,1}^{m+1},

the gauge anomaly
  G_m(omega) = | r_{m+1->m}(omega) xor r~_{m+1->m}(omega) |_0,

where r is naive truncation (drop last bit) and r~ is the fold-aware restriction
prefix of Fold_{m+1}.

Goal:
- Empirically audit the limiting mismatch density and the bulk joint law of
  (X, Y) where X is the naive bit and Y is the fold-aware output bit.

The manuscript states the conjectured exact rationals in Theorem
`thm:fold-gauge-anomaly-density`:

  P(X,Y) =
      Y=0     Y=1
  X=0 7/18    1/9
  X=1 1/3     1/6

so P(X xor Y = 1) = 4/9, and P(Y=1) = 5/18.

Outputs:
- artifacts/export/fold_gauge_anomaly_limit_law.json
"""

from __future__ import annotations

import argparse
import json
import random
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

from common_paths import export_dir
from common_phi_fold import Progress, fold_m


def _frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def _as_float_dict(d: Dict[Tuple[int, ...], Fraction]) -> Dict[str, float]:
    return {",".join(map(str, k)): float(v) for k, v in d.items()}


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit the limiting gauge-anomaly density and bulk joint laws.")
    ap.add_argument("--m", type=int, default=600, help="Resolution parameter m (uses words of length m+1).")
    ap.add_argument("--samples", type=int, default=20000, help="Number of IID samples.")
    ap.add_argument("--seed", type=int, default=2, help="RNG seed.")
    ap.add_argument(
        "--bulk-lo",
        type=int,
        default=-1,
        help="Bulk start index (0-based, inclusive). Default: m//3.",
    )
    ap.add_argument(
        "--bulk-hi",
        type=int,
        default=-1,
        help="Bulk end index (0-based, exclusive). Default: 2m//3.",
    )
    ap.add_argument(
        "--output",
        type=Path,
        default=export_dir() / "fold_gauge_anomaly_limit_law.json",
        help="Output JSON path.",
    )
    args = ap.parse_args()

    m = int(args.m)
    if m < 5:
        raise SystemExit("Require m>=5 for a meaningful bulk window.")
    L = m + 1
    n = int(args.samples)
    if n <= 0:
        raise SystemExit("Require samples > 0")

    bulk_lo = (m // 3) if int(args.bulk_lo) < 0 else int(args.bulk_lo)
    bulk_hi = ((2 * m) // 3) if int(args.bulk_hi) < 0 else int(args.bulk_hi)
    bulk_lo = max(0, bulk_lo)
    bulk_hi = min(m - 1, bulk_hi)  # must have i+1 < m
    if not (0 <= bulk_lo < bulk_hi <= m - 1):
        raise SystemExit(f"Invalid bulk window [{bulk_lo}, {bulk_hi}) for m={m}.")

    rng = random.Random(int(args.seed))
    prog = Progress("fold_gauge_anomaly_limit", every_seconds=20.0)
    t0 = time.time()

    total_g = 0
    counts_xy: Counter[Tuple[int, int]] = Counter()
    counts_yy: Counter[Tuple[int, int]] = Counter()

    for s in range(n):
        bits = [rng.getrandbits(1) for _ in range(L)]
        folded = fold_m(bits)  # length L
        prefix = bits[:-1]  # length m
        rem = folded[:-1]  # length m

        g = 0
        for a, b in zip(prefix, rem):
            g += a ^ b
        total_g += g

        for i in range(bulk_lo, bulk_hi):
            x = int(prefix[i])
            y = int(rem[i])
            counts_xy[(x, y)] += 1
            counts_yy[(y, int(rem[i + 1]))] += 1

        prog.tick(f"sample={s+1}/{n} m={m}")

    mean_g = total_g / float(n)
    mean_g_over_m = mean_g / float(m)

    xy_total = sum(counts_xy.values())
    yy_total = sum(counts_yy.values())
    if xy_total <= 0 or yy_total <= 0:
        raise RuntimeError("Empty counts (unexpected).")

    P_xy = {(x, y): Fraction(counts_xy[(x, y)], xy_total) for x in (0, 1) for y in (0, 1)}
    P_yy = {(a, b): Fraction(counts_yy[(a, b)], yy_total) for a in (0, 1) for b in (0, 1)}

    mismatch_bulk = P_xy[(0, 1)] + P_xy[(1, 0)]
    pY1_bulk = P_xy[(0, 1)] + P_xy[(1, 1)]

    # Conjectured exact rationals (manuscript).
    target_xy = {
        (0, 0): Fraction(7, 18),
        (0, 1): Fraction(1, 9),
        (1, 0): Fraction(1, 3),
        (1, 1): Fraction(1, 6),
    }
    target_mismatch = Fraction(4, 9)
    target_pY1 = Fraction(5, 18)
    target_yy = {
        (0, 0): Fraction(4, 9),
        (0, 1): Fraction(5, 18),
        (1, 0): Fraction(5, 18),
        (1, 1): Fraction(0, 1),
    }

    # Report
    def abs_diff(a: Fraction, b: Fraction) -> float:
        return abs(float(a - b))

    xy_abs_err = {f"{k[0]},{k[1]}": abs_diff(P_xy[k], target_xy[k]) for k in target_xy}
    yy_abs_err = {f"{k[0]}{k[1]}": abs_diff(P_yy[k], target_yy[k]) for k in target_yy}

    payload: Dict[str, object] = {
        "params": {
            "m": m,
            "samples": n,
            "seed": int(args.seed),
            "bulk_lo": bulk_lo,
            "bulk_hi": bulk_hi,
        },
        "mean_Gm": float(mean_g),
        "mean_Gm_over_m": float(mean_g_over_m),
        "bulk_P_XY": {f"{x},{y}": _frac_str(P_xy[(x, y)]) for x in (0, 1) for y in (0, 1)},
        "bulk_P_YY": {f"{a}{b}": _frac_str(P_yy[(a, b)]) for a in (0, 1) for b in (0, 1)},
        "bulk_mismatch_P_X_xor_Y_1": _frac_str(mismatch_bulk),
        "bulk_P_Y_1": _frac_str(pY1_bulk),
        "targets": {
            "P_XY": {f"{x},{y}": _frac_str(target_xy[(x, y)]) for x in (0, 1) for y in (0, 1)},
            "P_YY": {f"{a}{b}": _frac_str(target_yy[(a, b)]) for a in (0, 1) for b in (0, 1)},
            "mismatch": _frac_str(target_mismatch),
            "P_Y_1": _frac_str(target_pY1),
        },
        "abs_err_vs_targets": {
            "P_XY": xy_abs_err,
            "P_YY": yy_abs_err,
            "mismatch": abs_diff(mismatch_bulk, target_mismatch),
            "P_Y_1": abs_diff(pY1_bulk, target_pY1),
        },
    }

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Console summary
    print(f"[fold_gauge_anomaly_limit] m={m} n={n} mean(Gm)/m={mean_g_over_m:.6f}", flush=True)
    print("[fold_gauge_anomaly_limit] bulk P(X,Y):", {k: float(P_xy[k]) for k in sorted(P_xy)}, flush=True)
    print("[fold_gauge_anomaly_limit] bulk mismatch:", float(mismatch_bulk), "target", float(target_mismatch), flush=True)
    print("[fold_gauge_anomaly_limit] bulk P(Y=1):", float(pY1_bulk), "target", float(target_pY1), flush=True)
    print(f"[fold_gauge_anomaly_limit] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

