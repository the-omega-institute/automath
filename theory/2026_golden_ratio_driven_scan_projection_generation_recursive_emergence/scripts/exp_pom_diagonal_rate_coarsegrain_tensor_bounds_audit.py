#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit coarse-graining bounds and tensor upper bounds for the diagonal-coupling rate R_w(delta).

This script is English-only by repository convention.

We numerically verify:
  - Coarse-graining lower bound: R_w(delta) >= R_W(delta).
  - Coarse-graining constructive upper bound: R_w(delta) <= R_W(delta'),
      delta' = 1 - (1-delta)/c_pi, where c_pi = min_B sum_{x in B} w_B(x)^2.
  - Tensor upper bound for product distributions:
      R_{w1 ⊗ w2}(delta) <= inf_{delta1 ⊕ delta2 <= delta} [R_{w1}(delta1)+R_{w2}(delta2)].
    and the data-processing lower bound:
      R_{w1 ⊗ w2}(delta) >= max(R_{w1}(delta), R_{w2}(delta)).

Outputs:
  - artifacts/export/pom_diagonal_rate_coarsegrain_tensor_bounds_audit.json
  - sections/generated/eq_pom_diagonal_rate_coarsegrain_tensor_bounds_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp

from common_diagonal_rate import delta0_from_w, entropy, solve_scalar_collapse
from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _R_value(w: List[mp.mpf], delta: mp.mpf, *, dps: int) -> mp.mpf:
    """Numeric R_w(delta), handling endpoints delta=0 and delta>=delta0."""
    d0 = delta0_from_w(w)
    if delta >= d0:
        return mp.mpf(0)
    if delta <= 0:
        return entropy(w)
    return solve_scalar_collapse(w, delta, dps=dps).R


def _product_distribution(w1: List[mp.mpf], w2: List[mp.mpf]) -> List[mp.mpf]:
    return [a * b for a in w1 for b in w2]


def _partition_block_distribution(w: List[mp.mpf], blocks: List[List[int]]) -> Tuple[List[mp.mpf], mp.mpf]:
    """Return (W, c_pi) for a given partition blocks of indices."""
    W: List[mp.mpf] = []
    c_list: List[mp.mpf] = []
    for B in blocks:
        WB = mp.fsum([w[i] for i in B])
        W.append(WB)
        wB = [w[i] / WB for i in B]
        c_list.append(mp.fsum([p * p for p in wB]))
    return W, min(c_list)


@dataclass(frozen=True)
class CoarseRow:
    w: List[str]
    W: List[str]
    delta: str
    delta_prime: str
    c_pi: str
    R_w: str
    R_W_lower: str
    R_W_upper: str
    lower_ok: bool
    upper_ok: bool


@dataclass(frozen=True)
class TensorRow:
    w1: List[str]
    w2: List[str]
    delta: str
    R_prod: str
    upper_bound_grid_min: str
    upper_argmin_delta1: str
    upper_argmin_delta2max: str
    lower_bound: str
    upper_ok: bool
    lower_ok: bool


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit coarse-graining and tensor bounds for R_w(delta).")
    parser.add_argument("--dps", type=int, default=90, help="Decimal precision (default: 90).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable outputs.")
    mp.mp.dps = dps

    t0 = time.time()
    print("[pom-diagonal-rate-bounds] start", flush=True)

    # --- Coarse-graining example ---
    w = [mp.mpf("0.31"), mp.mpf("0.19"), mp.mpf("0.17"), mp.mpf("0.13"), mp.mpf("0.11"), mp.mpf("0.09")]
    # Partition: one nontrivial block + singletons.
    blocks = [[0, 5], [1], [2], [3], [4]]
    W, c_pi = _partition_block_distribution(w, blocks)

    delta = mp.mpf("0.40")  # chosen so that delta' is in [0,1]
    delta_prime = mp.mpf(1) - (mp.mpf(1) - delta) / c_pi
    if not (0 <= delta_prime <= 1):
        raise RuntimeError("delta' not in [0,1] for the chosen coarse-graining example.")

    Rw = _R_value(w, delta, dps=dps)
    RW_lower = _R_value(W, delta, dps=dps)
    RW_upper = _R_value(W, delta_prime, dps=dps)

    lower_ok = bool(Rw + mp.mpf("1e-25") >= RW_lower)
    upper_ok = bool(Rw <= RW_upper + mp.mpf("1e-25"))

    coarse_row = CoarseRow(
        w=[mp.nstr(p, 25) for p in w],
        W=[mp.nstr(p, 25) for p in W],
        delta=mp.nstr(delta, 25),
        delta_prime=mp.nstr(delta_prime, 25),
        c_pi=mp.nstr(c_pi, 25),
        R_w=mp.nstr(Rw, 25),
        R_W_lower=mp.nstr(RW_lower, 25),
        R_W_upper=mp.nstr(RW_upper, 25),
        lower_ok=bool(lower_ok),
        upper_ok=bool(upper_ok),
    )

    # --- Tensor bounds example ---
    w1 = [mp.mpf("0.50"), mp.mpf("0.30"), mp.mpf("0.20")]
    w2 = [mp.mpf("0.40"), mp.mpf("0.25"), mp.mpf("0.20"), mp.mpf("0.15")]
    w_prod = _product_distribution(w1, w2)

    delta_t = mp.mpf("0.15")
    R_prod = _R_value(w_prod, delta_t, dps=dps)

    # Grid-minimize upper bound: for each delta1 in [0,delta], take delta2=delta2_max(delta1).
    n_grid = 300
    best = mp.inf
    best_d1 = mp.mpf(0)
    best_d2 = mp.mpf(0)
    for i in range(n_grid + 1):
        d1 = delta_t * mp.mpf(i) / mp.mpf(n_grid)
        if d1 >= 1:
            continue
        d2_max = mp.mpf(1) - (mp.mpf(1) - delta_t) / (mp.mpf(1) - d1)
        if d2_max < 0:
            continue
        val = _R_value(w1, d1, dps=dps) + _R_value(w2, d2_max, dps=dps)
        if val < best:
            best = val
            best_d1 = d1
            best_d2 = d2_max

    upper_ok_t = bool(R_prod <= best + mp.mpf("1e-25"))

    lower_bd = max(_R_value(w1, delta_t, dps=dps), _R_value(w2, delta_t, dps=dps))
    lower_ok_t = bool(R_prod + mp.mpf("1e-25") >= lower_bd)

    tensor_row = TensorRow(
        w1=[mp.nstr(p, 25) for p in w1],
        w2=[mp.nstr(p, 25) for p in w2],
        delta=mp.nstr(delta_t, 25),
        R_prod=mp.nstr(R_prod, 25),
        upper_bound_grid_min=mp.nstr(best, 25),
        upper_argmin_delta1=mp.nstr(best_d1, 25),
        upper_argmin_delta2max=mp.nstr(best_d2, 25),
        lower_bound=mp.nstr(lower_bd, 25),
        upper_ok=bool(upper_ok_t),
        lower_ok=bool(lower_ok_t),
    )

    payload = {
        "coarse_graining": asdict(coarse_row),
        "tensor_bounds": asdict(tensor_row),
    }

    if not args.no_output:
        out_json = export_dir() / "pom_diagonal_rate_coarsegrain_tensor_bounds_audit.json"
        _write_json(out_json, payload)

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_pom_diagonal_rate_coarsegrain_tensor_bounds_audit.py",
                "\\[",
                f"\\text{{Coarse-graining example: }}\\delta={mp.nstr(delta,10)},\\ c_\\pi\\approx {mp.nstr(c_pi,10)},\\ \\delta'\\approx {mp.nstr(delta_prime,10)}.",
                "\\]",
                "\\[",
                f"R_w(\\delta)\\approx {mp.nstr(Rw,15)},\\quad R_W(\\delta)\\approx {mp.nstr(RW_lower,15)},\\quad R_W(\\delta')\\approx {mp.nstr(RW_upper,15)}.",
                "\\]",
                "\\[",
                f"\\text{{Tensor example: }}\\delta={mp.nstr(delta_t,10)},\\ R_{{w_1\\otimes w_2}}(\\delta)\\approx {mp.nstr(R_prod,15)},\\ "
                f"\\inf\\approx {mp.nstr(best,15)}.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_pom_diagonal_rate_coarsegrain_tensor_bounds_audit.tex"
        _write_text(out_tex, tex)

        print(f"[pom-diagonal-rate-bounds] wrote {out_json}", flush=True)
        print(f"[pom-diagonal-rate-bounds] wrote {out_tex}", flush=True)

    if not (lower_ok and upper_ok and upper_ok_t and lower_ok_t):
        raise RuntimeError("One or more bound checks failed.")

    dt = time.time() - t0
    print(
        "[pom-diagonal-rate-bounds] checks:"
        f" coarse=(lower={lower_ok},upper={upper_ok}) tensor=(lower={lower_ok_t},upper={upper_ok_t}) seconds={dt:.3f}",
        flush=True,
    )
    print("[pom-diagonal-rate-bounds] done", flush=True)


if __name__ == "__main__":
    main()

