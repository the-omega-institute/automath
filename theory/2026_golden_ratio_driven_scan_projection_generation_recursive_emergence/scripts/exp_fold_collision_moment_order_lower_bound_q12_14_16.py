#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit-style lower bound: order <= 12 candidates collapse at m=25
for k in {12,14,16}.

We compute exact collision moments:
  S_k(m) = sum_r c_m(r)^k,  with residue counts c_m(r) modulo F_{m+2},
using the modular Fibonacci DP (counts_mod_fib).

Then for each k and each order d<=12 we consider *homogeneous* integer recurrences
of order d on the finite window:

  c_0 S(m) - c_1 S(m-1) - ... - c_d S(m-d) = 0,

with integer coefficients (c_0,...,c_d) not all zero, required to hold for all
m in [d+1 .. m_fit] (default m_fit=24). This is a homogeneous linear system in
d+1 unknowns; any rational solution can be scaled to integers.

We then add the single extra constraint at m=m_break (default 25) and test
whether the solution space collapses to {0}. If so, any order<=12 candidate that
is consistent up to m<=24 must necessarily break at m=25.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_mod_fib_dp import counts_mod_fib, hist_from_counts
from common_paths import export_dir
from common_phi_fold import Progress


def moments_for_k_list(vals, freq, k_list: Sequence[int]) -> Dict[int, int]:
    """Compute S_k = sum_r c[r]^k for k in k_list as Python ints."""
    vals_py = [int(v) for v in vals.tolist()]
    freq_py = [int(f) for f in freq.tolist()]
    out: Dict[int, int] = {}
    for k in k_list:
        s = 0
        for v, f in zip(vals_py, freq_py, strict=True):
            s += f * (v**k)
        out[int(k)] = int(s)
    return out


def build_homogeneous_system(seq_by_m: Dict[int, int], order: int, m_end: int) -> sp.Matrix:
    """
    Build the homogeneous linear system for coefficients (c0,c1,...,cd):
      c0*S(m) - sum_{i=1..d} c_i*S(m-i) = 0
    for all m in [d+1 .. m_end].
    """
    d = int(order)
    rows: List[List[int]] = []
    for m in range(d + 1, int(m_end) + 1):
        if m - d < 1:
            continue
        row = [seq_by_m[m]] + [-seq_by_m[m - i] for i in range(1, d + 1)]
        rows.append(row)
    if not rows:
        return sp.Matrix([])
    return sp.Matrix(rows)


@dataclass(frozen=True)
class OrderAudit:
    order: int
    dim_fit: int
    dim_break: int
    forced_break: bool


@dataclass(frozen=True)
class Result:
    k: int
    m_fit: int
    m_break: int
    order_max: int
    audits: List[OrderAudit]
    all_orders_leq_force_break_at_m_break: bool


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit lower bound for integer recurrences (k=12,14,16).")
    ap.add_argument("--k-list", type=str, default="12,14,16", help="Comma-separated k values.")
    ap.add_argument("--m-fit", type=int, default=24, help="Fit/consistency window upper bound (default: 24).")
    ap.add_argument("--m-break", type=int, default=25, help="First forced break check index (default: 25).")
    ap.add_argument("--order-max", type=int, default=12, help="Max order to search (default: 12).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_order_lower_bound_q12_14_16.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    ks = [int(s.strip()) for s in str(args.k_list).split(",") if s.strip()]
    if not ks:
        raise SystemExit("Empty --k-list")
    if any(k < 2 for k in ks):
        raise SystemExit("All k must be >= 2")

    m_fit = int(args.m_fit)
    m_break = int(args.m_break)
    if m_break <= m_fit:
        raise SystemExit("Require m_break > m_fit")
    order_max = int(args.order_max)
    if order_max < 1:
        raise SystemExit("--order-max must be >= 1")

    prog = Progress("order-lb", every_seconds=20.0)

    # Compute exact S_k(m) for m=1..m_break.
    S: Dict[int, Dict[int, int]] = {k: {} for k in ks}
    for m in range(1, m_break + 1):
        c = counts_mod_fib(m, prog=prog)
        vals, freq = hist_from_counts(c)
        moms = moments_for_k_list(vals, freq, ks)
        for k in ks:
            S[k][m] = moms[k]
        print(f"[order-lb] m={m} mod={len(c)} computed k={ks}", flush=True)

    results: List[Result] = []
    for k in ks:
        seq = S[k]
        audits: List[OrderAudit] = []
        for d in range(1, order_max + 1):
            A_fit = build_homogeneous_system(seq, order=d, m_end=m_fit)
            A_break = build_homogeneous_system(seq, order=d, m_end=m_break)
            dim_fit = len(A_fit.nullspace()) if A_fit.rows > 0 else (d + 1)
            dim_break = len(A_break.nullspace()) if A_break.rows > 0 else (d + 1)
            forced = (dim_fit > 0) and (dim_break == 0)
            audits.append(OrderAudit(order=int(d), dim_fit=int(dim_fit), dim_break=int(dim_break), forced_break=bool(forced)))
            print(
                f"[order-lb] k={k} order={d} null_dim(m<= {m_fit})={dim_fit} null_dim(m<= {m_break})={dim_break}",
                flush=True,
            )

        all_force = all(a.dim_break == 0 for a in audits)
        results.append(
            Result(
                k=int(k),
                m_fit=int(m_fit),
                m_break=int(m_break),
                order_max=int(order_max),
                audits=audits,
                all_orders_leq_force_break_at_m_break=bool(all_force),
            )
        )

    payload = {
        "k_list": ks,
        "m_fit": m_fit,
        "m_break": m_break,
        "order_max": order_max,
        "results": [asdict(r) for r in results],
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[order-lb] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

