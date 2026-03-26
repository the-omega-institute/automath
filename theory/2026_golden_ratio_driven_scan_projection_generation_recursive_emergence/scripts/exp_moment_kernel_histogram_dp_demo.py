#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Executable demo: build a k-collision moment-kernel A_k using histogram DP.

We demonstrate the "state histogram + coefficient extraction" construction on the
audited 10-state sync-kernel transducer (uniform-input fingerprint script).

This script is intentionally minimal:
  - It constructs A_k on the symmetric quotient state space H_k (multisets),
  - estimates rho(A_k) by power iteration on the sparse rows,
  - exports a JSON summary suitable for audit/reproduction.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_moment_kernel_hist import (
    build_collision_moment_kernel_sparse,
    build_transducer_from_edges,
    collision_count_lumping_partition,
    histogram_state_count,
    estimate_spectral_radius_sparse,
    pressure_from_rho,
)
from common_paths import export_dir


@dataclass(frozen=True)
class Summary:
    kernel: str
    k: int
    n_states_base: int
    n_states_effective: int
    dim_Hk: int
    dim_formula: str
    rho_est: float
    pressure: float
    seconds_build: float
    seconds_power_iter: float
    lump_by_collision_counts: bool


def _sync10_transducer():
    # Reuse the audited edge list from the fingerprint script.
    import exp_sync_kernel_10_state_uniform_input_fingerprint as sync10

    edges = sync10.build_edges()
    states = list(sync10.STATES)
    input_symbols = sorted({int(e.d) for e in edges})

    T = build_transducer_from_edges(
        states=states,
        input_symbols=input_symbols,
        edges=edges,
        src_attr="src",
        dst_attr="dst",
        in_attr="d",
        out_attr="e",
    )
    return T


def main() -> None:
    ap = argparse.ArgumentParser(description="Demo: histogram-DP construction of collision moment-kernel A_k.")
    ap.add_argument("--kernel", type=str, default="sync10", choices=["sync10"], help="Base deterministic transducer.")
    ap.add_argument("--k", type=int, default=6, help="Moment order k (>=1).")
    ap.add_argument(
        "--lump-col",
        action="store_true",
        help="Pre-quotient Q by collision-count lumping (~col) before building H_k and A_k.",
    )
    ap.add_argument("--iters", type=int, default=2500, help="Power-iteration max iterations.")
    ap.add_argument("--tol", type=float, default=1e-13, help="Relative tolerance for power iteration.")
    ap.add_argument(
        "--max-dim",
        type=int,
        default=50_000,
        help="Safety cap on |H_k|. Use --force to override.",
    )
    ap.add_argument("--force", action="store_true", help="Override --max-dim safety cap.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "moment_kernel_histogram_dp_demo.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    k = int(args.k)
    if k < 1:
        raise SystemExit("Require k>=1")

    if str(args.kernel) == "sync10":
        T = _sync10_transducer()
    else:
        raise SystemExit(f"Unknown kernel {args.kernel!r}")

    n_base = int(T.n_states())
    n_eff = n_base
    if bool(args.lump_col):
        part = collision_count_lumping_partition(T)
        n_eff = int((1 + max(part)) if part else 0)
    dim = histogram_state_count(k, n_eff)
    dim_formula = f"C({k}+{n_eff}-1,{n_eff}-1)=C({k + n_eff - 1},{n_eff - 1})"
    print(
        f"[moment-kernel-hist-demo] kernel={args.kernel} k={k} |Q|={n_base}"
        + (f" -> |Q/~col|={n_eff}" if bool(args.lump_col) else "")
        + f"  |H_k|={dim} ({dim_formula})",
        flush=True,
    )

    if (not args.force) and dim > int(args.max_dim):
        print(
            f"[moment-kernel-hist-demo] SKIP build: |H_k|={dim} exceeds --max-dim={int(args.max_dim)}. "
            f"Rerun with --force to execute.",
            flush=True,
        )
        payload = {
            "kernel": str(args.kernel),
            "k": k,
            "n_states_base": int(n_base),
            "n_states_effective": int(n_eff),
            "dim_Hk": int(dim),
            "dim_formula": dim_formula,
            "lump_by_collision_counts": bool(args.lump_col),
            "note": "Skipped build due to safety cap; rerun with --force to compute rho(A_k).",
        }
        out = Path(str(args.json_out))
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[moment-kernel-hist-demo] wrote {out}", flush=True)
        return

    t0 = time.time()
    _states, rows = build_collision_moment_kernel_sparse(T, k=k, progress_every=0, lump_by_collision_counts=bool(args.lump_col))
    t1 = time.time()
    rho = estimate_spectral_radius_sparse(rows, iters=int(args.iters), tol=float(args.tol))
    t2 = time.time()

    P = pressure_from_rho(rho, k=k, out_alphabet_size=2)
    summary = Summary(
        kernel=str(args.kernel),
        k=k,
        n_states_base=int(n_base),
        n_states_effective=int(n_eff),
        dim_Hk=int(dim),
        dim_formula=dim_formula,
        rho_est=float(rho),
        pressure=float(P),
        seconds_build=float(t1 - t0),
        seconds_power_iter=float(t2 - t1),
        lump_by_collision_counts=bool(args.lump_col),
    )

    payload: Dict[str, object] = {
        "summary": asdict(summary),
        "notes": {
            "A_k_semantics": "k-collision moment kernel on histogram state space H_k (symmetric quotient of Q^k).",
            "pressure_definition": "P(k)=log rho(A_k) - k log 2 (output alphabet size=2).",
        },
    }

    out = Path(str(args.json_out))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"[moment-kernel-hist-demo] rho(A_k)~{rho:.12g}  pressure~{P:.12g}  "
        f"build={summary.seconds_build:.2f}s  power-it={summary.seconds_power_iter:.2f}s",
        flush=True,
    )
    print(f"[moment-kernel-hist-demo] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

