#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the joint mod-p full splitting frequency of:

  - Lee–Yang cubic:  P_LY(y) = 256 y^3 + 411 y^2 + 165 y + 32,
  - Lattès critical sextic:  C(X) = 2X^6 - 10X^4 + 10X^3 - 10X^2 + 2X + 1.

This script is English-only by repository convention.

Theory (Chebotarev + linear disjointness, see paper):
  - Gal(Spl(P_LY)/Q) ≅ S_3, hence density(full split) = 1/6.
  - Gal(Spl(C)/Q) ≅ S_4 × C_2 (order 48), hence density(full split) = 1/48.
  - The two Galois closures are linearly disjoint over Q (ramification test),
    hence the joint full-splitting density equals (1/6)*(1/48)=1/288.

We verify the predicted joint frequency on a finite prime window and export a
compact JSON summary for reproducibility.

Outputs (default):
  - artifacts/export/fold_zm_leyang_lattes_joint_splitting_density_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
import warnings
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

from common_paths import export_dir

# Keep pipeline output stable across SymPy versions.
warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _prime_sieve(n: int) -> List[bool]:
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


def _primes_up_to(n: int) -> List[int]:
    sieve = _prime_sieve(n)
    return [p for p in range(2, n + 1) if sieve[p]]


def _factor_degree_pattern(poly_expr: sp.Expr, var: sp.Symbol, p: int) -> Tuple[int, ...]:
    poly = sp.Poly(poly_expr, var, modulus=p)
    _, factors = sp.factor_list(poly, modulus=p)
    degs: List[int] = []
    for f, e in factors:
        degs.extend([int(f.degree())] * int(e))
    degs.sort()
    return tuple(degs)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit joint mod-p full splitting frequency for P_LY(y) and C(X)."
    )
    parser.add_argument(
        "--p-max",
        type=int,
        default=50000,
        help="Scan primes up to this bound (default: 50000).",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    p_max = int(args.p_max)
    if p_max < 5:
        raise SystemExit("--p-max must be >= 5.")

    t0 = time.time()
    print("[fold-zm-joint-splitting] start", flush=True)

    # Exclude primes where either reduction can be inseparable / degenerate.
    # For P_LY: Disc(poly) = -3^9 * 31^2 * 37 (so include 31 to keep factoring-type semantics clean).
    # For C: Disc(C) = -2^8 * 37^5.
    excluded = {2, 3, 31, 37}

    y = sp.Symbol("y")
    X = sp.Symbol("X")
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    C = 2 * X**6 - 10 * X**4 + 10 * X**3 - 10 * X**2 + 2 * X + 1

    primes = [p for p in _primes_up_to(p_max) if p not in excluded]
    n = len(primes)
    if n == 0:
        raise RuntimeError("no primes scanned (unexpected)")

    # Track full splitting events.
    ly_full = 0
    c_full = 0
    both_full = 0

    # Keep small samples for audit readability.
    samples: Dict[str, List[int]] = {"ly_full": [], "c_full": [], "both_full": []}

    for p in primes:
        degs_ly = _factor_degree_pattern(P_LY, y, p)
        degs_c = _factor_degree_pattern(C, X, p)

        is_ly_full = (degs_ly == (1, 1, 1))
        is_c_full = (degs_c == (1, 1, 1, 1, 1, 1))

        if is_ly_full:
            ly_full += 1
            if len(samples["ly_full"]) < 16:
                samples["ly_full"].append(p)
        if is_c_full:
            c_full += 1
            if len(samples["c_full"]) < 16:
                samples["c_full"].append(p)
        if is_ly_full and is_c_full:
            both_full += 1
            if len(samples["both_full"]) < 16:
                samples["both_full"].append(p)

    predicted = {
        "P_LY_full_split": 1.0 / 6.0,
        "C_full_split": 1.0 / 48.0,
        "joint_full_split": 1.0 / 288.0,
    }
    observed = {
        "P_LY_full_split": ly_full / n,
        "C_full_split": c_full / n,
        "joint_full_split": both_full / n,
    }

    payload: Dict[str, object] = {
        "p_max": p_max,
        "excluded_primes": sorted(excluded),
        "num_primes_scanned": n,
        "counts": {
            "P_LY_full_split": ly_full,
            "C_full_split": c_full,
            "joint_full_split": both_full,
        },
        "predicted_densities": predicted,
        "observed_densities": observed,
        "observed_minus_predicted": {k: observed[k] - predicted[k] for k in predicted},
        "sample_primes": samples,
    }

    if not args.no_output:
        out = export_dir() / "fold_zm_leyang_lattes_joint_splitting_density_audit.json"
        _write_json(out, payload)
        print(f"[fold-zm-joint-splitting] wrote {out}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-joint-splitting] done"
        f" primes={n} p_max={p_max}"
        f" joint={both_full} obs_joint={observed['joint_full_split']:.6g}"
        f" seconds={dt:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

