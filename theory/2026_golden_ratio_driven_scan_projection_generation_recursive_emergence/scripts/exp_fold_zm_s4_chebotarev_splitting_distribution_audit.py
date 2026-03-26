#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the effective Chebotarev splitting-type distribution for the Fold Z_m quartic Pi(lambda,y) mod p.

This script is English-only by repository convention.

Setup:
  Pi(lam,y) = lam^4 - lam^3 - (2y+1) lam^2 + lam + y(y+1) in F_p[lam,y].
  For y in F_p define N_p(y) = #{lam in F_p : Pi(lam,y)=0}.

Branch locus (ramified y-values):
  B(y) := y(y-1) P_LY(y), where P_LY(y)=256y^3+411y^2+165y+32.
  We restrict to unramified y in U_p := {y in F_p : B(y) != 0}.

Chebotarev prediction (generic Galois group S_4):
  As p grows, the distribution of N_p(y) over y in U_p approaches the fixed-point distribution
  for a uniformly random permutation in S_4:
    P(N=4)=1/24, P(N=2)=1/4, P(N=1)=1/3, P(N=0)=3/8.
  In particular, the counts differ from these proportions by O(sqrt(p)).

Implementation notes:
  We compute N_p(y) for all y by iterating lam and solving Pi(lam,y)=0 as a quadratic in y:
    y^2 + (1-2 lam^2) y + (lam^4 - lam^3 - lam^2 + lam) = 0,
  with discriminant D(lam)=4 lam^3 - 4 lam + 1.
  Square roots are obtained via a precomputed square table (O(p) time).

Outputs:
  - artifacts/export/fold_zm_s4_chebotarev_splitting_distribution_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence

from common_paths import export_dir


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


def _sample_evenly(xs: Sequence[int], k: int) -> List[int]:
    if k <= 0:
        return []
    if len(xs) <= k:
        return list(xs)
    if k == 1:
        return [xs[-1]]
    idxs = [round(i * (len(xs) - 1) / (k - 1)) for i in range(k)]
    idxs = sorted(set(int(i) for i in idxs))
    return [xs[i] for i in idxs]


def _poly_ply(y: int, p: int) -> int:
    """P_LY(y)=256y^3+411y^2+165y+32 mod p."""
    y %= p
    y2 = (y * y) % p
    y3 = (y2 * y) % p
    return (256 * y3 + 411 * y2 + 165 * y + 32) % p


def _branch_set(p: int) -> List[int]:
    roots: List[int] = [0 % p, 1 % p]
    for y in range(p):
        if _poly_ply(y, p) == 0:
            roots.append(y)
    # Deduplicate
    return sorted(set(roots))


def _sqrt_table(p: int) -> Dict[int, int]:
    """Map each quadratic residue a mod p to one square root r with r^2=a (mod p)."""
    tbl: Dict[int, int] = {0: 0}
    # Use representatives 1..(p-1)//2 to avoid duplicating +-r.
    for r in range(1, (p + 1) // 2):
        a = (r * r) % p
        if a not in tbl:
            tbl[a] = r
    return tbl


def _fiber_root_counts_unramified(p: int) -> tuple[List[int], List[int]]:
    """
    Return (N_p list of length p, branch_y list).
    N_p[y] = #{lam in F_p : Pi(lam,y)=0}.
    """
    if p % 2 == 0:
        raise ValueError("p must be odd.")

    inv2 = (p + 1) // 2
    sqrt_tbl = _sqrt_table(p)

    # Accumulate N_p(y) by iterating lam and solving the quadratic in y.
    Np = [0] * p
    for lam in range(p):
        lam2 = (lam * lam) % p
        lam3 = (lam2 * lam) % p
        b = (1 - 2 * lam2) % p
        disc = (4 * lam3 - 4 * lam + 1) % p  # equals b^2 - 4c
        r = sqrt_tbl.get(disc)
        if r is None:
            continue
        y1 = ((-b + r) * inv2) % p
        y2 = ((-b - r) * inv2) % p
        Np[y1] += 1
        if y2 != y1:
            Np[y2] += 1

    branch = _branch_set(p)
    return Np, branch


@dataclass(frozen=True)
class Row:
    p: int
    branch_y: List[int]
    unramified_count: int
    counts: Dict[str, int]
    expected: Dict[str, float]
    deviation: Dict[str, float]
    deviation_over_sqrtp: Dict[str, float]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Chebotarev splitting-type distribution for Pi(lambda,y) mod p.")
    parser.add_argument("--p-max", type=int, default=2000, help="Generate primes <= p-max.")
    parser.add_argument("--max-primes", type=int, default=25, help="Check at most this many primes (evenly sampled).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    excluded = {2, 3, 31, 37}
    p_max = max(5, int(args.p_max))
    max_primes = max(1, int(args.max_primes))

    primes_all = [p for p in _primes_up_to(p_max) if p not in excluded]
    primes = _sample_evenly(primes_all, max_primes)

    t0 = time.time()
    print("[fold-zm-s4-chebotarev-splitting] start", flush=True)

    # Predicted probabilities for fixed points in S_4 (unramified y).
    probs = {"N4": 1.0 / 24.0, "N2": 1.0 / 4.0, "N1": 1.0 / 3.0, "N0": 3.0 / 8.0}

    rows: List[Row] = []
    ok_all = True
    max_norm_dev = 0.0

    for p in primes:
        Np, branch = _fiber_root_counts_unramified(p)
        branch_set = set(branch)
        unram = [y for y in range(p) if y not in branch_set]
        n_unram = len(unram)

        # Count distribution of N_p(y) over unramified y.
        c0 = c1 = c2 = c4 = 0
        bad_values: List[tuple[int, int]] = []
        for y in unram:
            k = Np[y]
            if k == 0:
                c0 += 1
            elif k == 1:
                c1 += 1
            elif k == 2:
                c2 += 1
            elif k == 4:
                c4 += 1
            else:
                bad_values.append((y, k))

        # For unramified fibers we should never see N=3 (or any other value).
        if bad_values:
            ok_all = False

        counts = {"N4": c4, "N2": c2, "N1": c1, "N0": c0}
        expected = {k: probs[k] * float(n_unram) for k in probs}
        deviation = {k: float(counts[k]) - expected[k] for k in probs}
        sqrtp = math.sqrt(float(p))
        dev_over = {k: deviation[k] / sqrtp for k in probs}
        max_norm_dev = max(max_norm_dev, max(abs(v) for v in dev_over.values()))

        rows.append(
            Row(
                p=int(p),
                branch_y=list(branch),
                unramified_count=int(n_unram),
                counts=counts,
                expected=expected,
                deviation=deviation,
                deviation_over_sqrtp=dev_over,
            )
        )

    payload = {
        "params": {
            "p_max": p_max,
            "max_primes": max_primes,
            "excluded_primes": sorted(excluded),
            "checked_primes": primes,
        },
        "prediction": {
            "probs": probs,
            "note": "Probabilities are fixed-point counts for a uniform random element of S_4.",
        },
        "summary": {
            "ok": ok_all,
            "rows": len(rows),
            "max_abs_deviation_over_sqrtp": float(max_norm_dev),
            "elapsed_s": round(time.time() - t0, 6),
        },
        "rows": [asdict(r) for r in rows],
    }

    out_path = export_dir() / "fold_zm_s4_chebotarev_splitting_distribution_audit.json"
    if not args.no_output:
        _write_json(out_path, payload)

    if not ok_all:
        raise RuntimeError("Unexpected N_p(y) values on unramified set (should be in {0,1,2,4}).")

    print(f"[fold-zm-s4-chebotarev-splitting] ok; wrote={out_path}", flush=True)


if __name__ == "__main__":
    main()

