#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the mod-p splitting behavior of the Lee–Yang cubic

  g(y) = 256 y^3 + 411 y^2 + 165 y + 32

appearing in the Fold Z_m elliptic normalization.

This script is English-only by repository convention.

Theory (Chebotarev / S_3 cubic):
  For primes p not dividing Disc(g), the factorization type of g mod p is determined
  by the Frobenius conjugacy class in Gal(Split(g)/Q) ≅ S_3:
    - identity    <-> (1)(1)(1) (3 roots in F_p),
    - transposition <-> (1)(2)   (exactly 1 root in F_p),
    - 3-cycle     <-> (3)        (no root in F_p).
  Moreover, the quadratic character of the discriminant controls the parity:
    (Disc(g)/p) = sgn(Frob_p).
  Since Disc(g) has squarefree part -111, this predicts:
    (-111/p) = -1  => exactly one root,
    (-111/p) = +1  => either 0 or 3 roots.

We verify the predicted implication on a finite prime window and export a compact
summary for reproducibility.

Outputs (default):
  - artifacts/export/fold_zm_elliptic_leyang_cubic_modp_splitting_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple

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


def _legendre_symbol(a: int, p: int) -> int:
    """Legendre symbol (a/p) for odd prime p, with a not divisible by p."""
    a %= p
    if a == 0:
        return 0
    x = pow(a, (p - 1) // 2, p)
    return -1 if x == p - 1 else 1


def _g_mod_p(y: int, p: int) -> int:
    y %= p
    y2 = (y * y) % p
    y3 = (y2 * y) % p
    return (256 * y3 + 411 * y2 + 165 * y + 32) % p


def _root_count_mod_p(p: int) -> int:
    """Count roots of g(y) in F_p by brute force evaluation."""
    cnt = 0
    for y in range(p):
        if _g_mod_p(y, p) == 0:
            cnt += 1
    return cnt


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit mod-p splitting of the Lee–Yang cubic g(y).")
    parser.add_argument("--p-max", type=int, default=10000, help="Scan primes up to this bound (default: 10000).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    p_max = int(args.p_max)
    if p_max < 5:
        raise SystemExit("--p-max must be >= 5.")

    t0 = time.time()
    print("[fold-zm-leyang-cubic-modp] start", flush=True)

    bad = {3, 31, 37}  # ramified primes for Disc(g) = -3^9 * 31^2 * 37
    primes = [p for p in _primes_up_to(p_max) if p not in bad and p != 2]

    # Counts by root count and by discriminant character.
    counts_total = {0: 0, 1: 0, 3: 0}
    counts_eps = {-1: {0: 0, 1: 0, 3: 0}, +1: {0: 0, 1: 0, 3: 0}}

    # Keep a small sample for audit readability.
    samples: Dict[str, List[int]] = {"roots0": [], "roots1": [], "roots3": [], "eps-1": [], "eps+1": []}

    for p in primes:
        eps = _legendre_symbol(-111, p)
        if eps not in (-1, +1):
            raise RuntimeError("unexpected Legendre symbol value")

        r = _root_count_mod_p(p)
        if r not in (0, 1, 3):
            raise RuntimeError(f"unexpected root count r={r} at p={p} (p should be unramified)")

        # Theoretical implication check.
        if eps == -1 and r != 1:
            raise RuntimeError(f"theory mismatch: (-111/p)=-1 but root count is {r} at p={p}")
        if eps == +1 and r == 1:
            raise RuntimeError(f"theory mismatch: (-111/p)=+1 but root count is 1 at p={p}")

        counts_total[r] += 1
        counts_eps[eps][r] += 1

        if len(samples[f"roots{r}"]) < 12:
            samples[f"roots{r}"].append(p)
        if len(samples[f"eps{eps:+d}"]) < 12:
            samples[f"eps{eps:+d}"].append(p)

    n = sum(counts_total.values())
    if n == 0:
        raise RuntimeError("no primes scanned (unexpected)")

    # Chebotarev-predicted densities for S_3.
    predicted = {"roots1": 1 / 2, "roots3": 1 / 6, "roots0": 1 / 3}

    observed = {
        "roots1": counts_total[1] / n,
        "roots3": counts_total[3] / n,
        "roots0": counts_total[0] / n,
    }
    deltas = {k: observed[k] - predicted[k] for k in predicted}

    payload: Dict[str, object] = {
        "p_max": p_max,
        "excluded_primes": sorted(bad | {2}),
        "num_primes_scanned": n,
        "counts_total": {str(k): int(v) for k, v in counts_total.items()},
        "counts_by_legendre": {
            str(eps): {str(k): int(v) for k, v in counts.items()} for eps, counts in counts_eps.items()
        },
        "predicted_densities": predicted,
        "observed_densities": observed,
        "observed_minus_predicted": deltas,
        "sample_primes": samples,
    }

    if not args.no_output:
        out = export_dir() / "fold_zm_elliptic_leyang_cubic_modp_splitting_audit.json"
        _write_json(out, payload)
        print(f"[fold-zm-leyang-cubic-modp] wrote {out}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-leyang-cubic-modp] done"
        f" primes={n} p_max={p_max}"
        f" obs={{1:{observed['roots1']:.6f},3:{observed['roots3']:.6f},0:{observed['roots0']:.6f}}}"
        f" seconds={dt:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

