#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the mod-p fiber root counting identity for the Fold Z_m elliptic normalization.

This script is English-only by repository convention.

We verify, for odd primes p != 37:
  - Let Pi(lam,y)=lam^4-lam^3-(2y+1)lam^2+lam+y(y+1) over F_p.
    For each y in F_p define N_p(y) = #{lam in F_p : Pi(lam,y)=0}.
    Then sum_y N_p(y) equals the number of affine F_p-points on the curve Pi=0.
  - The elliptic normalization gives a bijection between affine points on Pi=0 and
    E(F_p) \\ {O}, hence:
        #E(F_p) = 1 + sum_y N_p(y).
  - Equivalently, for a_p := p+1-#E(F_p), we have:
        a_p = p - sum_y N_p(y),
    and Hasse gives |a_p| <= 2*sqrt(p).

Additionally, for primes p not in {2,3,31,37}, we (optionally) audit the
S4 splitting-type frequencies over unramified fibers y0 in F_p:
  - Exclude branch values where Disc_lam(Pi)= -y(y-1)P_LY(y) vanishes mod p.
  - Factor Pi(lam,y0) in F_p[lam] and record the factor degree pattern.

Outputs:
  - artifacts/export/fold_zm_elliptic_fiber_root_counting_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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


def _legendre_symbol(a: int, p: int) -> int:
    """Return the Legendre symbol (a|p) for odd prime p, with values in {-1,0,1}."""
    a %= p
    if a == 0:
        return 0
    # Euler criterion
    t = pow(a, (p - 1) // 2, p)
    if t == 1:
        return 1
    if t == p - 1:
        return -1
    # Should not happen for prime p, but keep a safe fallback.
    raise RuntimeError(f"Unexpected Euler criterion value t={t} for p={p}.")


def _pi_mod(lam: int, y: int, p: int) -> int:
    lam %= p
    y %= p
    lam2 = (lam * lam) % p
    lam3 = (lam2 * lam) % p
    lam4 = (lam2 * lam2) % p
    # Pi(lam,y)=lam^4-lam^3-(2y+1)lam^2+lam+y(y+1)
    return (lam4 - lam3 - ((2 * y + 1) % p) * lam2 + lam + y * ((y + 1) % p)) % p


def _ply_mod(y: int, p: int) -> int:
    """P_LY(y)=256y^3+411y^2+165y+32 mod p."""
    y %= p
    return (256 * y * y * y + 411 * y * y + 165 * y + 32) % p


def _disc_lam_pi_mod(y: int, p: int) -> int:
    """Disc_lam(Pi)= -y(y-1)P_LY(y) mod p (for odd p)."""
    y %= p
    return (-y * ((y - 1) % p) * _ply_mod(y, p)) % p


def _factor_degree_pattern_pi(lam_sym: sp.Symbol, y0: int, p: int) -> Tuple[int, ...]:
    """Return the sorted factor degree pattern of Pi(lam,y0) over F_p."""
    lam = lam_sym
    poly = sp.Poly(
        lam**4 - lam**3 - (2 * y0 + 1) * lam**2 + lam + y0 * (y0 + 1),
        lam,
        modulus=p,
    )
    _, factors = sp.factor_list(poly, modulus=p)
    degs: List[int] = []
    for f, e in factors:
        degs.extend([int(f.degree())] * int(e))
    degs.sort()
    return tuple(degs)


def _splitting_type_name_from_degrees(degs: Tuple[int, ...]) -> str:
    # Degree-4, squarefree (for unramified y0): only these patterns can occur.
    if degs == (4,):
        return "4"
    if degs == (1, 3):
        return "3+1"
    if degs == (2, 2):
        return "2+2"
    if degs == (1, 1, 2):
        return "2+1+1"
    if degs == (1, 1, 1, 1):
        return "1+1+1+1"
    # Defensive fallback for unexpected patterns.
    return "+".join(str(d) for d in degs)


def _count_pairs_bruteforce(p: int, *, include_fibers: bool) -> tuple[int, Optional[List[int]]]:
    """Return total #{(lam,y): Pi(lam,y)=0} and (optionally) fiber counts N_p(y)."""
    fibers: Optional[List[int]] = [0] * p if include_fibers else None
    total = 0
    for y in range(p):
        cnt = 0
        for lam in range(p):
            if _pi_mod(lam, y, p) == 0:
                cnt += 1
        total += cnt
        if fibers is not None:
            fibers[y] = cnt
    return total, fibers


def _count_pairs_via_quadratic_in_y(p: int) -> int:
    """
    Count affine points on Pi=0 over F_p by viewing Pi(lam,y) as a quadratic in y.

    Pi(lam,y) = y^2 + (1-2lam^2) y + (lam^4-lam^3-lam^2+lam).
    For odd p, the number of y-solutions equals 1 + (disc|p), where disc=b^2-4c.
    """
    total = 0
    for lam in range(p):
        lam2 = (lam * lam) % p
        lam3 = (lam2 * lam) % p
        disc = (4 * lam3 - 4 * lam + 1) % p  # equals (1-2lam^2)^2 - 4(lam^4-lam^3-lam^2+lam)
        total += 1 + _legendre_symbol(disc, p)
    return total


@dataclass(frozen=True)
class Row:
    p: int
    sum_Np: int
    E_count: int
    a_p: int
    hasse_ok: bool
    bruteforce_checked: bool
    bruteforce_ok: bool
    fiber_counts: Optional[List[int]]


@dataclass(frozen=True)
class S4SplitRow:
    p: int
    y_unramified_count: int
    y_ramified_values: List[int]
    counts: Dict[str, int]
    proportions: Dict[str, float]
    expected: Dict[str, float]
    max_abs_error: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit fiber root counting identity for Pi(lambda,y) mod p.")
    parser.add_argument("--p-max", type=int, default=401, help="Check all primes <= p-max (excluding 2,37).")
    parser.add_argument(
        "--bruteforce-p-max",
        type=int,
        default=101,
        help="For primes <= this bound, also brute force N_p(y) fibers (O(p^2)).",
    )
    parser.add_argument(
        "--store-fibers",
        action="store_true",
        help="Store fiber counts N_p(y) for brute-forced primes in the JSON payload.",
    )
    parser.add_argument(
        "--splitting-density-p-max",
        type=int,
        default=None,
        help=(
            "For primes <= this bound, also audit S4 splitting-type frequencies over unramified fibers "
            "(excluding p in {2,3,31,37}). Default: bruteforce_p_max."
        ),
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    p_max = max(3, int(args.p_max))
    brute_p_max = max(3, int(args.bruteforce_p_max))
    store_fibers = bool(args.store_fibers)
    split_p_max = brute_p_max if args.splitting_density_p_max is None else max(3, int(args.splitting_density_p_max))

    t0 = time.time()
    print("[fold-zm-elliptic-fiber-root-count] start", flush=True)

    rows: List[Row] = []
    split_rows: List[S4SplitRow] = []
    ok_all = True
    lam_sym = sp.Symbol("lam")

    s4_expected: Dict[str, float] = {
        "4": 1.0 / 4.0,  # 4-cycles: 6/24
        "3+1": 1.0 / 3.0,  # 3-cycles: 8/24
        "2+2": 1.0 / 8.0,  # double transpositions: 3/24
        "2+1+1": 1.0 / 4.0,  # transpositions: 6/24
        "1+1+1+1": 1.0 / 24.0,  # identity: 1/24
    }

    for p in _primes_up_to(p_max):
        if p in {2, 37}:
            continue
        if p % 2 == 0:
            continue

        sum_Np_fast = _count_pairs_via_quadratic_in_y(p)
        E_count = sum_Np_fast + 1
        a_p = p + 1 - E_count
        hasse_ok = (a_p * a_p) <= (4 * p)

        bruteforce_checked = p <= brute_p_max
        bruteforce_ok = True
        fibers: Optional[List[int]] = None
        if bruteforce_checked:
            sum_Np_brute, fibers_raw = _count_pairs_bruteforce(p, include_fibers=store_fibers)
            bruteforce_ok = (sum_Np_brute == sum_Np_fast)
            if store_fibers:
                fibers = fibers_raw
        row = Row(
            p=p,
            sum_Np=sum_Np_fast,
            E_count=E_count,
            a_p=a_p,
            hasse_ok=hasse_ok,
            bruteforce_checked=bruteforce_checked,
            bruteforce_ok=bruteforce_ok,
            fiber_counts=fibers,
        )
        rows.append(row)
        ok_all = ok_all and hasse_ok and bruteforce_ok

        if p <= split_p_max and p not in {2, 3, 31, 37}:
            # Unramified fibers are exactly y0 with Disc_lam(Pi)(y0) != 0 mod p.
            y_ramified = [y0 for y0 in range(p) if _disc_lam_pi_mod(y0, p) == 0]
            counts: Dict[str, int] = {k: 0 for k in s4_expected.keys()}
            other_counts: Dict[str, int] = {}
            for y0 in range(p):
                if _disc_lam_pi_mod(y0, p) == 0:
                    continue
                degs = _factor_degree_pattern_pi(lam_sym, y0, p)
                name = _splitting_type_name_from_degrees(degs)
                if name in counts:
                    counts[name] += 1
                else:
                    other_counts[name] = other_counts.get(name, 0) + 1
            if other_counts:
                for k, v in other_counts.items():
                    counts[k] = v

            y_unram = p - len(y_ramified)
            if sum(counts.values()) != y_unram:
                raise RuntimeError(
                    f"S4 splitting audit mismatch for p={p}: sum={sum(counts.values())} unram={y_unram}"
                )
            proportions = {k: (counts[k] / y_unram) for k in counts.keys()}
            max_abs_err = 0.0
            for k, exp in s4_expected.items():
                max_abs_err = max(max_abs_err, abs(proportions.get(k, 0.0) - exp))
            split_rows.append(
                S4SplitRow(
                    p=p,
                    y_unramified_count=y_unram,
                    y_ramified_values=y_ramified,
                    counts=counts,
                    proportions=proportions,
                    expected=s4_expected,
                    max_abs_error=max_abs_err,
                )
            )

    payload = {
        "params": {
            "p_max": p_max,
            "bruteforce_p_max": brute_p_max,
            "excluded_primes": [2, 37],
            "store_fibers": store_fibers,
            "splitting_density_p_max": split_p_max,
            "splitting_density_excluded_primes": [2, 3, 31, 37],
        },
        "summary": {
            "ok": ok_all,
            "checked_primes": len(rows),
            "elapsed_s": round(time.time() - t0, 6),
        },
        "rows": [asdict(r) for r in rows],
        "s4_splitting_density_audit": {
            "rows": [asdict(r) for r in split_rows],
        },
    }

    out_path = export_dir() / "fold_zm_elliptic_fiber_root_counting_audit.json"
    if not args.no_output:
        _write_json(out_path, payload)

    if not ok_all:
        raise RuntimeError("Fiber root counting audit failed for at least one prime.")

    print(f"[fold-zm-elliptic-fiber-root-count] ok; wrote={out_path}", flush=True)


if __name__ == "__main__":
    main()

