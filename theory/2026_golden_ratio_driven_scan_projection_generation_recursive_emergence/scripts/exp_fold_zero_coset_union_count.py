#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Exact size of the Fold_m multiplicity spectrum zero set Z_m.

We work on G_m = Z / F_{m+2} Z with residue counts d_m(r) and DFT
  d_hat_m(k) = sum_r d_m(r) * exp(-2π i k r / F_{m+2}).

From the product factorization,
  d_hat_m(k)=0  <=>  exists j in {1..m} s.t. exp(-2π i k F_{j+1}/M)=-1,
where M = F_{m+2}.

For fixed w and g=gcd(w,M), the solution set of exp(-2π i k w/M)=-1 is the
rigid arithmetic-progression coset
  S_g(M) = { k : k ≡ M/(2g) (mod M/g) }   (non-empty iff M even and g | M/2),
and |S_g(M)| = g.

Therefore
  Z_m = ⋃_{j=1}^m S_{g_j}(M),  g_j=gcd(F_{j+1},M),
and the union only depends on the distinct g-values.

This script computes |Z_m| exactly via inclusion-exclusion, using a generalized
CRT solver for intersections of the congruence classes.

Outputs:
- artifacts/export/fold_zero_coset_union_count.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from common_paths import export_dir
from common_phi_fold import fib_upto


def _fib(n: int) -> int:
    if n <= 0:
        raise ValueError("n must be positive")
    return fib_upto(n)[-1]


def _v2(x: int) -> int:
    """2-adic valuation v2(x) for x>0."""
    if x <= 0:
        raise ValueError("x must be positive")
    t = 0
    while (x & 1) == 0:
        x >>= 1
        t += 1
    return t


def _divisors(n: int) -> List[int]:
    if n <= 0:
        raise ValueError("n must be positive")
    small: List[int] = []
    large: List[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
        d += 1
    return small + large[::-1]


def _egcd(a: int, b: int) -> Tuple[int, int, int]:
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = _egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)


def _inv_mod(a: int, mod: int) -> int:
    """Multiplicative inverse of a mod mod (requires gcd(a,mod)=1)."""
    g, x, _y = _egcd(a, mod)
    if g != 1:
        raise ValueError(f"no inverse: gcd({a},{mod})={g}")
    return x % mod


def _crt_merge(a1: int, m1: int, a2: int, m2: int) -> Optional[Tuple[int, int]]:
    """Merge x≡a1 (mod m1), x≡a2 (mod m2). Return (a, lcm) or None."""
    if m1 <= 0 or m2 <= 0:
        raise ValueError("moduli must be positive")
    g = math.gcd(m1, m2)
    delta = a2 - a1
    if delta % g != 0:
        return None
    m1p = m1 // g
    m2p = m2 // g
    # Solve m1p * t ≡ delta/g (mod m2p).
    inv = _inv_mod(m1p % m2p, m2p)
    t = (delta // g) * inv % m2p
    lcm = m1p * m2  # = m1/g * m2
    a = (a1 + m1 * t) % lcm
    return (a, lcm)


def _intersection_size(congruences: Sequence[Tuple[int, int]], M: int) -> int:
    """Size of intersection in Z/MZ of congruences x≡a_i (mod m_i)."""
    a, mod = 0, 1
    for ai, mi in congruences:
        merged = _crt_merge(a, mod, ai % mi, mi)
        if merged is None:
            return 0
        a, mod = merged
    if M % mod != 0:
        raise RuntimeError(f"unexpected: combined modulus {mod} does not divide M={M}")
    return M // mod


@dataclass(frozen=True)
class Coset:
    # S_g(M) = { k : k ≡ a (mod mod) } with mod = M/g, a = M/(2g).
    g: int
    a: int
    mod: int
    # Metadata: which divisor-indices d (with F_d=g) witness this coset.
    ds: Tuple[int, ...]
    v2_g: int


@dataclass(frozen=True)
class Row:
    m: int
    n: int
    M: int
    v2_M: int
    cosets: List[Coset]
    Z_size: int
    Z_density: float
    brute_Z_size: Optional[int]


def _cosets_for_m(m: int) -> List[Coset]:
    n = m + 2
    fib = fib_upto(n)
    M = fib[n - 1]  # F_n
    if M % 2 != 0:
        return []

    # Candidate g-values: for each proper divisor d|n, g=F_d may appear as gcd(F_{j+1},F_n).
    divs = [d for d in _divisors(n) if d < n]
    by_g: Dict[int, List[int]] = {}
    for d in divs:
        g = fib[d - 1]  # F_d
        by_g.setdefault(g, []).append(d)

    out: List[Coset] = []
    for g, ds in sorted(by_g.items()):
        # Solvable iff 2g | M (equivalently g | M/2).
        if M % (2 * g) != 0:
            continue
        mod = M // g
        a = mod // 2  # = M/(2g)
        out.append(
            Coset(
                g=int(g),
                a=int(a),
                mod=int(mod),
                ds=tuple(sorted(ds)),
                v2_g=_v2(int(g)) if int(g) > 0 else 0,
            )
        )
    return out


def _union_size(cosets: Sequence[Coset], M: int) -> int:
    # Inclusion-exclusion over congruence classes.
    total = 0
    idxs = list(range(len(cosets)))
    for r in range(1, len(idxs) + 1):
        sign = 1 if (r % 2 == 1) else -1
        for sub in itertools.combinations(idxs, r):
            congr = [(cosets[i].a, cosets[i].mod) for i in sub]
            size = _intersection_size(congr, M=M)
            total += sign * size
    return int(total)


def _brute_zero_count(m: int, M: int) -> int:
    # Directly check the congruence criterion:
    #   exists j s.t. 2 k F_{j+1} ≡ M (mod 2M).
    fib = fib_upto(m + 2)
    weights = [int(fib[j]) for j in range(1, m + 1)]  # F_{j+1}, j=1..m
    mod2 = 2 * int(M)
    target = int(M) % mod2
    cnt = 0
    for k in range(int(M)):
        ok = False
        kk2 = (2 * k) % mod2
        for w in weights:
            if (kk2 * w) % mod2 == target:
                ok = True
                break
        if ok:
            cnt += 1
    return int(cnt)


def parse_ms(text: str) -> List[int]:
    raw = [chunk.strip() for chunk in text.split(",")] if text else []
    ms: List[int] = []
    for chunk in raw:
        if not chunk:
            continue
        try:
            val = int(chunk)
        except ValueError as exc:
            raise SystemExit(f"[fold-zero] invalid m: {chunk}") from exc
        if val < 1:
            raise SystemExit(f"[fold-zero] require m >= 1, got {val}")
        ms.append(val)
    if not ms:
        ms = [4, 6, 8, 10, 12, 14, 16, 58]
    return sorted(set(ms))


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact Fold_m Fourier zero-set size via coset union + CRT inclusion-exclusion.")
    parser.add_argument("--ms", type=str, default="", help="Comma-separated m values (default: 4,6,8,10,12,14,16,58).")
    parser.add_argument(
        "--brute-max-M",
        type=int,
        default=200_000,
        help="If M=F_{m+2} <= this threshold, brute-check |Z_m| by direct congruence scanning.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_zero_coset_union_count.json"),
    )
    args = parser.parse_args()

    rows: List[Row] = []
    for m in parse_ms(args.ms):
        n = m + 2
        M = _fib(n)
        v2_M = _v2(M) if M > 0 else 0
        cosets = _cosets_for_m(m)
        Z_size = _union_size(cosets, M=M) if cosets else 0
        Z_density = float(Z_size) / float(M) if M > 0 else 0.0

        brute = None
        if M <= int(args.brute_max_M) and M % 2 == 0:
            brute = _brute_zero_count(m=m, M=M)
            if brute != Z_size:
                raise RuntimeError(f"brute mismatch: m={m} M={M} brute={brute} coset={Z_size}")

        rows.append(
            Row(
                m=int(m),
                n=int(n),
                M=int(M),
                v2_M=int(v2_M),
                cosets=list(cosets),
                Z_size=int(Z_size),
                Z_density=float(Z_density),
                brute_Z_size=brute,
            )
        )

    payload = {
        "rows": [asdict(r) for r in rows],
        "notes": {
            "definition": "Z_m = {k mod F_{m+2} : d_hat_m(k)=0}",
            "method": "coset union S_g(M) + generalized CRT + inclusion-exclusion",
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-zero] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

