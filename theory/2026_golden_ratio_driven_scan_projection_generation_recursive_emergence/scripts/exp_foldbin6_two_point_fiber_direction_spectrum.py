#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Window-6: two-point fiber direction spectrum and geometric stabilizer parity-charge.

This experiment is a finite audit at m=6:
  - compute all Fold^{bin}_6 fibers (64 -> 21),
  - classify all two-point fibers by XOR direction vectors in F_2^6,
  - certify how sigma_geo restricts on each two-point fiber (swap vs fix),
  - compute the sign-map support of sigma_geo in the parity-charge lattice (Z_2)^{X_6}.

Outputs:
  - artifacts/export/foldbin6_two_point_fiber_direction_spectrum.json
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir
from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


def _golden_words(m: int) -> List[str]:
    """All length-m binary words with no adjacent ones (golden mean SFT)."""
    out: List[str] = []

    def rec(pos: int, prev1: int, acc: List[int]) -> None:
        if pos == m:
            out.append(word_to_str(acc))
            return
        acc.append(0)
        rec(pos + 1, 0, acc)
        acc.pop()
        if prev1 == 0:
            acc.append(1)
            rec(pos + 1, 1, acc)
            acc.pop()

    rec(0, 0, [])
    out.sort()
    return out


def _K_of_m(m: int) -> int:
    """Return K(m) s.t. F_{K+1} <= 2^m-1 < F_{K+2} (F_1=F_2=1)."""
    target = (1 << m) - 1
    f1, f2 = 1, 1
    idx = 2
    while f2 <= target:
        f1, f2 = f2, f1 + f2
        idx += 1
    return idx - 2


def _fold_bin_prefix(n: int, *, m: int, K: int) -> str:
    digits = zeckendorf_digits(n, K)  # digits for weights F_{k+1}, k=1..K
    return word_to_str(digits[:m])


def _bin6(n: int) -> Tuple[int, int, int, int, int, int]:
    return tuple((n >> i) & 1 for i in range(5, -1, -1))  # type: ignore[return-value]


def _int6(bits: Sequence[int]) -> int:
    out = 0
    for b in bits:
        out = (out << 1) | int(b)
    return out


def _xor6(a: Sequence[int], b: Sequence[int]) -> Tuple[int, int, int, int, int, int]:
    return tuple(int(x) ^ int(y) for x, y in zip(a, b))  # type: ignore[return-value]


def _bits_to_str(bits: Sequence[int]) -> str:
    return "".join(str(int(b)) for b in bits)


def _sigma_geo(bits: Sequence[int]) -> Tuple[int, int, int, int, int, int]:
    w1, w2, w3, w4, w5, w6 = [int(x) for x in bits]
    return (1 - w5, w2, w3, w4, 1 - w1, w6)


def _parity_of_perm(elements: Sequence[int], mapping: Dict[int, int]) -> int:
    """Return permutation parity mod 2 (0 even, 1 odd) via cycle decomposition."""
    seen: set[int] = set()
    transpositions = 0
    for x in elements:
        if x in seen:
            continue
        cur = x
        cyc_len = 0
        while cur not in seen:
            seen.add(cur)
            cyc_len += 1
            cur = mapping[cur]
        transpositions += (cyc_len - 1)
    return transpositions % 2


@dataclass(frozen=True)
class TwoPointFiber:
    w: str
    a: int
    b: int
    v: str
    geo_action: str  # "swap" or "fix"


def main() -> None:
    m = 6
    K = _K_of_m(m)
    if K != 9:
        raise AssertionError(f"Expected K(6)=9, got {K}")

    X6 = _golden_words(m)
    if len(X6) != 21:
        raise AssertionError(f"Unexpected |X6|={len(X6)}")
    bdry = ["100001", "100101", "101001"]
    if sorted([w for w in X6 if w[0] == "1" and w[-1] == "1"]) != bdry:
        raise AssertionError("Unexpected boundary words at m=6")

    pre: Dict[str, List[int]] = {w: [] for w in X6}
    for n in range(1 << m):
        w = _fold_bin_prefix(n, m=m, K=K)
        pre[w].append(n)

    # --- Two-point fibers (exactly those with |pre|=2) ---
    two: List[TwoPointFiber] = []
    for w in X6:
        ns = sorted(pre[w])
        if len(ns) != 2:
            continue
        a, b = ns
        v = _bits_to_str(_xor6(_bin6(a), _bin6(b)))
        # sigma_geo-induced action on the two elements
        img_a = _int6(_sigma_geo(_bin6(a)))
        img_b = _int6(_sigma_geo(_bin6(b)))
        if img_a == b and img_b == a:
            geo = "swap"
        elif img_a == a and img_b == b:
            geo = "fix"
        else:
            raise AssertionError(f"Unexpected sigma_geo restriction on two-point fiber w={w}: {(a,b)} -> {(img_a,img_b)}")
        two.append(TwoPointFiber(w=w, a=a, b=b, v=v, geo_action=geo))

    if len(two) != 8:
        raise AssertionError(f"Unexpected number of two-point fibers: {len(two)}")

    direction_groups: Dict[str, List[str]] = {}
    for f in two:
        direction_groups.setdefault(f.v, []).append(f.w)
    for v in direction_groups:
        direction_groups[v] = sorted(direction_groups[v])

    # --- sgn_6(sigma_geo) support over all fibers (parity-charge lattice) ---
    sgn_support: List[str] = []
    for w in X6:
        elems = pre[w]
        mapping = {n: _int6(_sigma_geo(_bin6(n))) for n in elems}
        if any(mapping[n] not in set(elems) for n in elems):
            raise AssertionError(f"sigma_geo did not preserve fiber: w={w}")
        if _parity_of_perm(elems, mapping) == 1:
            sgn_support.append(w)
    sgn_support.sort()

    out = {
        "m": 6,
        "K": K,
        "X6_size": len(X6),
        "boundary_words": bdry,
        "two_point_fibers": [
            {"w": f.w, "preimage_pair": [f.a, f.b], "direction_xor": f.v, "sigma_geo_action": f.geo_action}
            for f in sorted(two, key=lambda t: t.w)
        ],
        "two_point_direction_spectrum": sorted(direction_groups.keys()),
        "two_point_direction_groups": direction_groups,
        "two_point_sigma_geo_swapped_words": sorted([f.w for f in two if f.geo_action == "swap"]),
        "two_point_sigma_geo_fixed_words": sorted([f.w for f in two if f.geo_action == "fix"]),
        "sgn_support_words": sgn_support,
        "sgn_support_boundary_projection": [w for w in bdry if w in set(sgn_support)],
    }

    p = export_dir() / "foldbin6_two_point_fiber_direction_spectrum.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {p}")


if __name__ == "__main__":
    main()

