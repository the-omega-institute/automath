#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Closed-form audit for the path-graph toggle scan element.

We work on the Fibonacci cube Γ_n (Definition~\\ref{def:pom-fibonacci-cube}),
identified with Ind(P_n). Define toggle involutions τ_i (1<=i<=n) by attempting
to flip bit i, applying the flip if the result is Fibonacci-legal, otherwise
doing nothing.

Let c_n = τ_1 τ_2 ... τ_n. This script audits the closed-form results proved
from Joseph–Roby (2018):
  - the closed-form lcm formula for T(n)=ord(c_n) (n>=4),
  - the full orbit-length spectrum,
  - and the full cycle-type multiplicities via primitive necklace counts.

Outputs:
  - artifacts/export/path_toggle_scan_closed_form_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import comb, gcd
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir


def _is_legal(bits: str) -> bool:
    return "11" not in bits


def _vertices_gamma(n: int) -> List[str]:
    n = int(n)
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [""]
    out: List[str] = []
    for x in range(1 << n):
        s = format(x, "0%db" % n)
        if _is_legal(s):
            out.append(s)
    out.sort()
    return out


def _toggle_perm(vertices: List[str], i1: int) -> List[int]:
    """Return permutation τ_i as a list p where p[idx] = idx'."""
    n = len(vertices[0]) if vertices else 0
    i = int(i1) - 1
    if i < 0 or i >= n:
        raise ValueError("toggle index out of range")
    idx = {v: j for j, v in enumerate(vertices)}
    p = list(range(len(vertices)))
    for j, v in enumerate(vertices):
        if n == 0:
            p[j] = j
            continue
        w = list(v)
        w[i] = "1" if w[i] == "0" else "0"
        w2 = "".join(w)
        p[j] = idx[w2] if _is_legal(w2) else j
    return p


def _compose(p: List[int], q: List[int]) -> List[int]:
    """Return composition p∘q (apply q then p)."""
    if len(p) != len(q):
        raise ValueError("perm size mismatch")
    return [p[q[i]] for i in range(len(p))]


def _cycle_lengths_multiset(p: List[int]) -> List[int]:
    n = len(p)
    seen = [False] * n
    lens: List[int] = []
    for i in range(n):
        if seen[i]:
            continue
        j = i
        clen = 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            clen += 1
        lens.append(int(clen))
    lens.sort()
    return lens


def _lcm(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return (a // gcd(a, b)) * b


def _perm_order(p: List[int]) -> int:
    l = 1
    for c in _cycle_lengths_multiset(p):
        l = _lcm(l, c)
    return int(l)


def _prime_factors(n: int) -> Dict[int, int]:
    n = int(n)
    if n < 1:
        raise ValueError("n must be >= 1")
    f: Dict[int, int] = {}
    d = 2
    x = n
    while d * d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0) + 1
            x //= d
        d = 3 if d == 2 else d + 2
    if x > 1:
        f[x] = f.get(x, 0) + 1
    return f


def _mobius(n: int) -> int:
    """Möbius μ(n) for n>=1."""
    if n == 1:
        return 1
    fac = _prime_factors(n)
    for e in fac.values():
        if e >= 2:
            return 0
    return -1 if (len(fac) % 2 == 1) else 1


def _divisors(n: int) -> List[int]:
    n = int(n)
    if n < 1:
        return []
    ds = set([1, n])
    d = 2
    while d * d <= n:
        if n % d == 0:
            ds.add(d)
            ds.add(n // d)
        d += 1
    out = sorted(ds)
    return out


def _n_prim(m: int, a: int) -> int:
    """Primitive binary necklace count N_prim(m,a)."""
    m = int(m)
    a = int(a)
    if m <= 0:
        raise ValueError("m must be >= 1")
    if a < 0 or a > m:
        return 0
    g = gcd(m, a)
    s = 0
    for e in _divisors(g):
        s += _mobius(e) * comb(m // e, a // e)
    if s % m != 0:
        raise AssertionError("Möbius sum not divisible by m")
    return int(s // m)


def _pred_order_closed_form(n: int) -> int:
    n = int(n)
    if n < 0:
        raise ValueError("n must be >= 0")
    if n <= 3:
        return -1  # not asserted by the theorem
    if n % 2 == 0:
        l = 3
        for k in range(1, n // 2):
            l = _lcm(l, 3 * n - 3 - 4 * k)
        return int(l)
    else:
        l = _lcm(2, 3)
        for k in range(1, (n - 1) // 2):
            # for odd n, k ranges 1..(n-3)/2
            if 1 <= k <= (n - 3) // 2:
                l = _lcm(l, 3 * n - 3 - 4 * k)
        return int(l)


def _pred_cycle_counts(n: int) -> Dict[int, int]:
    """Map: cycle_length -> number of cycles, for n>=4."""
    n = int(n)
    if n < 4:
        raise ValueError("n must be >= 4")
    counts: Dict[int, int] = {}

    def add(L: int, c: int) -> None:
        counts[L] = counts.get(L, 0) + int(c)

    add(3, 1)
    if n % 2 == 1:
        add(2, 1)

    # k>0 and N1(k)>0
    for k in range(1, (n - 1) // 2 + 1):
        N1 = n - 1 - 2 * k
        if N1 <= 0:
            continue
        ell = (n - 1 - k)
        gk = gcd(N1, k)
        Lk = 3 * n - 3 - 4 * k
        for d in _divisors(gk):
            m = ell // d
            a = N1 // d
            add(Lk // d, _n_prim(m, a))

    return counts


@dataclass(frozen=True)
class Row:
    n: int
    V: int
    ord_c: int
    pred_ord: int
    ord_ok: bool
    spectrum_ok: bool
    counts_ok: bool
    total_ok: bool
    mismatch: str

    def to_dict(self) -> Dict[str, object]:
        return {
            "n": int(self.n),
            "V": int(self.V),
            "ord_c": int(self.ord_c),
            "pred_ord": int(self.pred_ord),
            "ord_ok": bool(self.ord_ok),
            "spectrum_ok": bool(self.spectrum_ok),
            "counts_ok": bool(self.counts_ok),
            "ok": bool(self.total_ok),
            "mismatch": str(self.mismatch),
        }


def _audit_n(n: int) -> Tuple[Row, Dict[str, object]]:
    vertices = _vertices_gamma(n)
    V = len(vertices)

    # Build c_n = τ_1 ∘ τ_2 ∘ ... ∘ τ_n (composition direction irrelevant for cycle data).
    c = list(range(V))
    for i in range(1, n + 1):
        c = _compose(_toggle_perm(vertices, i), c)

    ord_c = _perm_order(c)
    lens = _cycle_lengths_multiset(c)
    spectrum = sorted(set(lens))

    pred_ord = _pred_order_closed_form(n) if n >= 4 else -1
    ord_ok = True if n < 4 else (ord_c == pred_ord)

    spectrum_ok = True
    counts_ok = True
    mismatch = ""

    detail: Dict[str, object] = {
        "n": int(n),
        "V": int(V),
        "cycle_lengths": lens,
        "cycle_spectrum": spectrum,
        "ord_c": int(ord_c),
    }

    if n >= 4:
        pred_counts = _pred_cycle_counts(n)
        pred_lens = []
        for L, cL in pred_counts.items():
            pred_lens.extend([int(L)] * int(cL))
        pred_lens.sort()

        detail["pred_ord_closed_form"] = int(pred_ord)
        detail["pred_cycle_counts"] = {str(k): int(v) for k, v in sorted(pred_counts.items())}
        detail["pred_cycle_lengths"] = pred_lens
        detail["pred_cycle_spectrum"] = sorted(set(pred_lens))

        spectrum_ok = (sorted(set(lens)) == sorted(set(pred_lens)))
        counts_ok = (lens == pred_lens)

        if not spectrum_ok:
            mismatch += "spectrum "
        if not counts_ok:
            mismatch += "counts "

    total_ok = bool(ord_ok and spectrum_ok and counts_ok)
    row = Row(
        n=n,
        V=V,
        ord_c=ord_c,
        pred_ord=pred_ord,
        ord_ok=ord_ok,
        spectrum_ok=spectrum_ok,
        counts_ok=counts_ok,
        total_ok=total_ok,
        mismatch=mismatch.strip(),
    )
    return row, detail


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-max", type=int, default=12)
    args = ap.parse_args()

    n_max = int(args.n_max)
    if n_max < 0:
        raise ValueError("--n-max must be >= 0")

    rows: List[Row] = []
    details: Dict[str, object] = {"by_n": {}}
    all_ok = True

    for n in range(0, n_max + 1):
        row, detail = _audit_n(n)
        rows.append(row)
        details["by_n"][str(n)] = detail
        all_ok = all_ok and bool(row.total_ok)

    out = {
        "n_max": int(n_max),
        "ok": bool(all_ok),
        "rows": [r.to_dict() for r in rows],
        "details": details,
    }

    out_path: Path = export_dir() / "path_toggle_scan_closed_form_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not all_ok:
        raise SystemExit("Closed-form audit failed (see JSON report).")


if __name__ == "__main__":
    main()

