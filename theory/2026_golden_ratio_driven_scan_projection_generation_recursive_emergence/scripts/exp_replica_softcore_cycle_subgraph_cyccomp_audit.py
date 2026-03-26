#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the cyclic-composition coefficient law for cycle-subgraph independent-set counts.

This script is English-only by repository convention.

We enumerate all proper edge subsets S ⊂neq E(C_m) for m in a small range and verify:
  1) C_m[S] is a path forest; component sizes (in cyclic order) define a cyclic composition n of m.
  2) The independent-set count factorizes as
         I(C_m[S]) = ∏_i F_{n_i+2},
     where F is the Fibonacci sequence (F_0=0, F_1=1).
  3) For each cyclic-composition class n (mod rotation), the number of edge subsets realizing it is
         κ(n) = m / rep(n),
     where rep(n) is the maximal repetition count of the cyclic sequence n.

Outputs:
  - artifacts/export/replica_softcore_cycle_subgraph_cyccomp_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fibonacci_upto(n: int) -> List[int]:
    # Returns F[0..n] inclusive.
    if n < 0:
        return []
    F = [0, 1]
    while len(F) <= n:
        F.append(F[-1] + F[-2])
    return F


def _min_rotation(seq: List[int]) -> Tuple[int, ...]:
    if not seq:
        return tuple()
    rots = [tuple(seq[i:] + seq[:i]) for i in range(len(seq))]
    return min(rots)


def _rep_count(seq: Tuple[int, ...]) -> int:
    # Max repetition count of the cyclic sequence: seq is periodic with minimal period p,
    # then rep = len(seq) / p.
    L = len(seq)
    if L == 0:
        return 1
    for p in range(1, L + 1):
        if L % p != 0:
            continue
        ok = True
        for i in range(L):
            if seq[i] != seq[i % p]:
                ok = False
                break
        if ok:
            return L // p
    return 1


def _sizes_from_missing_edges(m: int, present_mask: int) -> List[int]:
    # Edges are indexed by t=0..m-1, edge t connects t and (t+1 mod m).
    # present_mask has bit t=1 iff edge t is present.
    missing = [t for t in range(m) if ((present_mask >> t) & 1) == 0]
    if not missing:
        raise ValueError("Expected a proper subset: at least one missing edge.")
    missing.sort()
    sizes: List[int] = []
    for i in range(len(missing) - 1):
        sizes.append(missing[i + 1] - missing[i])
    sizes.append(missing[0] + m - missing[-1])
    if sum(sizes) != m:
        raise RuntimeError(f"Invalid component sizes: m={m}, sizes={sizes}, sum={sum(sizes)}")
    return sizes


def _component_sizes_graph(m: int, present_mask: int) -> List[int]:
    adj: List[List[int]] = [[] for _ in range(m)]
    for t in range(m):
        if ((present_mask >> t) & 1) == 0:
            continue
        u = t
        v = (t + 1) % m
        if u == v:
            # Self-loop (only possible for m=1). For proper subsets we never include it, but keep safe.
            adj[u].append(v)
        else:
            adj[u].append(v)
            adj[v].append(u)

    seen = [False] * m
    sizes: List[int] = []
    for start in range(m):
        if seen[start]:
            continue
        # BFS
        stack = [start]
        seen[start] = True
        comp: List[int] = []
        while stack:
            v = stack.pop()
            comp.append(v)
            for w in adj[v]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        sizes.append(len(comp))
    return sizes


def _independent_set_count_forest(m: int, present_mask: int) -> int:
    # Tree DP per component (graph is a forest for proper subsets of a cycle).
    adj: List[List[int]] = [[] for _ in range(m)]
    for t in range(m):
        if ((present_mask >> t) & 1) == 0:
            continue
        u = t
        v = (t + 1) % m
        if u == v:
            # Self-loop: forbids selecting the vertex, hence independent sets count is 1 for that component.
            # This case does not occur in our audited ranges for proper subsets (m=1 has no present edges).
            adj[u].append(v)
        else:
            adj[u].append(v)
            adj[v].append(u)

    seen = [False] * m
    total = 1

    for root in range(m):
        if seen[root]:
            continue
        # Build parent/order by DFS
        parent = {root: -1}
        order: List[int] = []
        stack = [root]
        seen[root] = True
        while stack:
            v = stack.pop()
            order.append(v)
            for w in adj[v]:
                if w == parent[v]:
                    continue
                if not seen[w]:
                    seen[w] = True
                    parent[w] = v
                    stack.append(w)

        # Post-order DP
        dp0: Dict[int, int] = {}
        dp1: Dict[int, int] = {}
        for v in reversed(order):
            inc = 1
            exc = 1
            for w in adj[v]:
                if w == parent.get(v, -1):
                    continue
                # include v => exclude child
                inc *= dp0[w]
                # exclude v => child can be in or out
                exc *= dp0[w] + dp1[w]
            dp0[v] = exc
            dp1[v] = inc

        total *= dp0[root] + dp1[root]

    return total


@dataclass(frozen=True)
class MReport:
    m: int
    subsets_checked: int
    classes: int
    base_ok: bool
    multiplicity_ok: bool


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit cyclic-composition multiplicities and Fibonacci bases for cycle-subgraph independent sets."
    )
    parser.add_argument("--m-max", type=int, default=16, help="Max m to audit (default: 16).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    if args.m_max < 1:
        raise SystemExit("--m-max must be >= 1")

    t0 = time.time()
    print("[replica-softcore-cyccomp] start", flush=True)

    F = _fibonacci_upto(args.m_max + 2)

    reports: List[MReport] = []
    all_ok = True

    for m in range(1, args.m_max + 1):
        class_counts: Dict[Tuple[int, ...], int] = {}
        class_base: Dict[Tuple[int, ...], int] = {}

        base_ok = True
        subsets_checked = 0

        # Enumerate present-edge masks, excluding the full cycle mask (all edges present).
        full_mask = (1 << m) - 1
        for present_mask in range(0, full_mask):
            subsets_checked += 1

            sizes = _sizes_from_missing_edges(m, present_mask)
            cls = _min_rotation(sizes)
            class_counts[cls] = class_counts.get(cls, 0) + 1

            # Base value B(n) = ∏ F_{n_i+2}
            B = 1
            for n_i in cls:
                B *= F[n_i + 2]
            class_base[cls] = B

            # Cross-check with graph component sizes and independent-set DP.
            g_sizes = _component_sizes_graph(m, present_mask)
            if sorted(g_sizes) != sorted(list(cls)):
                raise RuntimeError(
                    f"Component-size mismatch: m={m}, mask={present_mask}, sizes={cls}, graph_sizes={g_sizes}"
                )
            ind_dp = _independent_set_count_forest(m, present_mask)
            if ind_dp != B:
                base_ok = False
                raise RuntimeError(
                    f"Independent-set base mismatch: m={m}, mask={present_mask}, got={ind_dp}, expected={B}"
                )

        multiplicity_ok = True
        for cls, cnt in class_counts.items():
            rep = _rep_count(cls)
            expected = m // rep
            if expected * rep != m:
                raise RuntimeError(f"Non-divisibility: m={m}, cls={cls}, rep={rep}")
            if cnt != expected:
                multiplicity_ok = False
                raise RuntimeError(
                    f"Multiplicity mismatch: m={m}, cls={cls}, rep={rep}, cnt={cnt}, expected={expected}"
                )

        reports.append(
            MReport(
                m=m,
                subsets_checked=subsets_checked,
                classes=len(class_counts),
                base_ok=base_ok,
                multiplicity_ok=multiplicity_ok,
            )
        )
        all_ok = all_ok and base_ok and multiplicity_ok

    payload: Dict[str, object] = {
        "m_max": int(args.m_max),
        "all_ok": bool(all_ok),
        "reports": [asdict(r) for r in reports],
    }

    if not args.no_output:
        out = export_dir() / "replica_softcore_cycle_subgraph_cyccomp_audit.json"
        _write_json(out, payload)

    dt = time.time() - t0
    print(f"[replica-softcore-cyccomp] ok all_ok={all_ok} elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

