#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the p-adic Hankel-rigidity DP formula on a fixed instance.

This script is English-only by repository convention.

Let p be a prime and let a_1,...,a_r be distinct integers (viewed in Z_p).
Let omega_1,...,omega_r be nonzero integers (p-adic weights).
For n <= r and I subset {1,...,r} with |I|=n, define:
  omega_I := product_{i in I} omega_i,
  Delta_I := product_{i<j, i,j in I} (a_j-a_i).
Define the p-adic rigidity ideal valuation by:
  v_p(H_n) := min_{|I|=n} v_p(omega_I * Delta_I^2)
           = min_{|I|=n} (sum_{i in I} v_p(omega_i) + 2 * sum_{i<j} v_p(a_j-a_i)).

The paper states a tree DP computes v_p(H_n) using congruence classes mod p^k.
We verify, on a deterministic test instance, that:
  - brute-force minimization over subsets matches the DP for all n,
  - the resulting sequence is discretely convex (nonnegative second differences).

Outputs:
  - artifacts/export/xi_hankel_rigidity_dp_audit.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from dataclasses import dataclass
from typing import Dict, List

from common_paths import export_dir


def _write_json(path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def v_p_int(x: int, p: int) -> int:
    if x == 0:
        raise ValueError("v_p(0) encountered (inputs must be distinct / nonzero).")
    x = abs(x)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


@dataclass(frozen=True)
class Node:
    level: int  # root is level 0, children are level 1, ...
    indices: List[int]  # leaf indices in this node
    children: List["Node"]


def build_tree(a: List[int], p: int) -> Node:
    r = len(a)
    idxs = list(range(r))
    max_v = 0
    for i in range(r):
        for j in range(i + 1, r):
            max_v = max(max_v, v_p_int(a[j] - a[i], p))
    max_level = max_v + 1  # mod p^{max_level} separates all points

    def build_node(indices: List[int], level: int) -> Node:
        if len(indices) <= 1:
            return Node(level=level, indices=list(indices), children=[])
        if level >= max_level:
            # Defensive termination: force leaves.
            children = [Node(level=level + 1, indices=[i], children=[]) for i in indices]
            return Node(level=level, indices=list(indices), children=children)
        mod = p ** (level + 1)
        buckets: Dict[int, List[int]] = {}
        for i in indices:
            buckets.setdefault(a[i] % mod, []).append(i)
        children = [build_node(b, level + 1) for b in buckets.values()]
        # Sort children deterministically by (size, residue representative).
        children = sorted(children, key=lambda nd: (len(nd.indices), min(nd.indices)))
        return Node(level=level, indices=list(indices), children=children)

    return build_node(idxs, level=0)


def dp_rigidity(root: Node, alpha: List[int]) -> List[int]:
    INF = 10**18

    def solve(u: Node) -> List[int]:
        c = len(u.indices)
        if not u.children:
            if c != 1:
                raise RuntimeError("Non-leaf node with no children.")
            i = u.indices[0]
            arr = [INF] * (c + 1)
            arr[0] = 0
            arr[1] = alpha[i]
            return arr

        dp = [INF] * (c + 1)
        dp[0] = 0
        for ch in u.children:
            f = solve(ch)
            new = [INF] * (c + 1)
            for t0 in range(c + 1):
                if dp[t0] >= INF:
                    continue
                # Child can contribute at most its capacity.
                for t1 in range(len(f)):
                    if t0 + t1 > c:
                        break
                    cand = dp[t0] + f[t1]
                    if cand < new[t0 + t1]:
                        new[t0 + t1] = cand
            dp = new

        if u.level > 0:
            # Add 2*binom(t,2) = t(t-1) for non-root levels.
            for t in range(c + 1):
                dp[t] += t * (t - 1)
        return dp

    return solve(root)


def brute_rigidity(a: List[int], alpha: List[int], p: int) -> List[int]:
    r = len(a)
    out = [0] * (r + 1)
    idxs = list(range(r))
    for n in range(1, r + 1):
        best = None
        for I in itertools.combinations(idxs, n):
            v = 0
            for i in I:
                v += alpha[i]
            for i_pos in range(n):
                for j_pos in range(i_pos + 1, n):
                    i = I[i_pos]
                    j = I[j_pos]
                    v += 2 * v_p_int(a[j] - a[i], p)
            if best is None or v < best:
                best = v
        if best is None:
            raise RuntimeError("Unexpected empty brute-force minimization.")
        out[n] = int(best)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit xi Hankel rigidity DP on a fixed instance.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[xi-hankel-rigidity-dp] start", flush=True)

    # Fixed deterministic instance (chosen to have nontrivial congruence tree).
    p = 3
    a = [0, 1, 3, 4, 9, 10, 12, 13]
    omega = [1, 3, 1, 9, 1, 3, 9, 1]

    if len(set(a)) != len(a):
        raise RuntimeError("a_i must be distinct.")
    if any(w == 0 for w in omega):
        raise RuntimeError("omega_i must be nonzero.")

    alpha = [v_p_int(w, p) for w in omega]

    root = build_tree(a, p)
    dp_vals = dp_rigidity(root, alpha)
    brute_vals = brute_rigidity(a, alpha, p)

    ok_all = all(int(dp_vals[n]) == int(brute_vals[n]) for n in range(len(a) + 1))
    if not ok_all:
        raise RuntimeError("DP values do not match brute-force minimization.")

    # Discrete convexity audit (second differences).
    second_diffs = []
    for n in range(1, len(a)):
        second_diffs.append(int(dp_vals[n + 1] - 2 * dp_vals[n] + dp_vals[n - 1]))
    convex_ok = all(d >= 0 for d in second_diffs)

    payload: Dict[str, object] = {
        "p": p,
        "a": a,
        "omega": omega,
        "alpha": alpha,
        "dp_vals": [int(x) for x in dp_vals],
        "brute_vals": [int(x) for x in brute_vals],
        "convex_ok": bool(convex_ok),
        "second_diffs": second_diffs,
        "elapsed_s": float(time.time() - t0),
    }

    if not args.no_output:
        out_json = export_dir() / "xi_hankel_rigidity_dp_audit.json"
        _write_json(out_json, payload)

    print("[xi-hankel-rigidity-dp] ok", flush=True)


if __name__ == "__main__":
    main()

