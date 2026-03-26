#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Minimality certificate for the 10-state sync-kernel Mealy transducer.

We minimize the deterministic Mealy machine (state, input d) -> (next_state, output e)
under the standard sequential equivalence:
  q ~ q'  iff  for all input words w, the output words from q and q' on w coincide.

This script computes:
- the partition of Q into ~-classes (via refinement to the greatest fixpoint),
- a shortest separating word for each inequivalent pair (q,q') (BFS on product),
- a small LaTeX fragment recording |Q/~| and the max witness length.

Outputs:
- artifacts/export/sync_kernel_10_state_mealy_minimality.json
- sections/generated/eq_sync_kernel_10_state_mealy_minimality.tex

No external deps beyond the stdlib.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from exp_sync_kernel_real_input_40 import KERNEL_STATES, build_kernel_edges


@dataclass(frozen=True)
class Mealy:
    Q: List[str]
    delta: Dict[Tuple[str, int], str]
    eta: Dict[Tuple[str, int], int]


def build_mealy() -> Mealy:
    Q = list(KERNEL_STATES)
    delta: Dict[Tuple[str, int], str] = {}
    eta: Dict[Tuple[str, int], int] = {}
    for e in build_kernel_edges():
        key = (e.src, int(e.d))
        if key in delta:
            raise RuntimeError(f"non-deterministic transition at {key}")
        delta[key] = e.dst
        eta[key] = int(e.e)
    for q in Q:
        for d in (0, 1, 2):
            if (q, d) not in delta or (q, d) not in eta:
                raise RuntimeError(f"missing transition for {(q, d)}")
    return Mealy(Q=Q, delta=delta, eta=eta)


def minimize_mealy(m: Mealy) -> Tuple[List[List[str]], Dict[str, int]]:
    """Return (blocks, class_id_by_state)."""
    Q = m.Q
    # Initial partition by output vectors on single symbols.
    outvec: Dict[str, Tuple[int, int, int]] = {
        q: (m.eta[(q, 0)], m.eta[(q, 1)], m.eta[(q, 2)]) for q in Q
    }
    blocks: List[List[str]] = []
    by_out: Dict[Tuple[int, int, int], List[str]] = {}
    for q in Q:
        by_out.setdefault(outvec[q], []).append(q)
    blocks = [sorted(v) for v in by_out.values()]

    def class_map(bs: List[List[str]]) -> Dict[str, int]:
        mp: Dict[str, int] = {}
        for i, b in enumerate(bs):
            for q in b:
                mp[q] = i
        return mp

    changed = True
    while changed:
        cid = class_map(blocks)
        new_blocks: Dict[Tuple[Tuple[int, int, int], Tuple[int, int, int]], List[str]] = {}
        for q in Q:
            key = (
                outvec[q],
                (cid[m.delta[(q, 0)]], cid[m.delta[(q, 1)]], cid[m.delta[(q, 2)]]),
            )
            new_blocks.setdefault(key, []).append(q)
        blocks2 = [sorted(v) for v in new_blocks.values()]
        blocks2.sort()
        changed = blocks2 != sorted(blocks)
        blocks = blocks2

    cid = class_map(blocks)
    return blocks, cid


def shortest_separating_word(m: Mealy, q: str, r: str) -> str:
    """BFS on product automaton, returns shortest word s.t. outputs differ."""
    if q == r:
        return ""
    from collections import deque

    seen = {(q, r)}
    dq = deque([(q, r, "")])
    while dq:
        a, b, w = dq.popleft()
        for d in (0, 1, 2):
            ea = m.eta[(a, d)]
            eb = m.eta[(b, d)]
            ww = w + str(d)
            if ea != eb:
                return ww
            na = m.delta[(a, d)]
            nb = m.delta[(b, d)]
            st = (na, nb)
            if st not in seen:
                seen.add(st)
                dq.append((na, nb, ww))
    raise RuntimeError(f"no separating word found for {q} vs {r} (unexpected)")


def main() -> None:
    mealy = build_mealy()
    blocks, cid = minimize_mealy(mealy)
    n_classes = len(blocks)

    # Witness words for inequivalent pairs.
    Q = mealy.Q
    witnesses: Dict[str, str] = {}
    max_len = 0
    for i in range(len(Q)):
        for j in range(i + 1, len(Q)):
            a, b = Q[i], Q[j]
            if cid[a] == cid[b]:
                continue
            w = shortest_separating_word(mealy, a, b)
            witnesses[f"{a}|{b}"] = w
            max_len = max(max_len, len(w))

    payload = {
        "states": Q,
        "n_classes": n_classes,
        "classes": blocks,
        "max_separating_word_length": max_len,
        "pair_witness_word": witnesses,
    }

    out_json = export_dir() / "sync_kernel_10_state_mealy_minimality.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    out_tex = generated_dir() / "eq_sync_kernel_10_state_mealy_minimality.tex"
    out_tex.parent.mkdir(parents=True, exist_ok=True)
    out_tex.write_text(
        "\\begin{equation}\\label{eq:sync_kernel_10_state_mealy_minimality}\n"
        f"\\boxed{{\\;|Q/\\!\\sim|={n_classes},\\qquad \\max_{{q\\neq q'}}|w_{{q,q'}}|={max_len}\\;}}.\n"
        "\\end{equation}\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()

