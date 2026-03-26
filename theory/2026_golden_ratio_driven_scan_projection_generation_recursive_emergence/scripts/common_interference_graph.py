#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Interference-graph utilities for the Fold_m lower bound via independent sets.

Paper mapping (Section 8 / Projection-ontology mathematics):
- For a stable word x in X_m (golden-mean legal, no '11'), define
    J(x) = { i in {1,...,m-2} : x_i x_{i+1} x_{i+2} = 100 }.
- The interference graph G(x) has vertex set J(x) and edges between i != j
  iff the length-3 intervals [i,i+2] and [j,j+2] overlap, equivalently |i-j| <= 2.
- The paper proves:
    d_m(x) = #Fold_m^{-1}(x) >= #Ind(G(x)),
  and gives a linear-time DP for #Ind(G(x)) with a block factorization.

This module implements the block DP, and exposes the "defect set" positions that
correspond to local steps of type a_t = a_{t-1} + a_{t-3} (dense triple runs).

All output is English-only by repository convention.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Iterable, List, Sequence, Tuple

_LN2 = math.log(2.0)


def log_int(n: int) -> float:
    """Compute ln(n) for a positive Python int without overflow."""
    if n <= 0:
        raise ValueError("log_int expects n >= 1")
    # Safe fast path for moderate integers.
    b = n.bit_length()
    if b <= 1022:
        return math.log(float(n))
    # Use top 53 bits as a float mantissa.
    shift = b - 53
    top = n >> shift
    return math.log(float(top)) + float(shift) * _LN2


def j_positions_100(word: str) -> List[int]:
    """Return J(x) positions (1-indexed) where word has substring '100'."""
    if any(c not in "01" for c in word):
        raise ValueError("word must be a 0/1 string")
    m = len(word)
    out: List[int] = []
    for i0 in range(0, max(0, m - 2)):
        if word[i0 : i0 + 3] == "100":
            out.append(i0 + 1)  # paper indexing
    return out


def split_blocks_radius2(positions: Sequence[int]) -> List[List[int]]:
    """Split sorted positions into blocks by breakpoints (gap > 2)."""
    if not positions:
        return []
    pos = list(int(p) for p in positions)
    pos.sort()
    blocks: List[List[int]] = []
    cur: List[int] = []
    for p in pos:
        if not cur:
            cur = [p]
            continue
        if p - cur[-1] <= 2:
            cur.append(p)
        else:
            blocks.append(cur)
            cur = [p]
    if cur:
        blocks.append(cur)
    return blocks


@dataclass(frozen=True)
class BlockIndStats:
    """Per-block independent-set DP stats (single block, radius-2 conflicts)."""

    vertices: List[int]  # positions i in the original word, 1-indexed
    ind_sets: int  # #Ind(G[block])
    sigmas: List[int]  # local letter word, values in {2,3}, for steps t=3..k
    defect_steps: List[int]  # t-indices (3..k) where sigma_t=3
    defect_vertices: List[int]  # corresponding i_t (right-end vertex of the triple)

    def to_dict(self) -> dict:
        return asdict(self)


def block_independent_sets_radius2(block_vertices: Sequence[int]) -> BlockIndStats:
    """Compute #Ind for one block (consecutive gaps <= 2), plus defect positions.

    The block is a sorted list of paper-indexed vertices i_1 < ... < i_k with
    i_{t+1}-i_t <= 2 for all t (i.e. one block after breakpoint splitting).
    """
    v = [int(x) for x in block_vertices]
    v.sort()
    k = len(v)
    if k == 0:
        return BlockIndStats(vertices=[], ind_sets=1, sigmas=[], defect_steps=[], defect_vertices=[])
    for a, b in zip(v, v[1:]):
        if b - a > 2:
            raise ValueError("block_vertices is not a single block (found gap > 2)")

    # DP for radius-2 conflict graph on the ordered vertices.
    # Base:
    #   a_0 = 1
    #   a_1 = 2
    # For a single block we always have a_2 = 3 when k >= 2 (since i_2-i_1 <= 2).
    if k == 1:
        return BlockIndStats(vertices=v, ind_sets=2, sigmas=[], defect_steps=[], defect_vertices=[])
    if k == 2:
        return BlockIndStats(vertices=v, ind_sets=3, sigmas=[], defect_steps=[], defect_vertices=[])

    a0, a1, a2 = 1, 2, 3
    a_tm3, a_tm2, a_tm1 = a0, a1, a2  # (a_{t-3}, a_{t-2}, a_{t-1}) at t=3
    sigmas: List[int] = []
    defect_steps: List[int] = []
    defect_vertices: List[int] = []

    # t is the vertex index in the ordered block (paper notation).
    for t in range(3, k + 1):
        # Dense triple iff i_t - i_{t-2} = 2 (equivalently two consecutive +1 gaps).
        if v[t - 1] - v[t - 3] == 2:
            sigma = 3
            a_t = a_tm1 + a_tm3
            defect_steps.append(t)
            defect_vertices.append(v[t - 1])
        else:
            sigma = 2
            a_t = a_tm1 + a_tm2
        sigmas.append(sigma)
        a_tm3, a_tm2, a_tm1 = a_tm2, a_tm1, a_t

    return BlockIndStats(
        vertices=v,
        ind_sets=int(a_tm1),
        sigmas=sigmas,
        defect_steps=defect_steps,
        defect_vertices=defect_vertices,
    )


def independent_sets_via_blocks(word: str) -> Tuple[int, List[BlockIndStats]]:
    """Compute #Ind(G(word)) using breakpoint blocks."""
    J = j_positions_100(word)
    blocks = split_blocks_radius2(J)
    stats: List[BlockIndStats] = []
    total = 1
    for blk in blocks:
        st = block_independent_sets_radius2(blk)
        stats.append(st)
        total *= int(st.ind_sets)
    return int(total), stats


def log_independent_sets_via_blocks(word: str) -> Tuple[float, List[BlockIndStats]]:
    """Compute ln(#Ind(G(word))) as a sum of per-block logs."""
    J = j_positions_100(word)
    blocks = split_blocks_radius2(J)
    stats: List[BlockIndStats] = []
    s = 0.0
    for blk in blocks:
        st = block_independent_sets_radius2(blk)
        stats.append(st)
        s += log_int(int(st.ind_sets))
    return float(s), stats


def defect_gap_list(defect_steps: Sequence[int]) -> List[int]:
    """Return successive gaps in defect step indices (t-space), for one block."""
    ds = [int(x) for x in defect_steps]
    if len(ds) <= 1:
        return []
    return [ds[i + 1] - ds[i] for i in range(len(ds) - 1)]


def flatten(it: Iterable[Iterable[int]]) -> List[int]:
    out: List[int] = []
    for xs in it:
        out.extend(int(x) for x in xs)
    return out

