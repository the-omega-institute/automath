#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Histogram-DP construction for collision moment-kernels A_k of a deterministic transducer.

This module is the executable core behind the "symmetric quotient / coefficient extraction"
interface for moment-kernels:

  - Base kernel K is a deterministic transducer:
        tau: Q × A_in -> Q × A_out
    (state q, input a) ↦ (next_state q', output b).

  - The k-collision moment kernel A_k evolves a multiset of k tracks and enforces
    *output collisions*: at each step all k tracks must emit the same output symbol b.

  - Instead of the exponential state space Q^k, we work on the symmetric quotient
    (histogram states):

        H_k := { ν: Q -> N | Σ_q ν(q) = k },
        |H_k| = C(k+|Q|-1, |Q|-1).

  - For fixed output symbol b, define the per-state generating polynomial

        F_{q,b}(z) := Σ_{a : out(tau(q,a))=b}  z_{next(tau(q,a))}

    (terms can repeat; multiplicities are counted).

    Then the transition weight is the coefficient-extraction formula:

        A_k(ν,ν') = Σ_{b∈A_out}  [z^{ν'}] Π_{q∈Q} F_{q,b}(z)^{ν(q)}.

We implement this coefficient extraction by a reusable dynamic program (DP)
that multiplies (small) multinomial expansions state-by-state.

All output is English-only by repository convention.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Dict, Hashable, Iterable, List, Mapping, Sequence, Tuple

try:
    import numpy as np
except Exception:  # pragma: no cover - optional dependency
    np = None  # type: ignore[assignment]

InSym = Hashable
OutSym = Hashable
Histogram = Tuple[int, ...]
SparseRow = List[Tuple[int, float]]
WeightFn = Callable[[int, InSym], float]


@dataclass(frozen=True)
class DeterministicTransducer:
    """A deterministic transducer tau: Q × A_in -> Q × A_out."""

    states: Tuple[str, ...]
    input_symbols: Tuple[InSym, ...]
    output_symbols: Tuple[OutSym, ...]
    # transition map: (state_idx, input_symbol) -> (next_state_idx, output_symbol)
    trans: Mapping[Tuple[int, InSym], Tuple[int, OutSym]]

    def n_states(self) -> int:
        return len(self.states)


def collision_count_lumping_partition(
    transducer: DeterministicTransducer,
    *,
    output_symbols: Sequence[OutSym] | None = None,
) -> Tuple[int, ...]:
    """Compute a coarsest "collision counting" lumping of states.

    This is the repository's executable form of the paper-side idea:
    states s,t are equivalent if they are indistinguishable by *counts* of
    output-consistent transitions into future equivalence classes.

    Concretely, let Π be a partition of Q. We refine Π until stable under:
        sig_Π(s)[b, B] := #{ a ∈ A_in : out(tau(s,a)) = b  and  next(tau(s,a)) ∈ B }.

    Two states are placed in the same block iff their signatures match for all
    output symbols b (restricted to `output_symbols` if provided).

    Returns:
        block_of_state: a tuple of length |Q| mapping each state index to a block id.
    """
    Q = transducer.n_states()
    if Q <= 0:
        return ()

    out_syms = tuple(output_symbols) if output_symbols is not None else tuple(transducer.output_symbols)
    out_set = set(out_syms)
    if not out_syms:
        raise ValueError("output_symbols must be non-empty")
    out_idx: Dict[OutSym, int] = {b: i for i, b in enumerate(out_syms)}

    # Start from the coarsest partition and refine to a fixpoint.
    block: List[int] = [0] * Q
    while True:
        n_blocks = 1 + max(block) if block else 0

        sig_to_bid: Dict[Tuple[Tuple[int, ...], ...], int] = {}
        new_block: List[int] = [0] * Q

        for s in range(Q):
            # counts[b_idx][bid] where b_idx indexes out_syms.
            counts = [[0] * n_blocks for _ in range(len(out_syms))]
            for a in transducer.input_symbols:
                s2, b = transducer.trans[(s, a)]
                if b not in out_set:
                    continue
                bi = out_idx[b]
                counts[bi][block[s2]] += 1

            sig = tuple(tuple(row) for row in counts)
            if sig not in sig_to_bid:
                sig_to_bid[sig] = len(sig_to_bid)
            new_block[s] = sig_to_bid[sig]

        if new_block == block:
            return tuple(new_block)
        block = new_block


def lump_transducer_by_partition(
    transducer: DeterministicTransducer,
    block_of_state: Sequence[int],
) -> DeterministicTransducer:
    """Build a deterministic transducer on block states preserving transition *counts*.

    The lumped machine keeps the same input alphabet size, but input labels are
    treated as abstract atoms: we only preserve, for each block B and each output
    symbol b, how many inputs go to each next block.

    This is sufficient for the histogram-DP construction of collision moment-kernels,
    which depends only on these multiplicities.
    """
    Q = transducer.n_states()
    if len(block_of_state) != Q:
        raise ValueError("block_of_state length mismatch")
    if Q == 0:
        return transducer

    r = 1 + max(int(x) for x in block_of_state)
    if r <= 0:
        return transducer

    # Choose a deterministic representative for each block.
    reps: List[int] = [-1] * r
    for s, bid in enumerate(block_of_state):
        ib = int(bid)
        if reps[ib] < 0:
            reps[ib] = int(s)
    if any(x < 0 for x in reps):
        raise RuntimeError("internal error: missing representative for some block")

    new_states = tuple(f"B{j}" for j in range(r))
    in_syms = tuple(transducer.input_symbols)
    out_syms = tuple(transducer.output_symbols)

    # For each block state, build an arbitrary deterministic assignment of input labels
    # that realizes the required multiplicities (counts) into next blocks with output b.
    new_trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}

    for bsrc in range(r):
        rep = reps[bsrc]

        # Count (output symbol, next block) multiplicities from the representative.
        counts: Dict[Tuple[OutSym, int], int] = {}
        for a in in_syms:
            s2, b = transducer.trans[(rep, a)]
            bdst = int(block_of_state[s2])
            counts[(b, bdst)] = counts.get((b, bdst), 0) + 1

        # Expand to a length-|A_in| list of (next_block, output_symbol) pairs.
        pairs: List[Tuple[int, OutSym]] = []
        for b in out_syms:
            for bdst in range(r):
                w = int(counts.get((b, bdst), 0))
                if w:
                    pairs.extend([(bdst, b)] * w)

        if len(pairs) != len(in_syms):
            raise RuntimeError(
                f"lumping failed to realize a total transition function: got {len(pairs)} pairs, need {len(in_syms)}"
            )

        for a, (bdst, b) in zip(in_syms, pairs, strict=True):
            new_trans[(bsrc, a)] = (int(bdst), b)

    return DeterministicTransducer(
        states=new_states,
        input_symbols=in_syms,
        output_symbols=out_syms,
        trans=new_trans,
    )


def lump_transducer_by_collision_counts(
    transducer: DeterministicTransducer,
    *,
    output_symbols: Sequence[OutSym] | None = None,
) -> Tuple[DeterministicTransducer, Tuple[int, ...]]:
    """Convenience wrapper: compute partition then build lumped transducer."""
    part = collision_count_lumping_partition(transducer, output_symbols=output_symbols)
    r = (1 + max(part)) if part else 0
    if r == 0 or r == transducer.n_states():
        return transducer, part
    return lump_transducer_by_partition(transducer, part), part


def build_transducer_from_edges(
    *,
    states: Sequence[str],
    input_symbols: Sequence[InSym],
    edges: Iterable[object],
    src_attr: str,
    dst_attr: str,
    in_attr: str,
    out_attr: str,
) -> DeterministicTransducer:
    """Build a DeterministicTransducer from an iterable of edge-like objects."""
    st = tuple(states)
    idx = {s: i for i, s in enumerate(st)}
    A_in = tuple(input_symbols)

    trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}
    out_syms_set: set[OutSym] = set()

    for e in edges:
        src = getattr(e, src_attr)
        dst = getattr(e, dst_attr)
        a = getattr(e, in_attr)
        b = getattr(e, out_attr)
        if src not in idx or dst not in idx:
            raise ValueError(f"Unknown state in edge: src={src!r}, dst={dst!r}")
        key = (idx[src], a)
        val = (idx[dst], b)
        if key in trans and trans[key] != val:
            raise ValueError(f"Non-deterministic transition for {key}: {trans[key]} vs {val}")
        trans[key] = val
        out_syms_set.add(b)

    # Determinism + completeness: expect |Q|*|A_in| transitions.
    expected = len(st) * len(A_in)
    if len(trans) != expected:
        missing: List[Tuple[str, InSym]] = []
        for s in st:
            i = idx[s]
            for a in A_in:
                if (i, a) not in trans:
                    missing.append((s, a))
        raise ValueError(f"Missing transitions (not a total function): {missing[:20]}{' ...' if len(missing)>20 else ''}")

    out_syms = tuple(sorted(out_syms_set, key=lambda x: str(x)))
    return DeterministicTransducer(states=st, input_symbols=A_in, output_symbols=out_syms, trans=trans)


def histogram_state_count(k: int, n_states: int) -> int:
    if k < 0:
        raise ValueError("k must be >= 0")
    if n_states <= 0:
        raise ValueError("n_states must be >= 1")
    return math.comb(k + n_states - 1, n_states - 1)


def histogram_states(k: int, n_states: int) -> List[Histogram]:
    """Enumerate ν ∈ H_k as tuples (ν_0,...,ν_{n-1}) in deterministic lexicographic order."""
    if k < 0:
        raise ValueError("k must be >= 0")
    if n_states <= 0:
        raise ValueError("n_states must be >= 1")

    out: List[Histogram] = []

    def rec(pos: int, remaining: int, prefix: List[int]) -> None:
        if pos == n_states - 1:
            out.append(tuple(prefix + [remaining]))
            return
        for x in range(remaining + 1):
            rec(pos + 1, remaining - x, prefix + [x])

    rec(0, k, [])
    return out


def _fact_upto(n: int) -> List[int]:
    f = [1] * (n + 1)
    for i in range(2, n + 1):
        f[i] = f[i - 1] * i
    return f


def _multinomial(fact: List[int], n: int, parts: Sequence[int]) -> int:
    denom = 1
    for x in parts:
        denom *= fact[x]
    return fact[n] // denom


def _compositions(n: int, d: int) -> Iterable[Tuple[int, ...]]:
    if d <= 0:
        return
    if d == 1:
        yield (n,)
        return
    for x in range(n + 1):
        for rest in _compositions(n - x, d - 1):
            yield (x,) + rest


def build_collision_moment_kernel_sparse(
    transducer: DeterministicTransducer,
    k: int,
    *,
    output_symbols: Sequence[OutSym] | None = None,
    progress_every: int = 0,
    lump_by_collision_counts: bool = False,
) -> Tuple[List[Histogram], List[SparseRow]]:
    """Build sparse rows of the histogram collision kernel A_k.

    Returns:
        (states, rows) where:
          - states is the list of histogram states in H_k
          - rows[i] is a sparse row list [(j, A_k(states[i], states[j]))] with float weights.
    """
    if k < 1:
        raise ValueError("k must be >= 1")

    if lump_by_collision_counts:
        transducer, _part = lump_transducer_by_collision_counts(transducer, output_symbols=output_symbols)

    Q = transducer.n_states()
    out_syms = list(output_symbols) if output_symbols is not None else list(transducer.output_symbols)
    if not out_syms:
        raise ValueError("empty output_symbols")

    out_idx: Dict[OutSym, int] = {b: i for i, b in enumerate(out_syms)}
    n_out = len(out_syms)

    # Precompute dest multiplicities:
    #   dests[q_idx][b_idx] = list[(next_state_idx, multiplicity)]
    dests: List[List[List[Tuple[int, int]]]] = [[[] for _ in range(n_out)] for _ in range(Q)]
    # Build as dicts first to combine repeated next states.
    accum: List[List[Dict[int, int]]] = [[{} for _ in range(n_out)] for _ in range(Q)]
    for q in range(Q):
        for a in transducer.input_symbols:
            q2, b = transducer.trans[(q, a)]
            if b not in out_idx:
                continue
            bi = out_idx[b]
            acc = accum[q][bi]
            acc[q2] = acc.get(q2, 0) + 1
    for q in range(Q):
        for bi in range(n_out):
            items = sorted(accum[q][bi].items(), key=lambda t: t[0])
            dests[q][bi] = [(int(q2), int(w)) for (q2, w) in items if w != 0]

    fact = _fact_upto(k)
    zero: Histogram = (0,) * Q

    @lru_cache(maxsize=None)
    def local_terms(q_idx: int, b_idx: int, n: int) -> Tuple[Tuple[Histogram, int], ...]:
        """Return the sparse multinomial expansion of (Σ_s w_s z_s)^n."""
        if n == 0:
            return ((zero, 1),)
        opts = dests[q_idx][b_idx]
        if not opts:
            return ()
        if len(opts) == 1:
            s, w = opts[0]
            delta = [0] * Q
            delta[s] = n
            return ((tuple(delta), int(w**n)),)

        # General (small) multinomial expansion.
        dest_list = [s for (s, _w) in opts]
        w_list = [w for (_s, w) in opts]
        d = len(dest_list)
        out: List[Tuple[Histogram, int]] = []
        for parts in _compositions(n, d):
            coeff = _multinomial(fact, n, parts)
            # Multiply by weights^counts.
            for wi, ci in zip(w_list, parts, strict=True):
                if ci:
                    coeff *= int(wi**ci)
            if coeff == 0:
                continue
            delta = [0] * Q
            for s, ci in zip(dest_list, parts, strict=True):
                if ci:
                    delta[s] += int(ci)
            out.append((tuple(delta), int(coeff)))
        return tuple(out)

    def convolve(dist: Dict[Histogram, int], terms: Sequence[Tuple[Histogram, int]]) -> Dict[Histogram, int]:
        out: Dict[Histogram, int] = {}
        for h, c1 in dist.items():
            for dh, c2 in terms:
                nh = tuple(h[i] + dh[i] for i in range(Q))
                out[nh] = out.get(nh, 0) + c1 * c2
        return out

    states = histogram_states(k, Q)
    index = {st: i for i, st in enumerate(states)}

    rows: List[SparseRow] = []
    for i, nu in enumerate(states):
        # Build row distribution A_k(nu, ·) as integer weights then cast to floats.
        row_accum: Dict[Histogram, int] = {}
        for b_idx in range(n_out):
            dist: Dict[Histogram, int] = {zero: 1}
            ok = True
            for q_idx, n_tracks in enumerate(nu):
                if n_tracks == 0:
                    continue
                terms = local_terms(q_idx, b_idx, int(n_tracks))
                if not terms:
                    ok = False
                    break
                dist = convolve(dist, terms)
                if not dist:
                    ok = False
                    break
            if not ok:
                continue
            for nu2, w in dist.items():
                row_accum[nu2] = row_accum.get(nu2, 0) + int(w)

        # Deterministic order: by target index.
        row: SparseRow = [(index[nu2], float(w)) for nu2, w in sorted(row_accum.items(), key=lambda t: index[t[0]]) if w]
        rows.append(row)

        if progress_every and (i + 1) % int(progress_every) == 0:
            print(f"[moment-kernel-hist] built {i+1}/{len(states)} rows", flush=True)

    return states, rows


def build_collision_moment_kernel_sparse_weighted(
    transducer: DeterministicTransducer,
    k: int,
    *,
    weight_fn: WeightFn,
    output_symbols: Sequence[OutSym] | None = None,
    progress_every: int = 0,
) -> Tuple[List[Histogram], List[SparseRow]]:
    """Build sparse rows of a *weighted* histogram collision kernel A_k(u,theta,...).

    This is the weighted analog of `build_collision_moment_kernel_sparse`, matching the
    paper-side coefficient-extraction interface where edges carry nonnegative weights:

      F_{q,b}(z) := Σ_{a: out(tau(q,a))=b} w(q,a) · z_{next(tau(q,a))}
      A_k(ν,ν')  := Σ_b  [z^{ν'}]  Π_q F_{q,b}(z)^{ν(q)}.

    Notes:
    - `weight_fn(state_idx, input_symbol)` must return a finite nonnegative float.
    - We do NOT apply collision-count lumping here: the existing lumping routine is
      count-based (integer multiplicities) and is not sound for general real weights.
    """
    if k < 1:
        raise ValueError("k must be >= 1")

    Q = transducer.n_states()
    out_syms = list(output_symbols) if output_symbols is not None else list(transducer.output_symbols)
    if not out_syms:
        raise ValueError("empty output_symbols")

    out_idx: Dict[OutSym, int] = {b: i for i, b in enumerate(out_syms)}
    n_out = len(out_syms)

    # Precompute dest weight-sums:
    #   dests[q_idx][b_idx] = list[(next_state_idx, weight_sum)]
    dests: List[List[List[Tuple[int, float]]]] = [[[] for _ in range(n_out)] for _ in range(Q)]
    accum: List[List[Dict[int, float]]] = [[{} for _ in range(n_out)] for _ in range(Q)]
    for q in range(Q):
        for a in transducer.input_symbols:
            q2, b = transducer.trans[(q, a)]
            if b not in out_idx:
                continue
            w = float(weight_fn(int(q), a))
            if not (w >= 0.0) or (not math.isfinite(w)):
                raise ValueError(f"weight_fn returned invalid weight {w} for (state={q}, input={a!r})")
            if w == 0.0:
                continue
            bi = out_idx[b]
            acc = accum[q][bi]
            acc[q2] = acc.get(q2, 0.0) + w
    for q in range(Q):
        for bi in range(n_out):
            items = sorted(accum[q][bi].items(), key=lambda t: t[0])
            dests[q][bi] = [(int(q2), float(w)) for (q2, w) in items if w != 0.0]

    fact = _fact_upto(k)
    zero: Histogram = (0,) * Q

    @lru_cache(maxsize=None)
    def local_terms(q_idx: int, b_idx: int, n: int) -> Tuple[Tuple[Histogram, float], ...]:
        """Return the sparse multinomial expansion of (Σ_s w_s z_s)^n with real weights."""
        if n == 0:
            return ((zero, 1.0),)
        opts = dests[q_idx][b_idx]
        if not opts:
            return ()
        if len(opts) == 1:
            s, w = opts[0]
            delta = [0] * Q
            delta[s] = n
            return ((tuple(delta), float(w**n)),)

        # General (small) multinomial expansion.
        dest_list = [s for (s, _w) in opts]
        w_list = [float(w) for (_s, w) in opts]
        d = len(dest_list)
        out: List[Tuple[Histogram, float]] = []
        for parts in _compositions(n, d):
            coeff = float(_multinomial(fact, n, parts))
            for wi, ci in zip(w_list, parts, strict=True):
                if ci:
                    coeff *= float(wi**ci)
            if coeff == 0.0:
                continue
            delta = [0] * Q
            for s, ci in zip(dest_list, parts, strict=True):
                if ci:
                    delta[s] += int(ci)
            out.append((tuple(delta), float(coeff)))
        return tuple(out)

    def convolve(dist: Dict[Histogram, float], terms: Sequence[Tuple[Histogram, float]]) -> Dict[Histogram, float]:
        out: Dict[Histogram, float] = {}
        for h, c1 in dist.items():
            for dh, c2 in terms:
                nh = tuple(h[i] + dh[i] for i in range(Q))
                out[nh] = out.get(nh, 0.0) + float(c1) * float(c2)
        return out

    states = histogram_states(k, Q)
    index = {st: i for i, st in enumerate(states)}

    rows: List[SparseRow] = []
    for i, nu in enumerate(states):
        row_accum: Dict[Histogram, float] = {}
        for b_idx in range(n_out):
            dist: Dict[Histogram, float] = {zero: 1.0}
            ok = True
            for q_idx, n_tracks in enumerate(nu):
                if n_tracks == 0:
                    continue
                terms = local_terms(q_idx, b_idx, int(n_tracks))
                if not terms:
                    ok = False
                    break
                dist = convolve(dist, terms)
                if not dist:
                    ok = False
                    break
            if not ok:
                continue
            for nu2, w in dist.items():
                row_accum[nu2] = row_accum.get(nu2, 0.0) + float(w)

        # Deterministic order: by target index.
        row: SparseRow = [
            (index[nu2], float(w))
            for nu2, w in sorted(row_accum.items(), key=lambda t: index[t[0]])
            if w > 0.0
        ]
        rows.append(row)

        if progress_every and (i + 1) % int(progress_every) == 0:
            print(f"[moment-kernel-hist-weighted] built {i+1}/{len(states)} rows", flush=True)

    return states, rows


def estimate_spectral_radius_sparse(
    rows: Sequence[SparseRow],
    *,
    iters: int = 2000,
    tol: float = 1e-12,
) -> float:
    """Estimate the PF spectral radius via L1-normalized power iteration."""
    n = len(rows)
    if n == 0:
        return 0.0
    if np is None:
        # Pure-python fallback (slower but dependency-free).
        v = [1.0 / float(n)] * n
        lam_prev = 0.0
        for _ in range(iters):
            w = [0.0] * n
            for i, row in enumerate(rows):
                s = 0.0
                for j, aij in row:
                    s += float(aij) * float(v[j])
                w[i] = s
            ssum = float(sum(w))
            if not (ssum > 0.0):
                return 0.0
            lam = ssum / float(sum(v))
            w = [x / ssum for x in w]
            if lam_prev > 0.0 and abs(lam - lam_prev) / lam_prev < tol:
                return float(lam)
            v = w
            lam_prev = lam
        return float(lam_prev)

    v = np.ones(n, dtype=np.float64)
    v /= float(n)
    lam_prev = 0.0
    for _ in range(iters):
        w = np.zeros(n, dtype=np.float64)
        for i, row in enumerate(rows):
            s = 0.0
            for j, aij in row:
                s += float(aij) * float(v[j])
            w[i] = s
        ssum = float(np.sum(w))
        if not (ssum > 0.0):
            return 0.0
        lam = ssum / float(np.sum(v))
        w /= ssum
        if lam_prev > 0.0 and abs(lam - lam_prev) / lam_prev < tol:
            return float(lam)
        v = w
        lam_prev = lam
    return float(lam_prev)


def pressure_from_rho(rho: float, k: int, out_alphabet_size: int = 2) -> float:
    if rho <= 0.0:
        return float("-inf")
    if out_alphabet_size <= 1:
        raise ValueError("out_alphabet_size must be >= 2")
    return math.log(float(rho)) - float(k) * math.log(float(out_alphabet_size))

