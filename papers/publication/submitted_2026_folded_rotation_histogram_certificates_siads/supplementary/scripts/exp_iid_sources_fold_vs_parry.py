#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""IID baselines: Bernoulli and Parry source -> Fold_m histogram vs Parry baseline, with TV certificates.

Motivation:
- The rotation (Sturmian) experiment is illustrative but not mixing.
- Here we add IID block sampling to provide finite-sample confidence envelopes (TV) under explicit assumptions.

Outputs:
- artifacts/export/iid_sources_fold_vs_parry.csv
"""

from __future__ import annotations

import csv
import math
import time
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

import numpy as np

from common_paths import export_dir
from common_fold_map_cache import fold_map_packed
from common_phi_fold import Progress, parry_params


def parry_q_and_legal(m: int) -> Tuple[np.ndarray, np.ndarray]:
    """Return (q_parry, legal_idxs) for length-m golden-mean words.

    q_parry is a float64 array of length 2^m, with q_parry[w]=P(word=w) for legal words
    and 0 for illegal words. legal_idxs lists all legal w in increasing order.
    """
    if m < 0:
        raise ValueError("m must be >= 0")
    size = 1 << m
    q = np.zeros(size, dtype=np.float64)
    if m == 0:
        q[0] = 1.0
        return q, np.array([0], dtype=np.int64)

    _phi, pi0, pi1, p00, p01 = parry_params()
    words: List[int] = [0, 1]
    last: List[int] = [0, 1]
    probs: List[float] = [float(pi0), float(pi1)]
    for _ in range(m - 1):
        new_words: List[int] = []
        new_last: List[int] = []
        new_probs: List[float] = []
        for w, l, p in zip(words, last, probs, strict=True):
            # Append 0 (always allowed).
            new_words.append((w << 1) | 0)
            new_last.append(0)
            new_probs.append(p * (p00 if l == 0 else 1.0))
            # Append 1 only after 0.
            if l == 0:
                new_words.append((w << 1) | 1)
                new_last.append(1)
                new_probs.append(p * p01)
        words, last, probs = new_words, new_last, new_probs

    for w, p in zip(words, probs, strict=True):
        q[int(w)] = float(p)
    legal = np.array(sorted(words), dtype=np.int64)
    return q, legal


def weissman_kl_eps(n: int, k: int, delta: float) -> float:
    """A simple high-probability upper bound for KL(ĥ || p) under IID sampling.

    Standard "method of types" / Sanov-style bound for a k-ary distribution:
      P( KL(ĥ || p) >= eps ) <= (n+1)^k * exp(-n eps).

    Solve for eps at confidence 1-delta:
      eps = (k log(n+1) + log(1/delta)) / n.

    This is conservative but fully explicit and assumption-auditable.
    """
    if n <= 0:
        return 1.0
    if k <= 1:
        return 0.0
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must be in (0,1)")
    return (float(k) * math.log(float(n) + 1.0) + math.log(1.0 / delta)) / float(n)


def weissman_tv_eps(n: int, k: int, delta: float) -> float:
    """Return epsilon such that P(TV(ĥ, p) > eps) <= delta for IID samples over k symbols.

    Uses a standard bound (Weissman et al.): P(||ĥ-p||_1 > e) <= 2^k * exp(-n e^2 / 2).
    Thus with e = sqrt(2/n * (k ln2 + ln(1/delta))), we get TV = 0.5 * ||.||_1.
    """
    if n <= 0:
        return 1.0
    if k <= 1:
        return 0.0
    if not (0.0 < delta < 1.0):
        raise ValueError("delta must be in (0,1)")
    e_l1 = math.sqrt((2.0 / float(n)) * (float(k) * math.log(2.0) + math.log(1.0 / delta)))
    return 0.5 * e_l1


def bernoulli_true_folded_dist_array(m: int, p1: float, fold_map: np.ndarray, prog: Progress) -> np.ndarray:
    """Exact pushforward distribution of Fold_m under IID Bernoulli(p1) blocks.

    Returns:
        p_fold: float64 array of length 2^m (mass on legal folded words; zeros elsewhere).
    """
    if not (0.0 <= p1 <= 1.0):
        raise ValueError("p1 must be in [0,1]")
    if m < 0:
        raise ValueError("m must be >= 0")
    size = 1 << m
    if int(fold_map.shape[0]) != size:
        raise ValueError("fold_map has wrong length for m")

    # Microstate probabilities depend only on popcount(w).
    w = np.arange(size, dtype=np.uint32)
    bits = np.unpackbits(w.view(np.uint8), axis=0).reshape(size, 32)
    ones = bits.sum(axis=1).astype(np.int64, copy=False)
    p0 = 1.0 - float(p1)
    pw = (float(p1) ** ones) * (p0 ** (int(m) - ones))

    folded = fold_map[w].astype(np.int64, copy=False)
    p_fold = np.bincount(folded, weights=pw, minlength=size).astype(np.float64, copy=False)
    prog.tick(f"bernoulli_true_folded_dist m={m} size={size}")
    return p_fold


def sample_blocks_bernoulli(rng: np.random.Generator, m: int, n_blocks: int, p1: float) -> np.ndarray:
    """Return packed int blocks of length m, IID Bernoulli(p1)."""
    bits = (rng.random((n_blocks, m)) < p1).astype(np.uint8)
    out = np.zeros(n_blocks, dtype=np.uint32)
    for j in range(m):
        out = (out << 1) | bits[:, j].astype(np.uint32)
    return out


def sample_blocks_parry(rng: np.random.Generator, m: int, n_blocks: int) -> np.ndarray:
    """Return packed int blocks of length m, IID blocks sampled from stationary Parry chain."""
    _, pi0, pi1, p00, p01 = parry_params()
    # For state 0: P(0->0)=p00, P(0->1)=p01. For state 1: P(1->0)=1.
    out = np.zeros(n_blocks, dtype=np.uint32)
    # First bit from stationary distribution.
    s = (rng.random(n_blocks) < pi1).astype(np.uint8)
    out = (out << 1) | s.astype(np.uint32)
    for _ in range(m - 1):
        u = rng.random(n_blocks)
        nxt = np.zeros(n_blocks, dtype=np.uint8)
        # from 0
        mask0 = s == 0
        if mask0.any():
            # 0->1 if u in [p00, 1), i.e. u >= p00
            nxt0 = (u[mask0] >= p00).astype(np.uint8)
            nxt[mask0] = nxt0
        # from 1: always go to 0
        # nxt already 0 on mask1.
        s = nxt
        out = (out << 1) | s.astype(np.uint32)
    return out


@dataclass(frozen=True)
class Case:
    model: str
    p1: float | None  # used only for Bernoulli


def main() -> None:
    out_csv = export_dir() / "iid_sources_fold_vs_parry.csv"
    out_csv.parent.mkdir(parents=True, exist_ok=True)

    # Moderate grid to keep runtime reasonable while still showing finite-sample behavior.
    ms = [6, 8, 10, 12, 14, 16, 18]
    Ns = [2_000, 5_000, 10_000, 30_000, 100_000]
    seeds = [1, 2, 3, 4, 5]
    delta = 0.05  # 95% confidence envelope

    cases = [
        Case(model="parry_iid_blocks", p1=None),
        Case(model="bernoulli_iid_blocks", p1=0.5),
    ]

    prog = Progress("exp_iid_sources_fold_vs_parry", every_seconds=20.0)
    t0_all = time.time()

    # Precompute fold maps and Parry baselines per m.
    fold_maps: Dict[int, np.ndarray] = {}
    parry_qs: Dict[int, np.ndarray] = {}
    legal_idxs: Dict[int, np.ndarray] = {}
    for m in ms:
        fold_maps[m] = fold_map_packed(m, prog=prog).astype(np.uint32, copy=False)
        q, legal = parry_q_and_legal(m)
        parry_qs[m] = q
        legal_idxs[m] = legal

    # Precompute the Bernoulli(p=0.5) exact folded distribution for each m (used for the gap term).
    bernoulli_fold_true: Dict[int, np.ndarray] = {}
    tv_gap_bernoulli: Dict[int, float] = {}
    for m in ms:
        bernoulli_fold_true[m] = bernoulli_true_folded_dist_array(m, 0.5, fold_maps[m], prog)
        L = legal_idxs[m]
        tv_gap_bernoulli[m] = 0.5 * float(np.sum(np.abs(bernoulli_fold_true[m][L] - parry_qs[m][L])))

    with out_csv.open("w", encoding="utf-8", newline="") as f:
        wr = csv.DictWriter(
            f,
            fieldnames=[
                "model",
                "p1",
                "seed",
                "m",
                "N",
                "tv_to_parry",
                "kl_to_parry",
                "kl_to_true",
                "tv_gap_true_to_parry",
                "kl_eps_95",
                "kl_bound_95",
                "tv_eps_95",
                "tv_bound_95",
                "unique_types",
            ],
        )
        wr.writeheader()

        for case in cases:
            for seed in seeds:
                rng = np.random.default_rng(seed)
                for m in ms:
                    fold_map = fold_maps[m]
                    q_parry = parry_qs[m]
                    L = legal_idxs[m]
                    qL = q_parry[L]
                    k = int(L.shape[0])  # alphabet size for folded outputs (legal words)
                    size = 1 << int(m)

                    # True gap term TV(p_true, parry).
                    # Also compute KL(ĥ || p_true) and a non-asymptotic high-probability certificate.
                    if case.model == "parry_iid_blocks":
                        tv_gap = 0.0
                        p_trueL = qL
                    elif case.model == "bernoulli_iid_blocks":
                        tv_gap = float(tv_gap_bernoulli[m])
                        p_trueL = bernoulli_fold_true[m][L]
                    else:
                        raise RuntimeError("unknown case")

                    # Sample once at Nmax and slice prefixes (keeps runtime lower).
                    Nmax = max(Ns)
                    t0 = time.time()
                    if case.model == "parry_iid_blocks":
                        blocks = sample_blocks_parry(rng, m, Nmax)
                    else:
                        assert case.p1 is not None
                        blocks = sample_blocks_bernoulli(rng, m, Nmax, case.p1)

                    # Fold all blocks (vectorized).
                    folded = fold_map[blocks].astype(np.int64, copy=False)

                    counts = np.zeros(size, dtype=np.int64)
                    prev = 0
                    for N in Ns:
                        if N <= prev:
                            raise RuntimeError("Ns must be strictly increasing")
                        counts += np.bincount(folded[prev:N], minlength=size)
                        prev = N

                        cL = counts[L]
                        pL = cL.astype(np.float64) / float(N)
                        tv = 0.5 * float(np.sum(np.abs(pL - qL)))

                        # KL(p_hat || parry) on the legal support.
                        mask = cL > 0
                        if np.any(mask):
                            ppos = pL[mask]
                            qpos = qL[mask]
                            kl = float(np.sum(ppos * np.log(ppos / qpos)))
                        else:
                            kl = 0.0

                        # Finite-sample TV envelope against true model, then triangle to Parry baseline.
                        tv_eps = weissman_tv_eps(N, k, delta=delta)
                        tv_bound = min(1.0, tv_gap + tv_eps)

                        # KL to the true IID model distribution and its certificate.
                        eps = 1e-300
                        if np.any(mask):
                            qtrue = p_trueL[mask]
                            qtrue = np.where(qtrue > 0.0, qtrue, eps)
                            kl_true = float(np.sum(ppos * np.log(ppos / qtrue)))
                        else:
                            kl_true = 0.0
                        kl_eps = weissman_kl_eps(N, k, delta=delta)
                        kl_bound = min(1.0, kl_eps)

                        wr.writerow(
                            {
                                "model": case.model,
                                "p1": "" if case.p1 is None else f"{case.p1:.16g}",
                                "seed": seed,
                                "m": m,
                                "N": N,
                                "tv_to_parry": f"{tv:.12g}",
                                "kl_to_parry": f"{kl:.12g}",
                                "kl_to_true": f"{kl_true:.12g}",
                                "tv_gap_true_to_parry": f"{tv_gap:.12g}",
                                "kl_eps_95": f"{kl_eps:.12g}",
                                "kl_bound_95": f"{kl_bound:.12g}",
                                "tv_eps_95": f"{tv_eps:.12g}",
                                "tv_bound_95": f"{tv_bound:.12g}",
                                "unique_types": int(np.count_nonzero(cL)),
                            }
                        )
                        prog.tick(
                            f"done model={case.model} seed={seed} m={m} N={N} tv={tv:.4g} kl_true={kl_true:.3g} tv_bound95={tv_bound:.3g} kl_eps95={kl_eps:.3g}"
                        )

                    _ = time.time() - t0

    dt_all = time.time() - t0_all
    print(f"[exp_iid_sources_fold_vs_parry] WROTE {out_csv} in {dt_all:.1f}s", flush=True)


if __name__ == "__main__":
    main()

