#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Rotation scan -> window microstates -> Fold_m histogram vs Parry baseline.

Outputs:
- artifacts/export/rotation_fold_vs_parry.csv
"""

from __future__ import annotations

import csv
import math
import time
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

import numpy as np

from common_paths import export_dir
from common_ostrowski_fold import metallic_alpha
from common_phi_fold import PHI, Progress, fold_m, is_golden_legal


def _pack_bits_to_int(bits: Iterable[int], m: int) -> int:
    """Pack length-m bits into an int, MSB is position 1."""
    x = 0
    for b in bits:
        x = (x << 1) | (1 if b else 0)
    return x & ((1 << m) - 1)


def _int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def build_fold_map(m: int, prog: Progress) -> List[int]:
    """Map each microstate int in [0,2^m) to folded int in [0,2^m)."""
    size = 1 << m
    out = [0] * size
    for w in range(size):
        bits = _int_to_bits(w, m)
        folded = fold_m(bits)
        out[w] = _pack_bits_to_int(folded, m)
        # Avoid per-iteration f-string overhead; Progress already rate-limits prints.
        if (w & 0x3FFF) == 0:
            prog.tick(f"build_fold_map m={m} w={w}/{size}")
    return out


def build_parry_q(m: int) -> Dict[int, float]:
    """Parry cylinder distribution on legal length-m words, keyed by packed int."""
    # Parameters from the paper: pi(1)=1/(phi^2+1), pi(0)=1-pi(1);
    # transitions: 00 with 1/phi, 01 with 1/phi^2, 10 with 1.
    pi1 = 1.0 / (PHI * PHI + 1.0)
    pi0 = 1.0 - pi1
    p00 = 1.0 / PHI
    p01 = 1.0 / (PHI * PHI)

    q: Dict[int, float] = {}
    for w in range(1 << m):
        # Fast legality check on packed bits: forbid adjacent 1s.
        if (w & (w >> 1)) != 0:
            continue
        bits = _int_to_bits(w, m)
        p = pi1 if bits[0] == 1 else pi0
        ok = True
        for a, b in zip(bits, bits[1:]):
            if a == 0 and b == 0:
                p *= p00
            elif a == 0 and b == 1:
                p *= p01
            elif a == 1 and b == 0:
                p *= 1.0
            else:
                ok = False
                break
        if ok:
            q[w] = p
    return q


def tv_distance_int(p: Dict[int, float], q: Dict[int, float]) -> float:
    keys = set(p.keys()) | set(q.keys())
    s = 0.0
    for k in keys:
        s += abs(p.get(k, 0.0) - q.get(k, 0.0))
    return 0.5 * s


def kl_divergence_int(p: Dict[int, float], q: Dict[int, float], eps: float = 1e-300) -> float:
    s = 0.0
    for k, pk in p.items():
        if pk <= 0.0:
            continue
        qk = q.get(k, 0.0)
        qk = qk if qk > 0.0 else eps
        s += pk * math.log(pk / qk)
    return s


def star_discrepancy(xs: np.ndarray) -> float:
    """Exact 1D star discrepancy for points in [0,1), by sorting."""
    n = int(xs.size)
    if n <= 0:
        return 1.0
    ys = np.sort(xs.astype(np.float64, copy=False))
    invn = 1.0 / float(n)
    i = np.arange(1, n + 1, dtype=np.float64)
    m1 = float(np.max(i * invn - ys))
    m2 = float(np.max(ys - (i - 1.0) * invn))
    return float(max(m1, m2))


def _golden_discrepancy_upper_bound_explicit(N: int) -> float:
    """Appendix-H explicit bound for alpha=phi^{-1}, valid for N>=2."""
    if N < 2:
        return 1.0
    return (3.0 + math.ceil(math.log((5.0 ** 0.5) * N) / math.log(PHI))) / float(N)


def discrepancy_upper_bound_from_partial_quotients(N: int, a: List[int]) -> float:
    """Upper bound via partial quotients: D_N^* <= (1 + sum_{j=1}^{n+1} a_j)/N.

    Uses denominators q_n from continued fractions; valid uniformly in x0.
    """
    if N < 1:
        return 1.0
    if any(x < 1 for x in a):
        raise ValueError("partial quotients must be >= 1")

    # Build q_n until q_n <= N < q_{n+1}.
    # q_{-1}=0, q_0=1, q_{k+1}=a_{k+1} q_k + q_{k-1}.
    q_minus_1 = 0
    q_0 = 1
    qs = [q_0]
    q_prev, q_curr = q_minus_1, q_0
    # We will extend with 1's if needed (tail-ones family).
    # This is enough for the experiment families we use.
    a_extended: List[int] = list(a)

    # Ensure we have enough digits to push q above N.
    while True:
        k = len(qs) - 1  # current index is q_k
        if q_curr > N:
            break
        # Need a_{k+1}
        if k + 1 > len(a_extended):
            a_extended.append(1)
        ak1 = a_extended[k]  # a_{k+1} with 1-based indexing
        q_next = ak1 * q_curr + q_prev
        qs.append(q_next)
        q_prev, q_curr = q_curr, q_next

    # Find n s.t. q_n <= N < q_{n+1}. Since qs[-1] = q_{K} > N, take n=K-1.
    n = len(qs) - 2
    # Need sum_{j=1}^{n+1} a_j. Ensure a_extended is long enough.
    while len(a_extended) < n + 1:
        a_extended.append(1)
    sum_a = sum(a_extended[: n + 1])
    return (1.0 + float(sum_a)) / float(N)


def rotation_bits(alpha: float, x0: float, beta: float, n: int) -> np.ndarray:
    """Binary readout s_t = 1_{[0,beta)}({x0 + t alpha}), length n."""
    ts = np.arange(n, dtype=np.float64)
    xs = (x0 + alpha * ts) % 1.0
    return (xs < beta).astype(np.uint8)


def rotation_points(alpha: float, x0: float, n: int) -> np.ndarray:
    """Kronecker points x_t = {x0 + t alpha} in [0,1), length n."""
    ts = np.arange(n, dtype=np.float64)
    return (x0 + alpha * ts) % 1.0


@dataclass(frozen=True)
class Config:
    alpha_name: str
    alpha: float
    partial_quotients_prefix: List[int]
    beta: float
    x0: float


def _packed_windows_by_m(
    s_bits: np.ndarray,
    *,
    N: int,
    m_max: int,
    needed_ms: Iterable[int],
) -> Dict[int, np.ndarray]:
    """Pack all length-m windows (MSB-first) for selected m, using vectorized shift-append.

    For each requested m, returns an array `w_m` of length N where:
        w_m[t] = pack(s_bits[t:t+m])  in [0,2^m).
    """
    if N <= 0:
        raise ValueError("N must be positive")
    if m_max <= 0:
        raise ValueError("m_max must be positive")
    need = sorted(set(int(x) for x in needed_ms))
    if not need:
        return {}
    if min(need) < 1 or max(need) > m_max:
        raise ValueError("needed_ms must satisfy 1 <= m <= m_max")
    if len(s_bits) < N + m_max - 1:
        raise ValueError("s_bits too short for requested N and m_max")
    if s_bits.dtype != np.uint8:
        s_bits = s_bits.astype(np.uint8, copy=False)
    # Cast once (avoid per-step uint8->uint32 conversions on large slices).
    s32 = s_bits.astype(np.uint32, copy=False)

    out: Dict[int, np.ndarray] = {}
    w = s32[:N]
    if 1 in need:
        out[1] = w.copy()

    for m in range(2, m_max + 1):
        nxt = s32[m - 1 : m - 1 + N]
        w = (w << 1) | nxt
        if m in need:
            out[m] = w.copy()
    return out


def pushforward_truncate_last_bit(counts_m1: Dict[int, int]) -> Dict[int, int]:
    """Push forward X_{m+1} histogram to X_m by truncating the last bit (prefix map)."""
    out: Dict[int, int] = {}
    for w, c in counts_m1.items():
        out[w >> 1] = out.get(w >> 1, 0) + c
    return out


def main() -> None:
    out_csv = export_dir() / "rotation_fold_vs_parry.csv"
    out_csv.parent.mkdir(parents=True, exist_ok=True)

    # Systematic but bounded grid (keeps runtime reasonable).
    # NOTE: build_fold_map scales like 2^m, so keep max m moderate.
    ms = [6, 8, 10, 12, 14, 16, 18]
    Ns = [10_000, 30_000, 100_000, 300_000]

    # Deterministic (beta,x0) replicates for error bars.
    betas = [0.2, 0.3, 0.5, 0.6180339887]
    x0s = [0.123, 0.271, 0.731]

    # Alpha families:
    # - bounded partial quotients (metallic means): [0;A,A,A,...]
    # - large partial quotient then ones: [0;B,1,1,1,...] to stress resonance.
    alpha_families: List[Tuple[str, float, List[int]]] = []

    for A in [1, 2, 3, 5]:
        name = "golden" if A == 1 else f"metal_{A}"
        alpha_families.append((name, metallic_alpha(A), [A]))

    # Large-partial-quotient prefix, then a tail of ones (approximated by float alpha).
    # We record the prefix so we can compute discrepancy upper bounds consistently.
    for B in [10, 30, 100]:
        # alpha ~ [0; B, 1, 1, 1, ...]
        # We implement this by solving the tail ones exactly: tail = 1/phi.
        tail = 1.0 / PHI
        alpha = 1.0 / (float(B) + tail)
        alpha_families.append((f"large_pq_{B}_then_ones", alpha, [B, 1]))

    configs: List[Config] = []
    for (alpha_name, alpha, pq_prefix) in alpha_families:
        for beta in betas:
            for x0 in x0s:
                configs.append(
                    Config(
                        alpha_name=alpha_name,
                        alpha=alpha,
                        partial_quotients_prefix=list(pq_prefix),
                        beta=float(beta),
                        x0=float(x0),
                    )
                )

    # Precompute fold maps and Parry baselines per m.
    fold_maps: Dict[int, np.ndarray] = {}
    parry_qs: Dict[int, np.ndarray] = {}
    legal_idxs: Dict[int, np.ndarray] = {}

    prog = Progress("exp_rotation_fold_vs_parry", every_seconds=20.0)

    t0_all = time.time()
    # For cross-resolution residual E_m we may need fold maps at m+1 (prefix pushforward).
    m_em_max = 14
    ms_all = set(ms) | {m + 1 for m in ms if m + 1 <= m_em_max}
    for m in sorted(ms_all):
        fold_maps[m] = np.asarray(build_fold_map(m, prog), dtype=np.uint32)
        q_dict = build_parry_q(m)
        q_arr = np.zeros(1 << m, dtype=np.float64)
        for k, v in q_dict.items():
            q_arr[int(k)] = float(v)
        parry_qs[m] = q_arr
        # Legal word indices (no adjacent 1s) for fast TV/KL on the support.
        ws = np.arange(1 << m, dtype=np.uint32)
        legal_idxs[m] = np.nonzero((ws & (ws >> 1)) == 0)[0].astype(np.int64, copy=False)

    with out_csv.open("w", encoding="utf-8", newline="") as f:
        wr = csv.DictWriter(
            f,
            fieldnames=[
                "model",
                "alpha_name",
                "alpha",
                "partial_quotients_prefix",
                "beta",
                "x0",
                "m",
                "N",
                "tv",
                "kl",
                "unique_types",
                "DN_star_upper_bound",
                "DN_star_exact",
                "tv_multiscale_residual",
            ],
        )
        wr.writeheader()

        Nmax = max(Ns)
        max_m_needed = max(fold_maps.keys())

        # Cache discrepancy computations across betas (xs_full depends only on alpha,x0).
        xs_cache: Dict[Tuple[float, float], np.ndarray] = {}
        dn_star_exact_cache: Dict[Tuple[float, float, int], float] = {}
        dn_star_ub_cache: Dict[Tuple[str, Tuple[int, ...], int], float] = {}

        for cfg in configs:
            ax_key = (cfg.alpha, cfg.x0)
            if ax_key not in xs_cache:
                xs_cache[ax_key] = rotation_points(cfg.alpha, cfg.x0, Nmax)
            xs_full = xs_cache[ax_key]

            dn_star_exact_by_N: Dict[int, float] = {}
            for N in Ns:
                k = (cfg.alpha, cfg.x0, int(N))
                if k not in dn_star_exact_cache:
                    dn_star_exact_cache[k] = star_discrepancy(xs_full[:N])
                dn_star_exact_by_N[N] = dn_star_exact_cache[k]

            dn_star_ub_by_N: Dict[int, float] = {}
            pq_key = (cfg.alpha_name, tuple(int(x) for x in cfg.partial_quotients_prefix))
            for N in Ns:
                k = (pq_key[0], pq_key[1], int(N))
                if k not in dn_star_ub_cache:
                    if cfg.alpha_name == "golden":
                        dn_star_ub_cache[k] = min(
                            _golden_discrepancy_upper_bound_explicit(N),
                            discrepancy_upper_bound_from_partial_quotients(N, cfg.partial_quotients_prefix),
                        )
                    else:
                        dn_star_ub_cache[k] = discrepancy_upper_bound_from_partial_quotients(N, cfg.partial_quotients_prefix)
                dn_star_ub_by_N[N] = dn_star_ub_cache[k]

            # Generate one long bitstream and pack all window-words we may need.
            s_len = Nmax + max_m_needed - 1
            s_full = rotation_bits(cfg.alpha, cfg.x0, cfg.beta, s_len)
            words_by_m = _packed_windows_by_m(s_full, N=Nmax, m_max=max_m_needed, needed_ms=fold_maps.keys())

            for m in ms:
                fold_map = fold_maps[m]
                legal = legal_idxs[m]
                q_legal = parry_qs[m][legal]

                words_m = words_by_m[m]
                folded_m = fold_map[words_m]
                if np.any((folded_m & (folded_m >> 1)) != 0):
                    raise RuntimeError("Fold produced illegal word(s)")

                folded_m1 = None
                if (m + 1) in fold_maps:
                    fold_map_m1 = fold_maps[m + 1]
                    words_m1 = words_by_m[m + 1]
                    folded_m1 = fold_map_m1[words_m1]
                    if np.any((folded_m1 & (folded_m1 >> 1)) != 0):
                        raise RuntimeError("Fold produced illegal word(s) at m+1")

                counts = np.zeros(1 << m, dtype=np.int64)
                counts_m1 = np.zeros(1 << (m + 1), dtype=np.int64) if folded_m1 is not None else None
                prev = 0
                for N in Ns:
                    counts += np.bincount(folded_m[prev:N], minlength=(1 << m))
                    if counts_m1 is not None and folded_m1 is not None:
                        counts_m1 += np.bincount(folded_m1[prev:N], minlength=(1 << (m + 1)))
                    prev = N

                    counts_legal = counts[legal]
                    p_legal = counts_legal.astype(np.float64) / float(N)

                    tv = 0.5 * float(np.sum(np.abs(p_legal - q_legal)))

                    # KL(p||q) on the legal support.
                    eps = 1e-300
                    mask = counts_legal > 0
                    if np.any(mask):
                        ppos = p_legal[mask]
                        qpos = q_legal[mask]
                        qpos = np.where(qpos > 0.0, qpos, eps)
                        kl = float(np.sum(ppos * np.log(ppos / qpos)))
                    else:
                        kl = 0.0

                    tv_multiscale = None
                    if counts_m1 is not None:
                        # Push forward m+1 histogram by truncating last bit: parent = w >> 1.
                        push_counts = counts_m1.reshape((1 << m), 2).sum(axis=1)
                        # TV(p_m, push(p_{m+1})) = (1/(2N)) * sum |counts - push_counts|.
                        tv_multiscale = (
                            0.5 * float(np.sum(np.abs((counts - push_counts)[legal]))) / float(N)
                        )

                    wr.writerow(
                        {
                            "model": "rotation_scan",
                            "alpha_name": cfg.alpha_name,
                            "alpha": f"{cfg.alpha:.16g}",
                            "partial_quotients_prefix": ",".join(str(x) for x in cfg.partial_quotients_prefix),
                            "beta": f"{cfg.beta:.16g}",
                            "x0": f"{cfg.x0:.16g}",
                            "m": m,
                            "N": N,
                            "tv": f"{tv:.12g}",
                            "kl": f"{kl:.12g}",
                            "unique_types": int(np.count_nonzero(counts_legal)),
                            "DN_star_upper_bound": f"{dn_star_ub_by_N[N]:.12g}",
                            "DN_star_exact": f"{dn_star_exact_by_N[N]:.12g}",
                            "tv_multiscale_residual": f"{tv_multiscale:.12g}" if tv_multiscale is not None else "",
                        }
                    )
                    prog.tick(f"done cfg={cfg.alpha_name} m={m} N={N} tv={tv:.4g} kl={kl:.4g}")

    dt_all = time.time() - t0_all
    print(f"[exp_rotation_fold_vs_parry] WROTE {out_csv} in {dt_all:.1f}s", flush=True)


if __name__ == "__main__":
    main()

