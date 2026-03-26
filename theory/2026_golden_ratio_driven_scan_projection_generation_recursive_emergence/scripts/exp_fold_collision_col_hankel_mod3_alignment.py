#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Align Fold collision (Col_m) with Hankel resonance certificates, marking mod-3 beat points.

We work with Fold_m fiber multiplicities d_m(x)=|Fold_m^{-1}(x)| and define:
  S_q(m) = sum_x d_m(x)^q.

The collision probability for the Fold output distribution pi_m(x)=d_m(x)/2^m is:
  Col_m := sum_x pi_m(x)^2 = S_2(m) / 2^{2m}.
We plot the scaled collision constant proxy:
  F_{m+2} * Col_m.

For a resonance order q in [9..17], the paper reports:
  - nominal dimension: n = 2*floor(q/2)+1,
  - audited minimal recurrence / Hankel rank: d_q < n.
We form a sliding n x n Hankel block from a_n := S_q(n+2) (equivalently from S_q(m)),
and track its rank over two finite fields as a robust lower bound on the rational rank.

We then align:
  - F_{m+2} * Col_m versus m
  - Hankel deficiency (n - rank) versus m
on the same m-axis, and highlight the arithmetic beat points m+2 ≡ 0 (mod 3).

Outputs (default):
  - artifacts/export/fold_collision_col_hankel_mod3_alignment_q9.json
  - artifacts/export/fold_collision_col_hankel_mod3_alignment_q9.png
  - sections/generated/fig_fold_collision_col_hankel_mod3_alignment_q9.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17, counts_mod_fib, moments_from_counts


def fib_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F[: n + 1]


def _find_precomputed_rec(q: int) -> Tuple[int, int, List[int]]:
    """Return (order d_q, start m0, coeffs) for q in PRECOMPUTED_RECS_9_17."""
    for r in PRECOMPUTED_RECS_9_17:
        if int(r["k"]) == int(q):
            coeffs = [int(c) for c in r["coeffs"]]
            return int(r["order"]), int(r["m0"]), coeffs
    raise KeyError(f"Missing precomputed recurrence for q={q}")


def _extend_by_recurrence(seed: Dict[int, int], coeffs: List[int], m0: int, m_max: int) -> List[int]:
    """Extend a sequence by an exact integer recurrence for m>=m0."""
    d = len(coeffs)
    if m_max < 0:
        raise ValueError("m_max must be >= 0")
    out: List[int] = [0] * (m_max + 1)
    for m, v in seed.items():
        if 0 <= m <= m_max:
            out[m] = int(v)
    # Fill forward from m0 using the recurrence.
    for m in range(m0, m_max + 1):
        s = 0
        for i, c in enumerate(coeffs, start=1):
            s += int(c) * int(out[m - i])
        out[m] = int(s)
    # Basic sanity: require all seeds to be preserved up to m0-1.
    for m, v in seed.items():
        if 0 <= m <= min(m0 - 1, m_max) and int(out[m]) != int(v):
            raise RuntimeError(f"Seed mismatch at m={m}: got={out[m]} want={v}")
    # Also require we had enough seeds to start the recurrence.
    for m in range(m0 - d, m0):
        if m < 0:
            continue
        if m not in seed:
            raise RuntimeError(f"Missing seed value at m={m} needed for recurrence start m0={m0}, d={d}")
    return out


def _rank_mod_p(A: List[List[int]], p: int) -> int:
    """Compute matrix rank over F_p by Gauss elimination (in-place copy)."""
    if p <= 2:
        raise ValueError("p must be an odd prime")
    if not A:
        return 0
    m = len(A)
    n = len(A[0])
    M = [[int(x) % p for x in row] for row in A]
    r = 0
    for c in range(n):
        # Find pivot row.
        piv = None
        for i in range(r, m):
            if M[i][c] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            M[r], M[piv] = M[piv], M[r]
        inv = pow(int(M[r][c]), -1, p)
        # Normalize pivot row.
        for j in range(c, n):
            M[r][j] = (M[r][j] * inv) % p
        # Eliminate in all other rows.
        for i in range(m):
            if i == r:
                continue
            f = M[i][c] % p
            if f == 0:
                continue
            for j in range(c, n):
                M[i][j] = (M[i][j] - f * M[r][j]) % p
        r += 1
        if r == m:
            break
    return int(r)


def _log10_abs_int(x: int) -> float:
    """Return log10(|x|) for large integers without float overflow."""
    x = abs(int(x))
    if x == 0:
        return float("-inf")
    b = x.bit_length()
    # Keep top ~52 bits for a stable mantissa.
    keep = 52
    if b <= keep:
        return math.log10(float(x))
    shift = b - keep
    mant = x >> shift
    return float(shift) * math.log10(2.0) + math.log10(float(mant))


@dataclass(frozen=True)
class Row:
    m: int
    beat_mod3: bool
    scaled_collision: float
    hankel_rank_lb: int
    hankel_deficiency_lb: int
    hankel_minor_log10abs_det: float


def _write_fig_tex(path: Path, png_rel: str, caption: str, label: str) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n",
        encoding="utf-8",
    )


def main() -> None:
    ap = argparse.ArgumentParser(description="Align Fold collision vs Hankel resonance (mod-3 beat markers).")
    ap.add_argument("--q", type=int, default=9, help="Resonance order q in [9..17].")
    ap.add_argument("--m-max", type=int, default=32, help="Max m to plot (audit window upper end).")
    ap.add_argument("--m-min", type=int, default=2, help="Min m to consider (>=2).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_col_hankel_mod3_alignment_q9.json"),
    )
    ap.add_argument(
        "--png-out",
        type=str,
        default=str(export_dir() / "fold_collision_col_hankel_mod3_alignment_q9.png"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "fig_fold_collision_col_hankel_mod3_alignment_q9.tex"),
    )
    args = ap.parse_args()

    q = int(args.q)
    if q < 9 or q > 17:
        raise SystemExit("Require --q in [9..17] (uses audited precomputed recurrences).")

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    if m_min < 2 or m_max < m_min:
        raise SystemExit("Require m_max >= m_min >= 2")

    # Hankel nominal size n = 2*floor(q/2)+1, and d_q from audited recurrence order.
    h = q // 2
    n = 2 * h + 1
    d_q, m0_q, coeffs_q = _find_precomputed_rec(q)
    # Expected resonance gap (nominal - d_q).
    delta_q = int(n - d_q)
    if delta_q < 0:
        raise SystemExit(f"Invalid resonance gap: nominal={n} < d_q={d_q}")

    # Sliding n x n Hankel block uses S_q values on a window of length (2n-1).
    win_span = 2 * n - 2  # start..end inclusive has length 2n-1
    m_plot_min = max(m_min, 2 + win_span)  # ensure the window start is >=2
    if m_plot_min > m_max:
        raise SystemExit(
            f"Need m_max >= {m_plot_min} for q={q} (nominal n={n}) to form a Hankel window within m>=2."
        )

    # Seed moments by modular DP only up to m0_q-1 and for S2 seeds.
    m_seed_max = max(m0_q - 1, 2)  # include small m for S2 seeds

    prog = Progress("col-hankel-align", every_seconds=20.0)
    seeds: Dict[int, Dict[int, int]] = {2: {}, q: {}}
    for m in range(0, m_seed_max + 1):
        c = counts_mod_fib(m, prog=prog)
        moms = moments_from_counts(c, k_max=max(q, 2))
        seeds[2][m] = int(moms[2])
        seeds[q][m] = int(moms[q])

    # Exact recurrences:
    # S2(m) recurrence from the audited A2 kernel: order 3, valid from m>=3.
    coeffs_2 = [2, 2, -2]
    m0_2 = 3
    S2 = _extend_by_recurrence(seeds[2], coeffs_2, m0=m0_2, m_max=m_max)
    Sq = _extend_by_recurrence(seeds[q], coeffs_q, m0=m0_q, m_max=m_max)

    # Precompute Fibonacci numbers for F_{m+2}.
    F = fib_upto(m_max + 2)

    # Two primes for modular rank lower bounds.
    primes = [2147483647, 2305843009213693951]  # 2^31-1, 2^61-1

    rows: List[Row] = []
    for m_end in range(m_plot_min, m_max + 1):
        beat = ((m_end + 2) % 3) == 0
        scaled_col = float(F[m_end + 2]) * float(S2[m_end]) / float(1 << (2 * m_end))

        m0 = m_end - win_span
        # Build the nominal n x n Hankel block from S_q(m).
        H = [[int(Sq[m0 + i + j]) for j in range(n)] for i in range(n)]
        rk_lb = max(_rank_mod_p(H, p) for p in primes)
        def_lb = int(n - rk_lb)

        # Conditioning proxy: log10|det| of a fixed d_q x d_q Hankel minor.
        # (We use the top-left minor; this is not optimized for maximal magnitude.)
        Hd = [[int(Sq[m0 + i + j]) for j in range(d_q)] for i in range(d_q)]
        det = int(sp.Matrix(Hd).det())
        logdet = float(_log10_abs_int(det))

        rows.append(
            Row(
                m=int(m_end),
                beat_mod3=bool(beat),
                scaled_collision=float(scaled_col),
                hankel_rank_lb=int(rk_lb),
                hankel_deficiency_lb=int(def_lb),
                hankel_minor_log10abs_det=float(logdet),
            )
        )

    # Write JSON export.
    payload = {
        "q": q,
        "nominal_n": n,
        "d_q_audited": d_q,
        "delta_q_expected": delta_q,
        "m0_q": m0_q,
        "coeffs_q": coeffs_q,
        "m_min_plot": m_plot_min,
        "m_max_plot": m_max,
        "rows": [asdict(r) for r in rows],
        "rank_primes": primes,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[col-hankel-align] wrote {jout}", flush=True)

    # Plot.
    ms = [r.m for r in rows]
    cols = [r.scaled_collision for r in rows]
    logdets = [r.hankel_minor_log10abs_det for r in rows]
    beats_m = [r.m for r in rows if r.beat_mod3]
    beats_col = [r.scaled_collision for r in rows if r.beat_mod3]
    beats_logdet = [r.hankel_minor_log10abs_det for r in rows if r.beat_mod3]

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(9.2, 6.4), sharex=True)

    ax1.plot(ms, cols, lw=1.8, color="#1f77b4")
    if beats_m:
        ax1.scatter(beats_m, beats_col, s=26, color="#d62728", zorder=3, label=r"$m+2\equiv 0\ (\mathrm{mod}\ 3)$")
    ax1.axhline(1.0, lw=1.0, color="black", alpha=0.25, linestyle="--")
    ax1.set_ylabel(r"$F_{m+2}\,\mathrm{Col}_m$")
    ax1.set_title(f"Fold collision vs Hankel resonance (q={q}), mod-3 beat markers")
    if beats_m:
        ax1.legend(loc="upper right", fontsize=9, frameon=False)

    ax2.plot(ms, logdets, lw=1.8, color="#2ca02c")
    if beats_m:
        ax2.scatter(beats_m, beats_logdet, s=26, color="#d62728", zorder=3)
    ax2.set_ylabel(r"$\log_{10}|\det(H_{d_q})|$ (Hankel minor)")
    ax2.set_xlabel(r"$m$ (right end of Hankel window)")

    fig.tight_layout()
    png = Path(args.png_out)
    png.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(png, dpi=180)
    plt.close(fig)
    print(f"[col-hankel-align] wrote {png}", flush=True)

    # Write TeX wrapper for paper inclusion.
    _write_fig_tex(
        path=Path(args.tex_out),
        png_rel=str(Path("artifacts/export") / Path(args.png_out).name),
        caption=(
            rf"对齐审计窗口内的碰撞常数代理 $F_{{m+2}}\mathrm{{Col}}_m$（上图）与共振区 $q={q}$ 的 Hankel 缺口下界（下图；$n=2\lfloor q/2\rfloor+1$）。"
            rf"下图绘制固定的 $d_q\times d_q$ Hankel 子式 $H_{{d_q}}$（$d_q$ 为已核验最小递推阶数）的 $\log_{{10}}|\det(H_{{d_q}})|$，作为“接近额外线性相关/条件数劣化”的一个可审计代理。"
            rf"红点标出算术节拍 $m+2\equiv 0\ (\mathrm{{mod}}\ 3)$（等价于 $F_{{m+2}}$ 为偶数，从而存在严格 Fourier 零点；见附录~\ref{{app:fold-multiplicity}}）。"
        ),
        label=f"fig:fold_collision_col_hankel_mod3_alignment_q{q}",
    )
    print(f"[col-hankel-align] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()