#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Endpoint-collapse audits for the golden-mean Parry chain (IID block sampling).

We sample IID length-m blocks from the stationary Parry Markov chain and compute:
  - endpoint mass matrix M_{ij}(m),
  - two overdetermined phi estimators from endpoint ratios,
  - fiber-flatness residues (span within each endpoint fiber),
  - the local "commuting square" residue at m=3: |pi(000)-pi(010)|.

Outputs:
  - artifacts/export/parry_endpoint_audit.json
  - sections/generated/tab_parry_endpoint_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress, fib_upto, parry_params


def _endpoints_from_packed(w: int, m: int) -> Tuple[int, int]:
    """Return (first_bit, last_bit) for an m-bit packed word."""
    if m <= 0:
        return (0, 0)
    return ((w >> (m - 1)) & 1, w & 1)


def _sample_parry_blocks(rng: np.random.Generator, m: int, n_blocks: int) -> np.ndarray:
    """Return packed int blocks of length m, IID blocks from stationary Parry chain."""
    _, pi0, pi1, p00, _ = parry_params()
    out = np.zeros(n_blocks, dtype=np.uint32)
    # First bit from stationary distribution.
    s = (rng.random(n_blocks) < pi1).astype(np.uint8)
    out = (out << 1) | s.astype(np.uint32)
    for _ in range(m - 1):
        u = rng.random(n_blocks)
        nxt = np.zeros(n_blocks, dtype=np.uint8)
        mask0 = s == 0
        if mask0.any():
            # 0->1 iff u >= p00 (since P(0->0)=p00, P(0->1)=1-p00).
            nxt[mask0] = (u[mask0] >= p00).astype(np.uint8)
        # from 1: always go to 0
        s = nxt
        out = (out << 1) | s.astype(np.uint32)
    return out


def _hist_packed(words: np.ndarray) -> Dict[int, int]:
    out: Dict[int, int] = {}
    for w in words.tolist():
        out[int(w)] = out.get(int(w), 0) + 1
    return out


def _endpoint_metrics_from_hist(hist: Dict[int, int], m: int, N: int) -> Dict[str, float]:
    """Compute endpoint masses and residues from a histogram over X_m."""
    # Fibonacci fiber sizes for golden-mean A^{m-1}.
    fib = fib_upto(max(3, m))
    Fm = float(fib[m - 1]) if m >= 1 else 1.0
    Fm1 = float(fib[m - 2]) if m >= 2 else 1.0
    Fm2 = float(fib[m - 3]) if m >= 3 else 1.0

    # Endpoint masses and observed spans.
    M = {(0, 0): 0.0, (0, 1): 0.0, (1, 0): 0.0, (1, 1): 0.0}
    maxp = {(0, 0): 0.0, (0, 1): 0.0, (1, 0): 0.0, (1, 1): 0.0}
    minp_obs = {(0, 0): 1.0, (0, 1): 1.0, (1, 0): 1.0, (1, 1): 1.0}
    seen = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}

    invN = 1.0 / float(N) if N > 0 else 0.0
    for w, c in hist.items():
        i, j = _endpoints_from_packed(w, m)
        p = float(c) * invN
        M[(i, j)] += p
        maxp[(i, j)] = max(maxp[(i, j)], p)
        minp_obs[(i, j)] = min(minp_obs[(i, j)], p)
        seen[(i, j)] += 1

    # Fiber sizes (counts of legal words with endpoints).
    # Using standard identity: A^{m-1} = [[F_m, F_{m-1}], [F_{m-1}, F_{m-2}]] for m>=2.
    fiber_size = {
        (0, 0): int(Fm) if m >= 2 else 1,
        (0, 1): int(Fm1) if m >= 2 else 0,
        (1, 0): int(Fm1) if m >= 2 else 0,
        (1, 1): int(Fm2) if m >= 3 else 0,
    }

    # Span residue within each endpoint fiber, with the convention that unseen words have prob 0.
    span = {}
    for key in [(0, 0), (0, 1), (1, 0), (1, 1)]:
        if fiber_size[key] <= 0:
            span[key] = 0.0
            continue
        mn = 0.0 if seen[key] < fiber_size[key] else float(minp_obs[key])
        span[key] = float(maxp[key] - mn)

    # Overdetermined phi estimators from endpoint ratios (only meaningful for m>=3).
    def safe_div(a: float, b: float) -> float:
        return a / b if b > 0 else float("nan")

    phi_hat_00_01 = float("nan")
    phi_hat_01_11 = float("nan")
    if m >= 3:
        phi_hat_00_01 = safe_div(M[(0, 0)], M[(0, 1)]) * (Fm1 / Fm) if Fm > 0 else float("nan")
        phi_hat_01_11 = safe_div(M[(0, 1)], M[(1, 1)]) * (Fm2 / Fm1) if Fm1 > 0 else float("nan")

    return {
        "M00": M[(0, 0)],
        "M01": M[(0, 1)],
        "M10": M[(1, 0)],
        "M11": M[(1, 1)],
        "phi_hat_00_01": phi_hat_00_01,
        "phi_hat_01_11": phi_hat_01_11,
        "span00": span[(0, 0)],
        "span01": span[(0, 1)],
        "span10": span[(1, 0)],
        "span11": span[(1, 1)],
        "span_max": max(span.values()) if span else 0.0,
    }


def _square_move_residue(rng: np.random.Generator, N: int) -> float:
    """Return |p_hat(000)-p_hat(010)| under IID sampling of length-3 Parry blocks."""
    words = _sample_parry_blocks(rng, m=3, n_blocks=N)
    hist = _hist_packed(words)
    p000 = float(hist.get(0b000, 0)) / float(N)
    p010 = float(hist.get(0b010, 0)) / float(N)
    return abs(p000 - p010)


@dataclass(frozen=True)
class Row:
    m: int
    N: int
    seed: int
    phi_hat_00_01: float
    phi_hat_01_11: float
    phi_hat_mean: float
    phi_hat_std: float
    span_max: float
    square_residue_m3: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Endpoint-collapse audits for Parry chain (IID blocks).")
    parser.add_argument("--ms", type=str, default="6,8,10,12,14", help="Comma-separated m grid.")
    parser.add_argument("--Ns", type=str, default="2000,10000,100000", help="Comma-separated N grid.")
    parser.add_argument("--seeds", type=str, default="1,2,3,4,5", help="Comma-separated seeds.")
    parser.add_argument("--json-out", type=str, default=str(export_dir() / "parry_endpoint_audit.json"))
    parser.add_argument("--tex-out", type=str, default=str(generated_dir() / "tab_parry_endpoint_audit.tex"))
    args = parser.parse_args()

    ms = [int(x.strip()) for x in str(args.ms).split(",") if x.strip()]
    Ns = [int(x.strip()) for x in str(args.Ns).split(",") if x.strip()]
    seeds = [int(x.strip()) for x in str(args.seeds).split(",") if x.strip()]
    if any(m < 3 for m in ms):
        raise SystemExit("Require m>=3 for endpoint audits (uses F_{m-2} and M11).")
    if any(N <= 0 for N in Ns):
        raise SystemExit("Require N>0.")

    prog = Progress("parry-endpoint-audit", every_seconds=20.0)
    t0 = time.time()

    rows: List[Row] = []
    payload_rows: List[dict] = []

    for m in ms:
        for N in Ns:
            phi_hats_00_01: List[float] = []
            phi_hats_01_11: List[float] = []
            spans: List[float] = []
            squares: List[float] = []
            for seed in seeds:
                rng = np.random.default_rng(seed)
                words = _sample_parry_blocks(rng, m=m, n_blocks=N)
                hist = _hist_packed(words)
                metrics = _endpoint_metrics_from_hist(hist, m=m, N=N)
                phi_hats_00_01.append(float(metrics["phi_hat_00_01"]))
                phi_hats_01_11.append(float(metrics["phi_hat_01_11"]))
                spans.append(float(metrics["span_max"]))
                squares.append(float(_square_move_residue(rng, N=N)))
                prog.tick(f"m={m} N={N} seed={seed}")

            # Summaries across seeds (overdetermined checks).
            phi_hats_all = [x for x in (phi_hats_00_01 + phi_hats_01_11) if math.isfinite(x)]
            phi_mean = float(statistics.fmean(phi_hats_all)) if phi_hats_all else float("nan")
            phi_std = float(statistics.pstdev(phi_hats_all)) if len(phi_hats_all) >= 2 else 0.0

            rows.append(
                Row(
                    m=m,
                    N=N,
                    seed=-1,
                    phi_hat_00_01=float(statistics.fmean(phi_hats_00_01)),
                    phi_hat_01_11=float(statistics.fmean(phi_hats_01_11)),
                    phi_hat_mean=phi_mean,
                    phi_hat_std=phi_std,
                    span_max=float(statistics.fmean(spans)),
                    square_residue_m3=float(statistics.fmean(squares)),
                )
            )
            payload_rows.append(
                {
                    "m": m,
                    "N": N,
                    "seeds": seeds,
                    "phi_hat_00_01": phi_hats_00_01,
                    "phi_hat_01_11": phi_hats_01_11,
                    "span_max": spans,
                    "square_residue_m3": squares,
                    "phi_hat_mean": phi_mean,
                    "phi_hat_std": phi_std,
                }
            )

    # Export JSON.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "phi": PHI,
                "ms": ms,
                "Ns": Ns,
                "seeds": seeds,
                "rows": payload_rows,
                "wall_time_seconds": time.time() - t0,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # Write TeX table.
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_parry_endpoint_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append("\\begin{tabular}{rrrrrr}")
    lines.append("\\toprule")
    lines.append("$m$ & $N$ & $\\widehat\\varphi_{00/01}$ & $\\widehat\\varphi_{01/11}$ & span$_{\\max}$ & $|\\hat\\pi_3(000)-\\hat\\pi_3(010)|$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.N} & {r.phi_hat_00_01:.6g} & {r.phi_hat_01_11:.6g} & {r.span_max:.3g} & {r.square_residue_m3:.3g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{Endpoint-collapse audits under IID block sampling from the stationary golden-mean Parry chain. "
        "The two endpoint-based estimators $\\widehat\\varphi_{00/01}(m)$ and $\\widehat\\varphi_{01/11}(m)$ "
        "should agree and stabilize to $\\varphi$; span$_{\\max}$ is the maximum within-fiber probability span "
        "over endpoint classes (with unseen words treated as probability $0$); the last column is the local "
        "commuting-square residue at length $3$.}"
    )
    lines.append("\\label{tab:parry_endpoint_audit}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"[parry-endpoint-audit] wrote {jout}", flush=True)
    print(f"[parry-endpoint-audit] wrote {tout}", flush=True)
    print("[parry-endpoint-audit] done", flush=True)


if __name__ == "__main__":
    main()

