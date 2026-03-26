#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Exhaustive scan of the Fold_m multiplicity spectrum Fourier modes.

We work on G_m = Z / F_{m+2} Z with residue counts:
  d_m(r) = #{ omega in {0,1}^m : sum_{j=1}^m omega_j F_{j+1} ≡ r (mod F_{m+2}) }.

Define the (unnormalized) DFT:
  d_hat_m(k) = sum_{r in G_m} d_m(r) * exp(-2π i k r / F_{m+2}).

This script computes, for m in [m_min, m_max]:
  - S_m := max_{k != 0} |d_hat_m(k)| via a full FFT,
  - argmax mode(s) (reported by the top-K head),
  - the Fibonacci resonance candidates k = F_m and k = F_{m+1} (= -F_m mod F_{m+2}),
  - a_m(F_m) := |d_hat_m(F_m)| / 2^m,
  - a product-form audit a_m(F_m) = Π_{t=1}^m |cos(π F_t / F_{m+2})|,
  - a Parseval audit for the FFT implementation.

Outputs:
  - artifacts/export/fold_multiplicity_fourier_extremal_mode_scan.json
  - sections/generated/tab_fold_multiplicity_fourier_extremal_mode_scan.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import numpy as np

from common_mod_fib_dp import counts_mod_fib, fib_upto
from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress


def c_phi_partial(n_max: int = 80) -> float:
    """Compute C_phi ≈ Π_{n=2}^∞ |cos(π φ^{-n})| via a partial product."""
    if n_max < 2:
        raise ValueError("n_max must be >= 2")
    p = 1.0
    for n in range(2, n_max + 1):
        p *= abs(math.cos(math.pi * (PHI ** (-n))))
    return float(p)


def a_fib_product(m: int, mod: int) -> float:
    """Compute Π_{t=1}^m |cos(π F_t / mod)| with F_0=0,F_1=1 convention."""
    if m < 0:
        raise ValueError("m must be >= 0")
    if m == 0:
        return 1.0
    F = fib_upto(m)
    xs = np.array([F[t] for t in range(1, m + 1)], dtype=np.float64) / float(mod)
    return float(np.prod(np.abs(np.cos(math.pi * xs))))


@dataclass(frozen=True)
class Row:
    m: int
    mod: int
    k_argmax: int
    S_over_2m: float
    a_Fm_over_2m: float
    a_Fm_over_2m_prod: float
    rel_gap_to_Fm: float
    fib_argmax_ok: bool
    parseval_rel_err: float
    head_k: List[int]
    head_vals_over_2m: List[float]


def write_table_tex(path: Path, rows: List[Row], C_phi: float) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Exhaustive FFT scan of nontrivial Fold$_m$ multiplicity spectrum modes "
        "$S_m=\\max_{k\\neq 0}|\\widehat d_m(k)|$. "
        "We report the maximizing frequency $k_\\ast$ (one representative), the normalized "
        "amplitude $S_m/2^m$, and compare it to the Fibonacci resonance $|\\widehat d_m(F_m)|/2^m$. "
        f"The limiting constant is $C_\\varphi\\approx {C_phi:.15f}$.}}"
    )
    lines.append("\\label{tab:fold_multiplicity_fourier_extremal_mode_scan}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $F_{m+2}$ & $k_\\ast$ & $S_m/2^m$ & $|\\widehat d_m(F_m)|/2^m$ & rel gap\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.mod} & {r.k_argmax} & {r.S_over_2m:.12f} & {r.a_Fm_over_2m:.12f} & {r.rel_gap_to_Fm:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="FFT scan: extremal Fourier mode of Fold_m residue counts d_m(r).")
    parser.add_argument("--m-min", type=int, default=4)
    parser.add_argument("--m-max", type=int, default=29)
    parser.add_argument("--head", type=int, default=6, help="How many top-|d_hat| modes to record (excluding k=0).")
    parser.add_argument("--tol-rel", type=float, default=1e-12, help="Relative tolerance to consider two maxima equal.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_multiplicity_fourier_extremal_mode_scan.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_multiplicity_fourier_extremal_mode_scan.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 1 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 1")
    head = int(args.head)
    if head < 1:
        raise SystemExit("Require --head >= 1")
    tol_rel = float(args.tol_rel)
    if not (tol_rel > 0.0):
        raise SystemExit("Require --tol-rel > 0")

    C_phi = c_phi_partial(80)

    prog = Progress("fold-multiplicity-fourier-scan", every_seconds=20.0)
    rows: List[Row] = []

    for m in range(int(args.m_min), int(args.m_max) + 1):
        F = fib_upto(m + 2)
        mod = int(F[m + 2])
        k_fm = int(F[m])
        k_fm1 = int(F[m + 1])  # = mod - F[m]

        c = counts_mod_fib(m, prog=prog)
        if int(c.size) != mod:
            raise RuntimeError("counts_mod_fib returned unexpected modulus length")

        # FFT uses exp(-2π i k n / N), matching the paper's convention.
        hat = np.fft.fft(c.astype(np.float64, copy=False))
        abs_hat = np.abs(hat)

        # Parseval audit: sum_r d(r)^2 = (1/N) sum_k |d_hat(k)|^2.
        lhs = float(np.sum(c.astype(np.float64, copy=False) ** 2))
        rhs = float(np.sum(abs_hat * abs_hat)) / float(mod)
        parseval_rel_err = abs(lhs - rhs) / max(1e-300, lhs)

        abs_hat[0] = 0.0  # exclude trivial mode
        k_arg = int(np.argmax(abs_hat))
        S = float(abs_hat[k_arg])

        # Candidate amplitudes.
        a_fm = float(abs_hat[k_fm])
        a_fm1 = float(abs_hat[k_fm1])

        Z = float(2**m)
        S_over_2m = S / Z
        a_fm_over_2m = a_fm / Z

        # Product-form audit (independent of FFT).
        a_fm_over_2m_prod = a_fib_product(m=m, mod=mod)

        # Gap to Fibonacci candidate (relative to S).
        best_fib = max(a_fm, a_fm1)
        rel_gap = (S - best_fib) / max(1e-300, S)
        fib_ok = rel_gap <= tol_rel

        # Top-K head (exclude k=0, report small reps).
        # Use argpartition for O(N) selection; then sort the head.
        idx = np.argpartition(abs_hat, -head)[-head:]
        idx = idx[np.argsort(abs_hat[idx])[::-1]]
        head_k = [int(i) for i in idx.tolist()]
        head_vals = [float(abs_hat[i] / Z) for i in head_k]

        print(
            f"[fold-mult-fourier] m={m} mod={mod} "
            f"k*={k_arg} S/2^m={S_over_2m:.12f} "
            f"|hat(F_m)|/2^m={a_fm_over_2m:.12f} "
            f"gap={rel_gap:.3e} ok={fib_ok} parseval_rel_err={parseval_rel_err:.2e}",
            flush=True,
        )

        rows.append(
            Row(
                m=int(m),
                mod=int(mod),
                k_argmax=int(k_arg),
                S_over_2m=float(S_over_2m),
                a_Fm_over_2m=float(a_fm_over_2m),
                a_Fm_over_2m_prod=float(a_fm_over_2m_prod),
                rel_gap_to_Fm=float(rel_gap),
                fib_argmax_ok=bool(fib_ok),
                parseval_rel_err=float(parseval_rel_err),
                head_k=head_k,
                head_vals_over_2m=head_vals,
            )
        )

    # Deterministic order.
    rows.sort(key=lambda r: r.m)

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "m_min": int(args.m_min),
        "m_max": int(args.m_max),
        "head": head,
        "tol_rel": tol_rel,
        "C_phi_partial_80": C_phi,
        "rows": [asdict(r) for r in rows],
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-mult-fourier] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows, C_phi=C_phi)
    print(f"[fold-mult-fourier] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

