#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute the two-series Möbius compression of log M for the real-input-40 kernel.

We use z_* = phi^{-2} and C = (47+21*sqrt(5))/100.
Define
  logK0 := log C - z_* + 3 z_*^2 + 2 log(1-z_*) + 3 log(1+z_*),
and the two Möbius-log sums
  S3   := sum_{m>=2} mu(m)/m * log(1 - 3 q^m + q^{2m}),
  Spm  := sum_{m>=2} mu(m)/m * log(1 + q^m - q^{2m}),
with q=z_*.
Then log M = logK0 - (S3 + Spm).

This script computes high-precision approximations and a certified tail bound
from the inequality |tail(N)| <= 5 * sum_{m>N} q^m/m <= 5*q^{N+1}/((N+1)(1-q)).

Outputs:
  - artifacts/export/real_input_40_abel_mertens_two_series_split.json
  - sections/generated/tab_real_input_40_abel_mertens_two_series_split.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp

from common_paths import export_dir, generated_dir


def mobius(n: int) -> int:
    """Compute Möbius mu(n) via trial division; sufficient for n<=1e6 scale."""
    if n == 1:
        return 1
    x = n
    mu = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            mu = -mu
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p = 3 if p == 2 else p + 2
    if x > 1:
        mu = -mu
    return mu


def tail_bound(q: mp.mpf, N: int) -> mp.mpf:
    return (5 * q ** (N + 1)) / ((N + 1) * (1 - q))


@dataclass(frozen=True)
class Row:
    N: int
    logK0: str
    S3: str
    Spm: str
    logM: str
    tail_bound: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Two-series split for log M (real-input-40).")
    parser.add_argument("--N", type=int, default=120, help="Truncation N for m>=2 sums.")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision (decimal digits).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_abel_mertens_two_series_split.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_abel_mertens_two_series_split.tex"),
    )
    args = parser.parse_args()

    N = int(args.N)
    if N < 10:
        raise SystemExit("Require N>=10 for a meaningful split.")
    mp.mp.dps = int(args.dps)

    phi = (1 + mp.sqrt(5)) / 2
    q = phi ** (-2)  # z_*
    C = (mp.mpf(47) + mp.mpf(21) * mp.sqrt(5)) / 100
    logK0 = mp.log(C) - q + 3 * q**2 + 2 * mp.log(1 - q) + 3 * mp.log(1 + q)

    S3 = mp.mpf("0")
    Spm = mp.mpf("0")
    for m in range(2, N + 1):
        mu = mobius(m)
        if mu == 0:
            continue
        t = q**m
        S3 += mp.mpf(mu) * mp.log(1 - 3 * t + t * t) / m
        Spm += mp.mpf(mu) * mp.log(1 + t - t * t) / m
        if m % 25 == 0:
            print(f"[abel-two-series] m={m}/{N}", flush=True)

    logM = logK0 - (S3 + Spm)
    bound = tail_bound(q, N)

    row = Row(
        N=N,
        logK0=mp.nstr(logK0, 18),
        S3=mp.nstr(S3, 18),
        Spm=mp.nstr(Spm, 18),
        logM=mp.nstr(logM, 18),
        tail_bound=mp.nstr(bound, 6),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "N": N,
                "dps": int(args.dps),
                "phi": str(phi),
                "z_star": str(q),
                "C": str(C),
                "row": asdict(row),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[abel-two-series] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Two-series Möbius compression for the Abel finite-part constant "
        "$\\log\\mathfrak{M}$ of the real-input $40$-state kernel at $z_\\star=\\varphi^{-2}$. "
        "Here $\\log\\mathfrak{M}=\\log K_0-(S_3+S_{\\pm})$, truncated at $m\\le N$ with a certified tail bound "
        "$|\\mathrm{tail}(N)|\\le 5z_\\star^{N+1}/((N+1)(1-z_\\star))$.}"
    )
    lines.append("\\label{tab:real_input_40_abel_mertens_two_series_split}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$N$ & $\\log K_0$ & $S_3$ & $S_{\\pm}$ & $\\log\\mathfrak{M}$ & tail bd\\\\")
    lines.append("\\midrule")
    lines.append(
        f"{row.N} & {row.logK0} & {row.S3} & {row.Spm} & {row.logM} & {row.tail_bound}\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[abel-two-series] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

