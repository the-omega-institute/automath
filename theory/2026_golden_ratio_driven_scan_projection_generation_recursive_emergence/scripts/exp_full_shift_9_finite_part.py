#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Abel/Mertens finite-part constants for the full 9-shift.

For the one-vertex full n-shift adjacency A=[n], we have:
  ζ(z) = 1/(1 - n z),  ρ=n,  z_* = 1/n,  C = 1.

Hence:
  log 𝔐 = Σ_{k>=2} μ(k)/k * log ζ(z_*^k)
        = - Σ_{k>=2} μ(k)/k * log(1 - n^{1-k}),
and the orbit-Mertens constant is 𝕄 = γ + log 𝔐.

Outputs (default):
  - artifacts/export/full_shift_9_finite_part.json
  - sections/generated/tab_full_shift_9_finite_part.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def mobius_upto(n: int) -> List[int]:
    mu = [0] * (n + 1)
    mu[0] = 0
    mu[1] = 1
    primes: List[int] = []
    is_comp = [False] * (n + 1)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def tail_bound_full_shift(n: int, k_max: int) -> float:
    # Uses |log(1-x)| <= x/(1-x) for x in (0,1).
    # Here x_k = n^{1-k}.
    s = 0.0
    for k in range(k_max + 1, k_max + 200000):
        x = n ** (1 - k)
        term = (1.0 / float(k)) * (x / (1.0 - x))
        s += term
        if term < 1e-220:
            break
    return s


@dataclass(frozen=True)
class FinitePart:
    n: int
    rho: float
    z_star: float
    C: float
    log_mathfrak_M: float
    mertens_M: float
    k_max: int
    tail_bound: float


def compute_finite_part(n: int, k_max: int, prog: Progress) -> FinitePart:
    mu = mobius_upto(k_max)
    s = 0.0
    for k in range(2, k_max + 1):
        if mu[k] == 0:
            continue
        x = n ** (1 - k)  # n^{1-k} in (0,1)
        term = -(mu[k] / float(k)) * math.log(1.0 - x)
        s += term
        prog.tick(f"k={k}/{k_max} term={term:.3e} partial={s:.12f}")

    log_mathfrak_M = s  # since C=1 for full shift
    gamma = 0.577215664901532860606512090082402431  # Euler–Mascheroni
    mertens_M = gamma + log_mathfrak_M
    tb = tail_bound_full_shift(n=n, k_max=k_max)

    return FinitePart(
        n=n,
        rho=float(n),
        z_star=1.0 / float(n),
        C=1.0,
        log_mathfrak_M=log_mathfrak_M,
        mertens_M=mertens_M,
        k_max=k_max,
        tail_bound=tb,
    )


def write_table_tex(path: Path, fp: FinitePart) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Abel/Mertens finite-part constants for the one-vertex full $9$-shift (adjacency $[9]$). "
        "Here $\\zeta(z)=1/(1-9z)$, $\\rho=9$, $z_\\star=1/\\rho$, "
        "$C=\\lim_{z\\to z_\\star}(1-\\rho z)\\zeta(z)=1$, "
        "$\\log\\mathfrak{M}=\\sum_{k\\ge2}\\mu(k)\\log\\zeta(z_\\star^k)/k$, and "
        "$\\mathsf{M}=\\gamma+\\log\\mathfrak{M}$.}"
    )
    lines.append("\\label{tab:full_shift_9_finite_part}")
    lines.append("\\begin{tabular}{r r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(f"$\\rho$ & {fp.rho:.12f}\\\\")
    lines.append(f"$z_\\star=1/\\rho$ & {fp.z_star:.12f}\\\\")
    lines.append(f"$C$ & {fp.C:.12f}\\\\")
    lines.append(f"$\\log\\mathfrak{{M}}$ & {fp.log_mathfrak_M:.15f}\\\\")
    lines.append(f"$\\mathsf{{M}}=\\gamma+\\log\\mathfrak{{M}}$ & {fp.mertens_M:.15f}\\\\")
    lines.append(f"$k_{{\\max}}$ & {fp.k_max}\\\\")
    lines.append(f"tail bound & {fp.tail_bound:.3e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Abel/Mertens finite-part for the full 9-shift.")
    parser.add_argument("--n", type=int, default=9, help="Full shift size n (adjacency [n]).")
    parser.add_argument("--k-max", type=int, default=250, help="Max k for Möbius tail sum.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "full_shift_9_finite_part.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_full_shift_9_finite_part.tex"),
        help="Output TeX table path.",
    )
    args = parser.parse_args()

    if args.n != 9:
        raise ValueError("This script is locked to n=9 to match the manuscript interface.")

    prog = Progress("full-shift-9-finite-part", every_seconds=20.0)
    fp = compute_finite_part(n=args.n, k_max=args.k_max, prog=prog)

    payload = {
        "n": fp.n,
        "rho": fp.rho,
        "z_star": fp.z_star,
        "C": fp.C,
        "log_mathfrak_M": fp.log_mathfrak_M,
        "mertens_M": fp.mertens_M,
        "k_max": fp.k_max,
        "tail_bound": fp.tail_bound,
    }
    json_path = Path(args.json_out)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    write_table_tex(Path(args.tex_out), fp=fp)
    prog.tick(f"Wrote {args.json_out} and {args.tex_out}")


if __name__ == "__main__":
    main()

