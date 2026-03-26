#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Artin sign (twist -F) Mertens constant for the real-input 40-state kernel.

For the exact determinant split:
  det(I - z M) = (1-z)^2 (1+z)^3 (1-3z+z^2) (1+z-z^2),
the factor (1+z-z^2) equals det(I + z F), i.e. the -F block.

Define:
  λ = φ^2,  z_* = 1/λ,
  ζ_twist(z) = 1/(1+z-z^2).

Then the "Artin sign" finite-part constant (pure twist factor) is:
  K_{-F} := log ζ_twist(z_*) + Σ_{m>=2} μ(m)/m * log ζ_twist(z_*^m)
         = - Σ_{m>=1} μ(m)/m * log(1+z_*^m - z_*^{2m}).

This equals the split-table entry log 𝔐_twist.

Outputs (default):
  - artifacts/export/real_input_40_artin_sign_mertens.json
  - sections/generated/tab_real_input_40_artin_sign_mertens.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

import mpmath as mp

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress


def mobius_upto(n: int) -> list[int]:
    mu = [0] * (n + 1)
    mu[0] = 0
    mu[1] = 1
    primes: list[int] = []
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


def det_twist(z: mp.mpf) -> mp.mpf:
    # det(I + z F) = 1 + z - z^2
    return mp.mpf("1") + z - z * z


def zeta_twist(z: mp.mpf) -> mp.mpf:
    return mp.mpf("1") / det_twist(z)


@dataclass(frozen=True)
class ArtinSignMertens:
    lam: str
    z_star: str
    k_max: int
    K_minus_F: str
    tail_bound_proxy: str


def compute(k_max: int, mp_dps: int, prog: Progress) -> ArtinSignMertens:
    mp.mp.dps = mp_dps
    lam = mp.mpf(str(PHI)) * mp.mpf(str(PHI))
    z_star = mp.mpf("1") / lam

    mu = mobius_upto(k_max)
    s = mp.mpf("0")
    max_abs_term = mp.mpf("0")

    for m in range(1, k_max + 1):
        mmu = mu[m]
        if mmu == 0:
            continue
        zm = z_star**m
        term = mp.mpf(mmu) / mp.mpf(m) * mp.log(zeta_twist(zm))
        s += term
        if abs(term) > max_abs_term:
            max_abs_term = abs(term)
        prog.tick(f"m={m}/{k_max} partial={s}")

    # A crude tail proxy: z_star^(k_max+1) is tiny; log(1/(1-x)) ~ x.
    tail_proxy = mp.mpf("10") * (z_star ** (k_max + 1))
    return ArtinSignMertens(
        lam=str(lam),
        z_star=str(z_star),
        k_max=k_max,
        K_minus_F=str(s),
        tail_bound_proxy=str(tail_proxy),
    )


def write_table_tex(path: Path, res: ArtinSignMertens) -> None:
    lines: list[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Artin sign (twist $-F$) finite-part constant at the main pole $z_\\star=\\varphi^{-2}$. "
        "We define $\\zeta_{-F}(z)=(1+z-z^2)^{-1}$ and "
        "$K_{-F}:=\\sum_{m\\ge 1}\\mu(m)\\log\\zeta_{-F}(z_\\star^m)/m$.}"
    )
    lines.append("\\label{tab:real_input_40_artin_sign_mertens}")
    lines.append("\\begin{tabular}{l l}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(r"$\lambda=\varphi^2$ & $%s$\\\\" % res.lam)
    lines.append(r"$z_\star=1/\lambda$ & $%s$\\\\" % res.z_star)
    lines.append(r"$k_{\max}$ & $%d$\\\\" % res.k_max)
    lines.append(r"$K_{-F}$ & $%s$\\\\" % res.K_minus_F)
    lines.append(r"tail proxy & $%s$\\\\" % res.tail_bound_proxy)
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Artin sign Mertens constant K_{-F}.")
    parser.add_argument("--k-max", type=int, default=4000, help="Max m in Möbius sum.")
    parser.add_argument("--mp-dps", type=int, default=80, help="mpmath decimal precision.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_artin_sign_mertens.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_artin_sign_mertens.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("artin-sign-mertens", every_seconds=20.0)
    res = compute(k_max=int(args.k_max), mp_dps=int(args.mp_dps), prog=prog)

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(res.__dict__, indent=2), encoding="utf-8")
    print(f"[artin-sign-mertens] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), res)
    print(f"[artin-sign-mertens] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

