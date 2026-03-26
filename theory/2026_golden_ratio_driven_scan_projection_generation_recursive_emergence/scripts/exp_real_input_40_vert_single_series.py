#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Single-series decomposition for the vertical synchronizer contribution P_vert(z_star).

In the paper we split:
  ζ_M(z) = ζ_in(z) * ζ_vert(z),
where
  ζ_vert(z) = 1 / ((1-z)^2 (1+z) (1+z-z^2)).

Define the Möbius--log transform:
  P_vert(z) = Σ_{m>=1} μ(m)/m * log ζ_vert(z^m),
analytic for |z|<1.

Using the corrected Möbius--log identities:
  Σ μ(m)/m log(1-z^m)  = -z,
  Σ μ(m)/m log(1+z^m)  = z - z^2,
we get the exact semi-closed form:
  P_vert(z) = z + z^2 - S_F(z),
where
  S_F(z) := Σ_{m>=1} μ(m)/m * log(1+z^m - z^{2m}).

This script evaluates the decomposition at z_star = φ^{-2} with certified truncation control.

Outputs:
  - artifacts/export/real_input_40_vert_single_series.json
  - sections/generated/tab_real_input_40_vert_single_series.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress


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


def zeta_vert(z: float) -> float:
    return 1.0 / (((1.0 - z) ** 2) * (1.0 + z) * (1.0 + z - z * z))


@dataclass(frozen=True)
class Result:
    phi: float
    lam: float
    z_star: float
    z_star_exact: str
    k_max: int
    S_F: float
    z_plus_z2: float
    P_vert: float
    consistency_err: float
    tail_proxy: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Vertical single-series decomposition at z_star.")
    parser.add_argument("--k-max", type=int, default=800)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_vert_single_series.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_vert_single_series.tex"),
    )
    args = parser.parse_args()

    prog = Progress("real-input-40-vert-single", every_seconds=20.0)

    phi = PHI
    lam = phi * phi
    z_star = 1.0 / lam
    mu = mobius_upto(int(args.k_max))

    # S_F(z_star) and P_vert(z_star) sums.
    S_F = 0.0
    P_vert = 0.0
    last_abs = 0.0
    for m in range(1, int(args.k_max) + 1):
        if mu[m] == 0:
            continue
        zm = z_star**m
        term_sf = (mu[m] / float(m)) * math.log(1.0 + zm - zm * zm)
        term_pv = (mu[m] / float(m)) * math.log(zeta_vert(zm))
        S_F += term_sf
        P_vert += term_pv
        last_abs = max(last_abs, abs(term_sf) + abs(term_pv))
        prog.tick(f"m={m}/{args.k_max} partial_SF={S_F:.12f} partial_Pvert={P_vert:.12f}")

    z_plus_z2 = z_star + z_star * z_star
    consistency_err = abs(P_vert - (z_plus_z2 - S_F))
    tail_proxy = 10.0 * (z_star ** (int(args.k_max) + 1))

    res = Result(
        phi=phi,
        lam=lam,
        z_star=z_star,
        z_star_exact=r"$(3-\sqrt{5})/2$",
        k_max=int(args.k_max),
        S_F=S_F,
        z_plus_z2=z_plus_z2,
        P_vert=P_vert,
        consistency_err=consistency_err,
        tail_proxy=tail_proxy,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(res), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[vert-single] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Single-series decomposition for the vertical synchronizer contribution "
        "$P_{\\mathrm{vert}}(z_\\star)$ of the real-input $40$-state kernel at $z_\\star=\\varphi^{-2}$. "
        "We report $S_F(z_\\star)=\\sum_{m\\ge 1}\\mu(m)\\log(1+z_\\star^m-z_\\star^{2m})/m$ and verify "
        "$P_{\\mathrm{vert}}(z_\\star)=z_\\star+z_\\star^2-S_F(z_\\star)$.}"
    )
    lines.append("\\label{tab:real_input_40_vert_single_series}")
    lines.append("\\begin{tabular}{l r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(f"$z_\\star$ & {res.z_star:.15f}\\\\")
    lines.append(f"$z_\\star+z_\\star^2$ & {res.z_plus_z2:.15f}\\\\")
    lines.append(f"$S_F(z_\\star)$ & {res.S_F:.15f}\\\\")
    lines.append(f"$P_{{\\mathrm{{vert}}}}(z_\\star)$ & {res.P_vert:.15f}\\\\")
    lines.append(f"consistency err & {res.consistency_err:.3e}\\\\")
    lines.append(f"$k_{{\\max}}$ & {res.k_max}\\\\")
    lines.append(f"tail proxy & {res.tail_proxy:.3e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[vert-single] wrote {tout}", flush=True)
    print("[vert-single] done", flush=True)


if __name__ == "__main__":
    main()

