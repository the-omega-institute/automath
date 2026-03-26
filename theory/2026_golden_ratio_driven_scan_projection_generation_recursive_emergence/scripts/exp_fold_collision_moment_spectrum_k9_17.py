#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Summarize verified moment recurrences and their Perron roots r_k (k=9..17).

We take the exact integer recurrences for S_k(m)=sum_x d_m(x)^k in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
and compute the dominant root r_k of the characteristic polynomial
  x^d - c_1 x^{d-1} - ... - c_d = 0.

We also report:
  - the (unnormalized) Renyi-q projection fingerprint rate: h_k = log(2^k / r_k),
  - the normalized Renyi rate: h_k^R = h_k / (k-1),
  - and r_k^{1/k}, which converges to sqrt(phi) as k->infty.

Outputs:
  - artifacts/export/fold_collision_moment_spectrum_k9_17.json
  - sections/generated/tab_fold_collision_moment_spectrum_k9_17.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Rec:
    k: int
    coeffs: List[int]  # S(m)=sum_{i=1..d} coeffs[i-1]*S(m-i)
    m0: int


# Precomputed, audited recurrences (see exp_fold_collision_moment_recursions_mod_dp.py --precomputed).
RECS_9_17: List[Rec] = [
    Rec(k=9, m0=9, coeffs=[2, 62, 386, 2819, 62, 900, -450]),
    Rec(k=10, m0=11, coeffs=[2, 96, 830, 7945, 2, 1852, -830, 4, -4]),
    Rec(k=11, m0=11, coeffs=[2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174]),
    Rec(k=12, m0=15, coeffs=[2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8]),
    Rec(k=13, m0=13, coeffs=[2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690]),
    Rec(k=14, m0=15, coeffs=[2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8]),
    Rec(k=15, m0=13, coeffs=[2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538]),
    Rec(k=16, m0=15, coeffs=[2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8]),
    Rec(
        k=17,
        m0=15,
        coeffs=[
            2,
            2599,
            125872,
            6569850,
            -96034590,
            -2764163954,
            -643026032,
            -15022392733,
            769974566,
            15329386299,
            642908352,
            1347896340,
            -673948170,
        ],
    ),
]


def dominant_root(coeffs: List[int], dps: int = 80) -> float:
    """Return dominant root of x^d - c1 x^{d-1} - ... - cd with high precision."""
    d = len(coeffs)
    x = sp.Symbol("x")
    poly = x**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * x ** (d - i)
    roots = sp.nroots(poly, n=int(dps), maxsteps=200)
    roots_c = [complex(sp.re(r).evalf(dps), sp.im(r).evalf(dps)) for r in roots]
    r = max(roots_c, key=lambda z: abs(z))
    if abs(r.imag) > 1e-20:
        raise RuntimeError(f"dominant root is not (numerically) real: {r}")
    rr = float(r.real)
    if rr <= 0:
        raise RuntimeError(f"dominant root is not positive: {rr}")
    return rr


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Exact recurrences and Perron roots for collision moments "
        "$S_k(m)=\\sum_x d_m(x)^k$ (Fold$_m$ fibers), $k=9,\\dots,17$. "
        "Here $r_k$ is the dominant root of the recurrence characteristic polynomial, "
        "$h_k=\\log(2^k/r_k)$ is the corresponding (unnormalized) R\\'enyi fingerprint rate, "
        "and $h_k^{\\mathrm R}=h_k/(k-1)$ is the normalized rate.}"
    )
    lines.append("\\label{tab:fold_collision_moment_spectrum_k9_17}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append("$k$ & order $d$ & starts at $m\\ge$ & $r_k$ & $r_k^{1/k}$ & $h_k$ & $h_k^{\\mathrm R}$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['k']} & {r['order']} & {r['m0']} & {r['r_k']:.12f} & {r['r_k_1k']:.12f} "
            f"& {r['h_k']:.12f} & {r['h_k_R']:.12f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Summarize r_k,h_k for k=9..17 from audited exact recurrences.")
    parser.add_argument("--dps", type=int, default=100, help="Precision for algebraic root extraction.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_spectrum_k9_17.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_spectrum_k9_17.tex"),
    )
    args = parser.parse_args()

    rows: List[dict] = []
    for rec in RECS_9_17:
        rk = dominant_root(rec.coeffs, dps=int(args.dps))
        hk = math.log((2.0**rec.k) / rk)
        hkR = hk / (rec.k - 1)
        rows.append(
            {
                "k": rec.k,
                "order": len(rec.coeffs),
                "m0": rec.m0,
                "coeffs": rec.coeffs,
                "r_k": rk,
                "r_k_1k": rk ** (1.0 / rec.k),
                "h_k": hk,
                "h_k_R": hkR,
            }
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[moment-spectrum] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[moment-spectrum] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

