#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Summarize verified moment recurrences and their Perron roots r_k (k=2..8).

We take the exact integer recurrences for S_k(m)=sum_x d_m(x)^k in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
and compute the dominant root r_k of the characteristic polynomial
  x^d - c_1 x^{d-1} - ... - c_d = 0.
Then the (unnormalized) Renyi-q projection entropy rate is
  h_k = log(2^k / r_k).
The normalized (standard) Renyi rate is
  h_k^R = h_k / (k-1).

Outputs:
  - artifacts/export/fold_collision_moment_spectrum_k2_8.json
  - sections/generated/tab_fold_collision_moment_spectrum_k2_8.tex

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
from common_phi_fold import PHI


@dataclass(frozen=True)
class Rec:
    k: int
    coeffs: List[int]  # S(m)=sum_{i=1..d} coeffs[i-1]*S(m-i)
    m0: int


RECS: List[Rec] = [
    Rec(k=2, coeffs=[2, 2, -2], m0=3),
    Rec(k=3, coeffs=[2, 4, -2], m0=3),
    Rec(k=4, coeffs=[2, 7, 0, 2, -2], m0=5),
    Rec(k=5, coeffs=[2, 11, 8, 20, -10], m0=5),
    Rec(k=6, coeffs=[2, 17, 28, 88, -26, 4, -4], m0=7),
    Rec(k=7, coeffs=[2, 26, 74, 311, -34, 84, -42], m0=7),
    Rec(k=8, coeffs=[2, 40, 174, 969, 2, 428, -174, 4, -4], m0=9),
]


def dominant_root(coeffs: List[int], dps: int = 80) -> float:
    """Return dominant root of x^d - c1 x^{d-1} - ... - cd with high precision."""
    d = len(coeffs)
    x = sp.Symbol("x")
    poly = x**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * x ** (d - i)
    # SymPy nroots uses `n` for decimal digits of precision (API varies by version).
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
        "$S_k(m)=\\sum_x d_m(x)^k$ (Fold$_m$ fibers), $k=2,\\dots,8$. "
        "Here $r_k$ is the dominant root of the recurrence characteristic polynomial, "
        "and $h_k=\\log(2^k/r_k)$ is the corresponding (unnormalized) R\\'enyi fingerprint rate. "
        "We also report the normalized rate $h_k^{\\mathrm R}=h_k/(k-1)$ "
        "and its endpoint gap $h_k^{\\mathrm R}-\\log(2/\\sqrt{\\varphi})$.}"
    )
    lines.append("\\label{tab:fold_collision_moment_spectrum_k2_8}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$k$ & order $d$ & starts at $m\\ge$ & $r_k$ & $h_k$ & $h_k^{\\mathrm R}$ & gap\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['k']} & {r['order']} & {r['m0']} & {r['r_k']:.12f} & {r['h_k']:.12f} & {r['h_k_R']:.12f} & {r['gap_to_endpoint']:.12f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Summarize r_k,h_k for k=2..8 from exact recurrences.")
    parser.add_argument("--dps", type=int, default=80, help="Precision for algebraic root extraction.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_spectrum_k2_8.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_spectrum_k2_8.tex"),
    )
    args = parser.parse_args()

    endpoint = math.log(2.0 / math.sqrt(PHI))
    rows: List[dict] = []
    for rec in RECS:
        rk = dominant_root(rec.coeffs, dps=int(args.dps))
        hk = math.log((2.0**rec.k) / rk)
        hkR = hk / (rec.k - 1)
        gap = hkR - endpoint
        rows.append(
            {
                "k": rec.k,
                "order": len(rec.coeffs),
                "m0": rec.m0,
                "coeffs": rec.coeffs,
                "r_k": rk,
                "h_k": hk,
                "h_k_R": hkR,
                "endpoint": endpoint,
                "gap_to_endpoint": gap,
            }
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps({"endpoint": endpoint, "rows": rows}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"[moment-spectrum] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[moment-spectrum] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

