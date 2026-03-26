#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Summarize verified moment recurrences and their Perron roots r_k (k=18..23).

We take the exact integer recurrences for S_k(m)=sum_x d_m(x)^k in the form
  S(m) = sum_{i=1..d} c_i S(m-i),
and compute the dominant root r_k of the characteristic polynomial
  x^d - c_1 x^{d-1} - ... - c_d = 0.

We also report:
  - the (unnormalized) Renyi-q projection fingerprint rate: h_k = log(2^k / r_k),
  - the normalized Renyi rate: h_k^R = h_k / (k-1),
  - and r_k^{1/k}.

Outputs:
  - artifacts/export/fold_collision_moment_spectrum_k18_23.json
  - sections/generated/tab_fold_collision_moment_spectrum_k18_23.tex

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


# Precomputed, audited recurrences (audit window m<=35).
# Derived and exported by scripts/exp_fold_collision_moment_signature_q18_25.py.
RECS_18_23: List[Rec] = [
    Rec(
        k=18,
        m0=19,
        coeffs=[
            2,
            4196,
            253750,
            16841706,
            -359838840,
            -12680716224,
            -10092724500,
            -275807280985,
            -359838838,
            -45547388948,
            10093485750,
            -1371988544,
            719677692,
            2063568,
            -1015000,
            16,
            -16,
        ],
    ),
    Rec(
        k=19,
        m0=17,
        coeffs=[
            2,
            6782,
            510722,
            43115177,
            -1319512222,
            -57102085832,
            -103492425230,
            -3287973427007,
            70431413590,
            1820299893334,
            141396315958,
            1490826289911,
            -69111868602,
            75808868436,
            -37904434218,
        ],
    ),
    Rec(
        k=20,
        m0=19,
        coeffs=[
            2,
            10964,
            1026646,
            110369322,
            -4747929480,
            -252584574960,
            -930476920260,
            -34979269477849,
            -4747929478,
            -2366125043732,
            930480000198,
            -18550240640,
            9495858972,
            8300880,
            -4106584,
            16,
            -16,
        ],
    ),
    Rec(
        k=21,
        m0=17,
        coeffs=[
            2,
            17730,
            2061690,
            282555981,
            -16835263662,
            -1102832042704,
            -7541355704902,
            -337018569789879,
            -4580907037962,
            -178299513045558,
            19655380096446,
            491312623390091,
            4597742367158,
            24228053037540,
            -12114026518770,
        ],
    ),
    Rec(
        k=22,
        m0=19,
        coeffs=[
            2,
            28676,
            4136950,
            723669546,
            -58977801240,
            -4764905230944,
            -56923673862900,
            -3036610091030425,
            -58977801238,
            -123377166461588,
            56923686273750,
            -233016526784,
            117955602492,
            33325008,
            -16547800,
            16,
            -16,
        ],
    ),
    Rec(
        k=23,
        m0=19,
        coeffs=[
            2,
            46389,
            8295828,
            1854356343,
            -204594953196,
            -20423908865911,
            -406371384219676,
            -25926856168486983,
            4571341699730040,
            246398742959564703,
            33380612780988,
            1761279457237853,
            -8364467395452148,
            -214666561582310301,
            372990762880716,
            -7586660581874892,
            3793330290937446,
        ],
    ),
]


def dominant_root(coeffs: List[int], dps: int = 120) -> float:
    """Return dominant root of x^d - c1 x^{d-1} - ... - cd with high precision."""
    d = len(coeffs)
    x = sp.Symbol("x")
    poly = sp.Poly.from_list([1] + [-int(c) for c in coeffs], gens=x, domain=sp.ZZ).as_expr()
    roots = sp.nroots(poly, n=int(dps), maxsteps=500)
    roots_c = [complex(r) for r in roots]
    r = max(roots_c, key=lambda z: abs(z))
    if abs(r.imag) > 1e-12:
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
        "$S_k(m)=\\sum_x d_m(x)^k$ (Fold$_m$ fibers), $k=18,\\dots,23$. "
        "Here $r_k$ is the dominant root of the recurrence characteristic polynomial, "
        "$h_k=\\log(2^k/r_k)$ is the corresponding (unnormalized) R\\'enyi fingerprint rate, "
        "and $h_k^{\\mathrm R}=h_k/(k-1)$ is the normalized rate.}"
    )
    lines.append("\\label{tab:fold_collision_moment_spectrum_k18_23}")
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
    ap = argparse.ArgumentParser(description="Summarize r_k,h_k for k=18..23 from audited exact recurrences.")
    ap.add_argument("--dps", type=int, default=140, help="Precision for algebraic root extraction.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_spectrum_k18_23.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_spectrum_k18_23.tex"),
    )
    args = ap.parse_args()

    rows: List[dict] = []
    for rec in RECS_18_23:
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

