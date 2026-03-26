#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Write precomputed (audited) integer recurrences for S_k(m), k=18..23.

We record recurrences in the form:
  S(m) = sum_{i=1..d} c_i S(m-i),  valid for all m >= m0.

Outputs:
  - artifacts/export/fold_collision_moment_recursions_18_23.json
  - sections/generated/tab_fold_collision_moment_recursions_18_23.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import List

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


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{Verified integer recurrences for higher collision moments "
        "$S_k(m)=\\sum_x d_m(x)^k$ computed via modular DP on $\\mathbb{Z}/F_{m+2}\\mathbb{Z}$ "
        "(audit window $m\\le 35$). "
        "Coefficients are in the form $S(m)=\\sum_{i=1}^d c_i S(m-i)$.}"
    )
    lines.append("\\label{tab:fold_collision_moment_recursions_18_23}")
    lines.append("\\begin{tabular}{r r r p{0.72\\linewidth}}")
    lines.append("\\toprule")
    lines.append("$k$ & order $d$ & starts at $m\\ge$ & $(c_1,\\dots,c_d)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        coeffs = ", ".join(str(c) for c in r["coeffs"])
        lines.append(f"{int(r['k'])} & {int(r['order'])} & {int(r['m0'])} & ({coeffs})\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Write precomputed integer recurrences for S_k(m), k=18..23.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_recursions_18_23.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_recursions_18_23.tex"),
    )
    args = ap.parse_args()

    rows = [{"k": r.k, "order": len(r.coeffs), "m0": r.m0, "coeffs": r.coeffs} for r in RECS_18_23]

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"precomputed": True, "rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[moment-rec-18-23] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[moment-rec-18-23] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

