#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Singular value spectrum of the folding conditional expectation E_m.

We use the modular DP counts c_m(r) (subset-sum counts mod F_{m+2}),
which coincide with the folding fiber multiplicities d_m(x) under the paper's identification.

For the uniform fiber-average operator
    (E_m f)(x) = (1/d_m(x)) * sum_{Fold_m(a)=x} f(a),
viewed as a linear map l^2(Omega_m) -> l^2(X_m) with counting inner products,
the singular values are exactly:
    sigma_x(E_m) = d_m(x)^(-1/2).

Hence Schatten p-quasi-moments are negative moments of d_m:
    ||E_m||_{S_p}^p = sum_x d_m(x)^(-p/2).

Outputs:
  - artifacts/export/fold_conditional_expectation_singular_spectrum.json
  - sections/generated/tab_fold_conditional_expectation_singular_spectrum.tex

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

from common_mod_fib_dp import hist_from_counts
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_fold_collision_moment_recursions_mod_dp import counts_mod_fib


@dataclass(frozen=True)
class Row:
    m: int
    mod: int
    d_min: int
    d_max: int
    hs2: float
    s1: float
    s2: float
    s4: float
    op: float
    S2: int


def _schatten_p_sums(c: np.ndarray, p: float) -> float:
    # sum_x d(x)^(-p/2)
    cp = c.astype(np.float64)
    return float(np.sum(np.power(cp, -0.5 * p)))


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Singular spectrum fingerprints of the folding conditional expectation $E_m$ "
        "(counting inner products). We report $d_{\\min},d_{\\max}$ and several Schatten norms "
        "computed from $\\sigma_x(E_m)=d_m(x)^{-1/2}$.}"
    )
    lines.append("\\label{tab:fold_conditional_expectation_singular_spectrum}")
    lines.append("\\begin{tabular}{r r r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $|X_m|$ & $d_{\\min}$ & $d_{\\max}$ & $\\|E_m\\|_{HS}^2$ & "
        "$\\|E_m\\|_{S_1}$ & $\\|E_m\\|_{S_2}$ & $\\|E_m\\|_{S_4}$ & $\\|E_m\\|_{op}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.mod} & {r.d_min} & {r.d_max} & "
            f"{r.hs2:.6e} & {r.s1:.6e} & {r.s2:.6e} & {r.s4:.6e} & {r.op:.6e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute singular spectrum of E_m via modular DP.")
    parser.add_argument("--m-list", type=str, default="8,10,12,14,16,18,20,22,24")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_conditional_expectation_singular_spectrum.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_conditional_expectation_singular_spectrum.tex"),
    )
    args = parser.parse_args()

    ms = [int(x) for x in str(args.m_list).split(",") if x.strip()]
    prog = Progress("exp_fold_conditional_expectation_singular_spectrum", every_seconds=20.0)

    out_rows: List[Row] = []
    for m in ms:
        c_uint = counts_mod_fib(m, prog=prog)
        c = c_uint.astype(np.float64, copy=False)
        mod = int(c_uint.shape[0])
        d_min = int(np.min(c_uint))
        d_max = int(np.max(c_uint))

        hs2 = float(np.sum(1.0 / c))
        s1 = _schatten_p_sums(c, p=1.0) ** 1.0
        s2 = _schatten_p_sums(c, p=2.0) ** (1.0 / 2.0)
        s4 = _schatten_p_sums(c, p=4.0) ** (1.0 / 4.0)
        op = float(1.0 / math.sqrt(float(d_min)))

        # Dual positive second moment (collision strength), exact integer via histogram on uint64.
        vals, freq = hist_from_counts(c_uint)
        S2 = 0
        for v, f in zip(vals.tolist(), freq.tolist(), strict=True):
            vv = int(v)
            ff = int(f)
            S2 += ff * (vv * vv)

        out_rows.append(
            Row(
                m=m,
                mod=mod,
                d_min=d_min,
                d_max=d_max,
                hs2=hs2,
                s1=s1,
                s2=s2,
                s4=s4,
                op=op,
                S2=int(S2),
            )
        )
        print(
            f"[E_m-spectrum] m={m} |X|={mod} dmin={d_min} dmax={d_max} HS2={hs2:.6g} op={op:.6g}",
            flush=True,
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps({"rows": [asdict(r) for r in out_rows]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"[E_m-spectrum] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, out_rows)
    print(f"[E_m-spectrum] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

