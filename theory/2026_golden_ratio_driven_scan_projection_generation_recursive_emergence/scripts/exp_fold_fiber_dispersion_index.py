#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fiber dispersion index from the folding conditional expectation E_m.

Recall the folding fiber sizes d_m(x)=|Fold_m^{-1}(x)| (x in X_m), and the conditional
expectation (fiber average) E_m. With counting inner products,
    ||E_m||_{HS}^2 = sum_x 1/d_m(x).

Define the dispersion index
    D_m := (2^m / |X_m|^2) * ||E_m||_{HS}^2
         = (arithmetic mean of d_m) / (harmonic mean of d_m),
which is >= 1 with equality iff all fibers are equal.

Outputs:
  - artifacts/export/fold_fiber_dispersion_index.json
  - sections/generated/tab_fold_fiber_dispersion_index.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_fold_collision_moment_recursions_mod_dp import counts_mod_fib


@dataclass(frozen=True)
class Row:
    m: int
    x_card: int
    hs2: float
    dispersion: float


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Fiber dispersion index $\\mathfrak{D}_m$ derived from the folding conditional "
        "expectation $E_m$ (counting inner products). We report $\\|E_m\\|_{HS}^2=\\sum_x 1/d_m(x)$ "
        "and $\\mathfrak{D}_m=(2^m/|X_m|^2)\\,\\|E_m\\|_{HS}^2$.}"
    )
    lines.append("\\label{tab:fold_fiber_dispersion_index}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $|X_m|$ & $\\|E_m\\|_{HS}^2$ & $\\mathfrak{D}_m$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.m} & {r.x_card} & {r.hs2:.6e} & {r.dispersion:.6f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compute fiber dispersion index D_m from modular DP fiber counts."
    )
    parser.add_argument("--m-list", type=str, default="8,10,12,14,16,18,20,22,24")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_fiber_dispersion_index.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_fiber_dispersion_index.tex"),
    )
    args = parser.parse_args()

    ms = [int(x) for x in str(args.m_list).split(",") if x.strip()]
    prog = Progress("exp_fold_fiber_dispersion_index", every_seconds=20.0)

    out_rows: List[Row] = []
    for m in ms:
        c_uint = counts_mod_fib(m, prog=prog)
        c = c_uint.astype(np.float64, copy=False)
        x_card = int(c_uint.shape[0])

        hs2 = float(np.sum(1.0 / c))
        dispersion = float((2**m) * hs2 / float(x_card * x_card))

        out_rows.append(Row(m=m, x_card=x_card, hs2=hs2, dispersion=dispersion))
        print(
            f"[fiber-dispersion] m={m} |X|={x_card} HS2={hs2:.6g} D={dispersion:.6g}",
            flush=True,
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps({"rows": [asdict(r) for r in out_rows]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"[fiber-dispersion] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, out_rows)
    print(f"[fiber-dispersion] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

