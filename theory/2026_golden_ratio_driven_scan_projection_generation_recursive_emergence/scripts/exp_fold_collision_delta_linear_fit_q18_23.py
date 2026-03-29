#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Least-squares linear fit for the high-q kernel-RH shift delta_q (q=18..23).

This script parses the already-exported table:
  sections/generated/tab_fold_collision_kernel_rh_scan_q18_23.tex
extracts (q, delta_q), and fits
  delta_q ≈ a*q + b
by ordinary least squares.

Outputs:
  - artifacts/export/fold_collision_delta_linear_fit_q18_23.json
  - sections/generated/eq_fold_collision_delta_linear_fit_q18_23.tex
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import List, Tuple

from common_paths import export_dir, generated_dir, paper_root


def _parse_q_delta_from_table(p: Path) -> Tuple[List[int], List[float]]:
    qs: List[int] = []
    deltas: List[float] = []
    for raw in p.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("%") or line.startswith("\\"):
            continue
        if "&" not in line or not line[:1].isdigit():
            continue
        parts = [x.strip() for x in line.split("&")]
        if len(parts) < 2:
            continue
        q = int(parts[0])
        delta_str = parts[-1].replace("\\\\", "").strip()
        delta = float(delta_str)
        qs.append(q)
        deltas.append(delta)
    if not qs:
        raise RuntimeError(f"no (q, delta_q) rows parsed from table: {p}")
    return qs, deltas


def _ols_fit(xs: List[int], ys: List[float]) -> Tuple[float, float]:
    x = [float(v) for v in xs]
    y = [float(v) for v in ys]
    xbar = sum(x) / len(x)
    ybar = sum(y) / len(y)
    sxx = sum((xi - xbar) ** 2 for xi in x)
    if sxx == 0.0:
        raise RuntimeError("degenerate x variance in OLS fit")
    sxy = sum((xi - xbar) * (yi - ybar) for xi, yi in zip(x, y))
    a = sxy / sxx
    b = ybar - a * xbar
    return a, b


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--table",
        type=str,
        default="sections/generated/tab_fold_collision_kernel_rh_scan_q18_23.tex",
        help="relative path to the TeX table to parse",
    )
    args = ap.parse_args()

    table_path = (paper_root() / args.table).resolve()
    qs, deltas = _parse_q_delta_from_table(table_path)
    a, b = _ols_fit(qs, deltas)

    a6 = f"{a:.6f}"
    b6 = f"{b:+.6f}"
    a2_6 = f"{(a / 2.0):.6f}"
    b2_6 = f"{(b / 2.0):+.6f}"

    export_dir().mkdir(parents=True, exist_ok=True)
    generated_dir().mkdir(parents=True, exist_ok=True)

    out_json = export_dir() / "fold_collision_delta_linear_fit_q18_23.json"
    out_tex = generated_dir() / "eq_fold_collision_delta_linear_fit_q18_23.tex"

    payload = {
        "source_table": str(Path(args.table)),
        "q_min": min(qs),
        "q_max": max(qs),
        "slope_delta": a,
        "intercept_delta": b,
        "slope_logR": a / 2.0,
        "intercept_logR": b / 2.0,
        "n": len(qs),
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    out_tex.write_text(
        "\n".join(
            [
                "% Auto-generated; do not edit by hand.",
                r"\begin{equation}\label{eq:fold-collision-delta-linear-fit-q18-23}",
                r"\boxed{",
                rf"\delta_q \approx {a6}\,q{b6},",
                rf"\qquad R_q=\exp(\delta_q/2)\approx \exp({a2_6}\,q{b2_6}),",
                r"\qquad (q=18,\dots,23).",
                r"}",
                r"\end{equation}",
                "",
            ]
        ),
        encoding="utf-8",
    )

    print(f"[ok] parsed n={len(qs)} rows from {table_path.name}")
    print(f"[ok] delta_q ~= {a6} * q {b6}")
    print(f"[ok] log R_q ~= {a2_6} * q {b2_6}")


if __name__ == "__main__":
    main()

