#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the endpoint angle-window law vs the min-entropy endpoint constant.

This script is English-only by repository convention.

We use the exact closed-form measure for the endpoint angle window A_Y(varrho):
  meas A_Y(varrho) = 2(π - arccos(c_Y(varrho)))
where
  c_Y(varrho) = ((1 - varrho^2) - Y(1 + varrho^2)) / (2 varrho Y)
in the intermediate regime y_-(varrho) < Y < y_+(varrho), with
  y_-(varrho) = (1 - varrho)/(1 + varrho),  y_+(varrho) = (1 + varrho)/(1 - varrho).

We then test the scaling from Theorem~\\ref{thm:app-endpoint-window-hinfty-match}:
  phi := (1 + sqrt(5))/2,
  h_infty := log(2/sqrt(phi)),
  Y_m := (4/phi^2)^m,
  varrho_m := 1 - eta_m,  eta_m := c * phi^{-m}.

The theorem predicts:
  meas A_{Y_m}(varrho_m) ~ 2*sqrt(2c)*exp(-m*h_infty),
and hence
  P(Im t(varrho_m, Θ) >= Y_m) ~ (sqrt(2c)/pi) * exp(-m*h_infty),
with Θ ~ Unif[0, 2π).

Outputs:
- artifacts/export/jensen_endpoint_window_hinfty_match.csv
- sections/generated/tab_jensen_endpoint_window_hinfty_match.tex
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List

from common_paths import export_dir, generated_dir


def golden_ratio() -> float:
    return (1.0 + math.sqrt(5.0)) / 2.0


def h_infty(phi: float) -> float:
    return math.log(2.0 / math.sqrt(phi))


def y_minus(varrho: float) -> float:
    return (1.0 - varrho) / (1.0 + varrho)


def y_plus(varrho: float) -> float:
    return (1.0 + varrho) / (1.0 - varrho)


def c_Y(varrho: float, Y: float) -> float:
    return ((1.0 - varrho * varrho) - Y * (1.0 + varrho * varrho)) / (2.0 * varrho * Y)


def meas_A(varrho: float, Y: float) -> float:
    """Return meas A_Y(varrho) in [0, 2π]."""
    ym = y_minus(varrho)
    yp = y_plus(varrho)
    if Y <= ym:
        return 2.0 * math.pi
    if Y >= yp:
        return 0.0
    # Intermediate regime: use a numerically stable evaluation.
    #
    # We have the exact identity:
    #   meas A_Y(varrho) = 2(π - arccos(c)) = 2 arccos(-c),
    # and arccos(-c) can be written as 2 asin(sqrt((1+c)/2)).
    #
    # The direct c_Y formula loses the tiny (1+c) scale when c≈-1, so we compute
    # eps := 1 + c_Y(varrho) in a cancellation-free form:
    #   eps = (1 - varrho^2)/(2 varrho Y) - (1 - varrho)^2/(2 varrho).
    eta = 1.0 - varrho
    one_minus_varrho2 = eta * (2.0 - eta)  # exact: 1 - (1-eta)^2 = 2η - η^2
    eps = (one_minus_varrho2 / (2.0 * varrho * Y)) - ((eta * eta) / (2.0 * varrho))
    # Guard against tiny negative due to roundoff at the boundary.
    if eps <= 0.0:
        return 0.0
    if eps >= 2.0:
        return 2.0 * math.pi
    return 4.0 * math.asin(math.sqrt(eps / 2.0))


@dataclass(frozen=True)
class Row:
    m: int
    c: float
    eta: float
    varrho: float
    Y: float
    y_minus: float
    y_plus: float
    meas: float
    pred_meas: float
    ratio_meas: float
    prob: float
    pred_prob: float
    ratio_prob: float
    regime: str


def build_rows(c: float, m_min: int, m_max: int) -> List[Row]:
    phi = golden_ratio()
    hinf = h_infty(phi)
    rows: List[Row] = []
    for m in range(m_min, m_max + 1):
        eta = c * (phi ** (-m))
        varrho = 1.0 - eta
        Y = (4.0 / (phi * phi)) ** m

        ym = y_minus(varrho)
        yp = y_plus(varrho)
        if Y <= ym:
            regime = "all"
        elif Y >= yp:
            regime = "empty"
        else:
            regime = "window"

        meas = meas_A(varrho, Y)
        pred_meas = 2.0 * math.sqrt(2.0 * c) * math.exp(-m * hinf)
        ratio_meas = meas / pred_meas if pred_meas > 0 else float("nan")

        prob = meas / (2.0 * math.pi)
        pred_prob = (math.sqrt(2.0 * c) / math.pi) * math.exp(-m * hinf)
        ratio_prob = prob / pred_prob if pred_prob > 0 else float("nan")

        rows.append(
            Row(
                m=m,
                c=c,
                eta=eta,
                varrho=varrho,
                Y=Y,
                y_minus=ym,
                y_plus=yp,
                meas=meas,
                pred_meas=pred_meas,
                ratio_meas=ratio_meas,
                prob=prob,
                pred_prob=pred_prob,
                ratio_prob=ratio_prob,
                regime=regime,
            )
        )
    return rows


def write_csv(rows: List[Row], out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "m",
                "c",
                "eta",
                "varrho",
                "Y",
                "y_minus",
                "y_plus",
                "regime",
                "meas",
                "pred_meas",
                "ratio_meas",
                "prob",
                "pred_prob",
                "ratio_prob",
            ]
        )
        for r in rows:
            w.writerow(
                [
                    r.m,
                    f"{r.c:.12g}",
                    f"{r.eta:.12g}",
                    f"{r.varrho:.12g}",
                    f"{r.Y:.12g}",
                    f"{r.y_minus:.12g}",
                    f"{r.y_plus:.12g}",
                    r.regime,
                    f"{r.meas:.12g}",
                    f"{r.pred_meas:.12g}",
                    f"{r.ratio_meas:.12g}",
                    f"{r.prob:.12g}",
                    f"{r.pred_prob:.12g}",
                    f"{r.ratio_prob:.12g}",
                ]
            )


def write_tex(rows: List[Row], out_path: Path, stride: int) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Keep a compact audit table: stride-subsample plus always include m=6.
    keep: List[Row] = []
    for r in rows:
        if r.m == 6 or (stride > 0 and (r.m - rows[0].m) % stride == 0):
            keep.append(r)

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_jensen_endpoint_window_hinfty_match.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.12}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $\\eta_m$ & $Y_m$ & $\\mathrm{meas}\\,A_{Y_m}(\\varrho_m)$ & "
        "$\\frac{\\mathrm{meas}\\,A_{Y_m}(\\varrho_m)}{2\\sqrt{2c}\\,e^{-m h_\\infty}}$ \\\\"
    )
    lines.append("\\midrule")
    for r in keep:
        lines.append(
            f"{r.m} & {r.eta:.3e} & {r.Y:.3e} & {r.meas:.6g} & {r.ratio_meas:.6g} \\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{Audit of Theorem~\\ref{thm:app-endpoint-window-hinfty-match}: "
        "the exact endpoint angle-window measure $\\mathrm{meas}\\,A_{Y_m}(\\varrho_m)$ "
        "computed from the closed form in Proposition~\\ref{prop:app-jensen-endpoint-angle-window}, "
        "under the scaling $Y_m=(4/\\varphi^2)^m$ and $\\varrho_m=1-c\\varphi^{-m}$.}"
    )
    lines.append("\\label{tab:jensen_endpoint_window_hinfty_match}")
    lines.append("\\end{table}")
    lines.append("")
    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--c", type=float, default=1.0, help="eta_m = c * phi^{-m}")
    p.add_argument("--m_min", type=int, default=4)
    p.add_argument("--m_max", type=int, default=48)
    p.add_argument("--tex_stride", type=int, default=4, help="Subsample stride for TeX table.")
    args = p.parse_args()

    if args.c <= 0:
        raise SystemExit("--c must be > 0")
    if args.m_min < 1 or args.m_max < args.m_min:
        raise SystemExit("Require 1 <= m_min <= m_max")

    rows = build_rows(args.c, args.m_min, args.m_max)

    csv_path = export_dir() / "jensen_endpoint_window_hinfty_match.csv"
    tex_path = generated_dir() / "tab_jensen_endpoint_window_hinfty_match.tex"
    write_csv(rows, csv_path)
    write_tex(rows, tex_path, stride=args.tex_stride)

    # Minimal stdout summary (deterministic, useful for CI logs).
    last = rows[-1]
    print(
        f"[jensen_endpoint_window_hinfty_match] m={last.m} regime={last.regime} "
        f"ratio_meas={last.ratio_meas:.6g} ratio_prob={last.ratio_prob:.6g}"
    )


if __name__ == "__main__":
    main()

