#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Derived left-tail conclusions from the singular spectrum table of E_m.

We treat the generated TeX table
  sections/generated/tab_fold_conditional_expectation_singular_spectrum.tex
as the auditable interface (Table 99 in the compiled manuscript).

From that table alone we compute three derived layers:
  1) Empirical per-step bases b_s(m) for negative moments
       T_s(m) := sum_{x in X_m} d_m(x)^(-s), s in {1/2, 1, 2}.
  2) Effective support sizes of the singular-value energy distribution p_x ∝ d_m(x)^(-1):
       N2    = 1 / sum_x p_x^2,
       N1/2  = (sum_x sqrt(p_x))^2.
  3) Paley–Zygmund left-tail certificate (m=24) for s=1/2 and s=1.

Outputs:
  - artifacts/export/fold_conditional_expectation_left_tail_conclusions.json
  - sections/generated/tab_fold_conditional_expectation_left_tail_bases.tex
  - sections/generated/tab_fold_conditional_expectation_effective_support.tex
  - sections/generated/eq_fold_conditional_expectation_left_tail_m24.tex
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class SpectrumRow:
    m: int
    X: int
    d_min: int
    d_max: int
    hs2: float
    s1: float
    s2: float
    s4: float
    op: float


_ROW_RE = re.compile(r"^\s*(\d+)\s*&")


def _parse_spectrum_table(tex_path: Path) -> List[SpectrumRow]:
    if not tex_path.is_file():
        raise SystemExit(f"Missing input table: {tex_path}")
    rows: List[SpectrumRow] = []
    for raw in tex_path.read_text(encoding="utf-8").splitlines():
        if not _ROW_RE.match(raw):
            continue
        line = raw.strip()
        # Drop the trailing LaTeX row terminator "\\"
        line = line.split("\\\\")[0].strip()
        parts = [p.strip() for p in line.split("&")]
        if len(parts) < 9:
            raise SystemExit(f"Failed to parse row (expected 9 cols): {raw}")
        rows.append(
            SpectrumRow(
                m=int(parts[0]),
                X=int(parts[1]),
                d_min=int(parts[2]),
                d_max=int(parts[3]),
                hs2=float(parts[4]),
                s1=float(parts[5]),
                s2=float(parts[6]),
                s4=float(parts[7]),
                op=float(parts[8]),
            )
        )
    if not rows:
        raise SystemExit(f"No rows parsed from: {tex_path}")
    return sorted(rows, key=lambda r: r.m)


def _tex_sci(x: float, digits_after_decimal: int = 5) -> str:
    """Format x as a TeX scientific string like '5.53146\\times 10^{4}'."""
    if x == 0.0:
        return "0"
    s = f"{x:.{digits_after_decimal}e}"  # e.g. 5.53146e+04
    mant, exp = s.split("e")
    exp_i = int(exp)
    return f"{mant}\\times 10^{{{exp_i}}}"


def _write_table_left_tail_bases(path: Path, bases: List[Dict[str, float]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{从表 \\ref{tab:fold_conditional_expectation_singular_spectrum} 导出的负矩左尾经验底数。"
        "定义 $T_s(m)=\\sum_{x\\in X_m}d_m(x)^{-s}$，并在偶数网格上取 "
        "$b_s(m)=(T_s(m)/T_s(m-2))^{1/2}$（每增加 $1$ 个 $m$ 的底数）。"
        "报告 $s=\\tfrac12,1,2$ 的结果。}"
    )
    lines.append("\\label{tab:fold_conditional_expectation_left_tail_bases}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $b_{1/2}(m)$ & $b_{1}(m)$ & $b_{2}(m)$\\\\")
    lines.append("\\midrule")
    for r in bases:
        lines.append(f"{int(r['m'])} & {r['b_half']:.6f} & {r['b_1']:.6f} & {r['b_2']:.6f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_table_effective_support(path: Path, rows: List[Dict[str, float]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{折叠条件期望 $E_m$ 的奇异值能量分布之有效支撑规模。"
        "令 $p_x\\propto d_m(x)^{-1}$，并定义 $N_2=1/\\sum_x p_x^2$ 与 "
        "$N_{1/2}=(\\sum_x\\sqrt{p_x})^2$；各值均可由表 "
        "\\ref{tab:fold_conditional_expectation_singular_spectrum} 的 Schatten 范数直接复算。}"
    )
    lines.append("\\label{tab:fold_conditional_expectation_effective_support}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $|X_m|$ & $N_2(m)$ & $N_2/|X_m|$ & $N_{1/2}(m)$ & $N_{1/2}/|X_m|$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{int(r['m'])} & {int(r['X'])} & {r['N2']:.6e} & {r['N2_ratio']:.6f} & "
            f"{r['Nhalf']:.6e} & {r['Nhalf_ratio']:.6f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_eq_m24(path: Path, m24: Dict[str, float]) -> None:
    # Use integer ceilings for thresholds:
    # event {d <= ceil(threshold)} contains {d <= threshold}, hence the lower bound is preserved.
    d_half = int(m24["pz_half_thresh_int"])
    d_1 = int(m24["pz_1_thresh_int"])
    lines: List[str] = []
    lines.append(f"% Auto-generated by {Path(__file__).name}")
    lines.append("% Auditable numeric readout for m=24 (inputs come from Table 99).")
    lines.append(
        "\\begin{remark}[数值例（$m=24$）：有效支撑与左尾证书]\\label{rem:fold-negative-moment-m24}"
    )
    lines.append(
        "将表 \\ref{tab:fold_conditional_expectation_singular_spectrum} 的 $m=24$ 行代入命题 "
        "\\ref{prop:fold-Em-effective-support-schatten} 与定理 "
        "\\ref{prop:fold-negative-moment-left-tail-certificate}，得到"
    )
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(
        f"N_2(24) &\\approx {_tex_sci(float(m24['N2']))},\\qquad "
        f"N_{{1/2}}(24)\\approx {_tex_sci(float(m24['Nhalf']))},\\\\"
    )
    lines.append(
        f"\\frac{{\\#\\{{x\\in X_{{24}}:\\ d_{{24}}(x)\\le {d_half}\\}}}}{{|X_{{24}}|}}"
        f" &\\ge {_tex_sci(float(m24['pz_half_frac']))},\\\\"
    )
    lines.append(
        f"\\frac{{\\#\\{{x\\in X_{{24}}:\\ d_{{24}}(x)\\le {d_1}\\}}}}{{|X_{{24}}|}}"
        f" &\\ge {_tex_sci(float(m24['pz_1_frac']))}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append(
        "其中阈值 $"
        f"{d_half}$ 与 ${d_1}$ 分别为 $(2|X_{{24}}|/T_{{1/2}}(24))^2$ 与 "
        "$(2|X_{24}|/T_{1}(24))$ 的上取整（从而不削弱下界）。"
    )
    lines.append("\\end{remark}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Derive left-tail conclusions from E_m singular-spectrum table."
    )
    parser.add_argument(
        "--input-tex",
        type=str,
        default=str(generated_dir() / "tab_fold_conditional_expectation_singular_spectrum.tex"),
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_conditional_expectation_left_tail_conclusions.json"),
    )
    parser.add_argument(
        "--tex-bases-out",
        type=str,
        default=str(generated_dir() / "tab_fold_conditional_expectation_left_tail_bases.tex"),
    )
    parser.add_argument(
        "--tex-support-out",
        type=str,
        default=str(generated_dir() / "tab_fold_conditional_expectation_effective_support.tex"),
    )
    parser.add_argument(
        "--tex-m24-out",
        type=str,
        default=str(generated_dir() / "eq_fold_conditional_expectation_left_tail_m24.tex"),
    )
    args = parser.parse_args()

    tex_in = Path(args.input_tex)
    spec_rows = _parse_spectrum_table(tex_in)
    by_m: Dict[int, SpectrumRow] = {r.m: r for r in spec_rows}

    # --- 1) Left-tail bases (adjacent even m, step=2) ---
    bases_out: List[Dict[str, float]] = []
    for r in spec_rows:
        if (r.m - 2) not in by_m:
            continue
        rp = by_m[r.m - 2]
        # T_{1/2}=||E||_{S1}, T_1=||E||_{HS}^2, T_2=||E||_{S4}^4
        T_half = float(r.s1)
        T_1 = float(r.hs2)
        T_2 = float(r.s4**4)
        Tp_half = float(rp.s1)
        Tp_1 = float(rp.hs2)
        Tp_2 = float(rp.s4**4)
        bases_out.append(
            {
                "m": float(r.m),
                "b_half": math.sqrt(T_half / Tp_half),
                "b_1": math.sqrt(T_1 / Tp_1),
                "b_2": math.sqrt(T_2 / Tp_2),
            }
        )

    # --- 2) Effective support sizes ---
    support_out: List[Dict[str, float]] = []
    for r in spec_rows:
        T_1 = float(r.hs2)
        T_2 = float(r.s4**4)
        N2 = (T_1 * T_1) / T_2
        Nhalf = (float(r.s1) / float(r.s2)) ** 2
        support_out.append(
            {
                "m": float(r.m),
                "X": float(r.X),
                "N2": float(N2),
                "Nhalf": float(Nhalf),
                "N2_ratio": float(N2 / float(r.X)),
                "Nhalf_ratio": float(Nhalf / float(r.X)),
            }
        )

    # --- 3) Paley–Zygmund left-tail certificate at m=24 ---
    if 24 not in by_m:
        raise SystemExit("m=24 row not found in input table")
    r24 = by_m[24]
    X24 = float(r24.X)
    T_half_24 = float(r24.s1)
    T_1_24 = float(r24.hs2)
    T_2_24 = float(r24.s4**4)
    # s=1/2: T_{2s}=T_1
    pz_half_frac = 0.25 * (T_half_24 * T_half_24) / (X24 * T_1_24)
    pz_half_thresh = (2.0 * X24 / T_half_24) ** 2
    # s=1: T_{2s}=T_2
    pz_1_frac = 0.25 * (T_1_24 * T_1_24) / (X24 * T_2_24)
    pz_1_thresh = (2.0 * X24 / T_1_24)

    m24_out = {
        "m": 24,
        "X": r24.X,
        "N2": (T_1_24 * T_1_24) / T_2_24,
        "Nhalf": (float(r24.s1) / float(r24.s2)) ** 2,
        "pz_half_frac": pz_half_frac,
        "pz_half_thresh": pz_half_thresh,
        "pz_half_thresh_int": float(math.ceil(pz_half_thresh - 1e-12)),
        "pz_1_frac": pz_1_frac,
        "pz_1_thresh": pz_1_thresh,
        "pz_1_thresh_int": float(math.ceil(pz_1_thresh - 1e-12)),
    }

    # --- Write outputs ---
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "input_table": str(tex_in),
                "spectrum_rows": [asdict(r) for r in spec_rows],
                "bases": bases_out,
                "effective_support": support_out,
                "m24": m24_out,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[left-tail] wrote {jout}", flush=True)

    _write_table_left_tail_bases(Path(args.tex_bases_out), bases_out)
    print(f"[left-tail] wrote {args.tex_bases_out}", flush=True)

    _write_table_effective_support(Path(args.tex_support_out), support_out)
    print(f"[left-tail] wrote {args.tex_support_out}", flush=True)

    _write_eq_m24(Path(args.tex_m24_out), m24_out)
    print(f"[left-tail] wrote {args.tex_m24_out}", flush=True)


if __name__ == "__main__":
    main()

