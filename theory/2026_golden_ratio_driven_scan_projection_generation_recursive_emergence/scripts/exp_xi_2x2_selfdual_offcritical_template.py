#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Minimal (2x2) self-dual bridge kernel: explicit off-critical zero template.

Outputs:
- artifacts/export/xi_2x2_selfdual_offcritical_template.json
- sections/generated/tab_xi_2x2_selfdual_offcritical_template.tex

This script generates a small, audit-friendly numerical artifact for the explicit
classification in Theorem `thm:xi-2x2-selfdual-offcritical-template`.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import dataclass
from typing import Dict, List, Sequence

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class RootRow:
    equation: str
    r: complex
    abs_r: float
    arg_r: float
    sigma: float
    t0: float


def _quad_roots(A: float, B: float, C: float) -> List[complex]:
    """Solve A x^2 + B x + C = 0 (A,B,C real), returning 0-2 complex roots."""
    if abs(A) < 1e-30:
        # Linear (or degenerate).
        if abs(B) < 1e-30:
            return []
        return [complex(-C / B, 0.0)]
    D = complex(B * B - 4.0 * A * C, 0.0)
    sqrtD = cmath.sqrt(D)
    return [(-B + sqrtD) / (2.0 * A), (-B - sqrtD) / (2.0 * A)]


def _fmt_float(x: float, sig: int = 6) -> str:
    # Compact, stable formatting consistent with other tables in this repo.
    return f"{x:.{sig}g}"


def _fmt_complex(z: complex, sig: int = 6) -> str:
    re = float(z.real)
    im = float(z.imag)
    if abs(im) < 5e-15:
        return _fmt_float(re, sig=sig)
    sgn = "+" if im >= 0 else "-"
    return f"{_fmt_float(re, sig=sig)}{sgn}{_fmt_float(abs(im), sig=sig)}\\mathrm{{i}}"


def _compute_rows(a: int, b: int, L: float) -> List[RootRow]:
    if not (L > 1.0):
        raise ValueError("require L>1")
    sqrtL = float(math.sqrt(L))
    logL = float(math.log(L))
    if logL <= 0.0:
        raise ValueError("unexpected: logL<=0")

    rows: List[RootRow] = []
    eqs = [
        (r"$(a+b)r^2-\sqrt{L}\,r+(a-b)=0$", float(a + b), -sqrtL, float(a - b)),
        (r"$(a-b)r^2-\sqrt{L}\,r+(a+b)=0$", float(a - b), -sqrtL, float(a + b)),
    ]
    for eq_name, A, B, C in eqs:
        for r in _quad_roots(A, B, C):
            abs_r = float(abs(r))
            if abs_r <= 0.0:
                # r=0 would correspond to |u|=0 and is not a meaningful s-address.
                continue
            arg_r = float(cmath.phase(r))
            sigma = 0.5 + float(math.log(abs_r)) / logL
            t0 = float(arg_r) / logL
            rows.append(
                RootRow(
                    equation=eq_name,
                    r=r,
                    abs_r=abs_r,
                    arg_r=arg_r,
                    sigma=sigma,
                    t0=t0,
                )
            )

    # Deterministic ordering: (equation, |r|, arg, Re).
    rows.sort(
        key=lambda rr: (
            rr.equation,
            round(rr.abs_r, 15),
            round(rr.arg_r, 15),
            round(rr.r.real, 15),
        )
    )
    return rows


def _write_json(a: int, b: int, L: float, rows: Sequence[RootRow]) -> str:
    logL = float(math.log(L))
    out: Dict[str, object] = {
        "a": int(a),
        "b": int(b),
        "L": float(L),
        "sqrtL": float(math.sqrt(L)),
        "logL": float(logL),
        "imag_period": float(2.0 * math.pi / logL),
        "roots": [
            {
                "equation": rr.equation,
                "r_re": float(rr.r.real),
                "r_im": float(rr.r.imag),
                "abs_r": float(rr.abs_r),
                "arg_r": float(rr.arg_r),
                "sigma": float(rr.sigma),
                "t0_k0": float(rr.t0),
                "delta_sigma": float(rr.sigma - 0.5),
            }
            for rr in rows
        ],
    }

    p = export_dir() / "xi_2x2_selfdual_offcritical_template.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return str(p)


def _write_table(a: int, b: int, L: float, rows: Sequence[RootRow]) -> str:
    logL = float(math.log(L))
    period = float(2.0 * math.pi / logL)

    lines: List[str] = []
    lines.append("\\begin{table}[H]\n")
    lines.append("\\centering\n")
    lines.append("\\small\n")
    lines.append("\\begin{tabular}{l l r r r}\n")
    lines.append("\\toprule\n")
    lines.append("eq & $r$ & $|r|$ & $\\Re(s)-\\tfrac12$ & $\\Im(s)$ (k=0)\\\\\n")
    lines.append("\\midrule\n")
    for rr in rows:
        r_tex = _fmt_complex(rr.r)
        abs_tex = _fmt_float(rr.abs_r)
        ds_tex = _fmt_float(rr.sigma - 0.5)
        im_tex = _fmt_float(rr.t0)
        lines.append(
            f"{rr.equation} & ${r_tex}$ & {abs_tex} & {ds_tex} & {im_tex}\\\\\n"
        )
    lines.append("\\bottomrule\n")
    lines.append("\\end{tabular}\n")
    lines.append(
        "\\caption{最小 $(2\\times2)$ 自对偶桥接核在样例参数 "
        f"$(a,b,L)=({a},{b},{_fmt_float(L, sig=8)})$ 下的代数根 $r$，以及 "
        "$s=\\tfrac12+\\log r/\\log L$ 在主值分支 ($k=0$) 的零点样本。"
        f"虚部平移周期为 $2\\pi/\\log L\\approx {_fmt_float(period, sig=6)}$.}}\n"
    )
    lines.append("\\label{tab:xi-2x2-selfdual-offcritical-template}\n")
    lines.append("\\end{table}\n")

    p = generated_dir() / "tab_xi_2x2_selfdual_offcritical_template.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(lines), encoding="utf-8")
    return str(p)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate an audit table for the minimal 2x2 self-dual off-critical template."
    )
    parser.add_argument("--a", type=int, default=2)
    parser.add_argument("--b", type=int, default=1)
    parser.add_argument("--L", type=float, default=5.0)
    args = parser.parse_args()

    rows = _compute_rows(int(args.a), int(args.b), float(args.L))
    _write_json(int(args.a), int(args.b), float(args.L), rows)
    _write_table(int(args.a), int(args.b), float(args.L), rows)


if __name__ == "__main__":
    main()

