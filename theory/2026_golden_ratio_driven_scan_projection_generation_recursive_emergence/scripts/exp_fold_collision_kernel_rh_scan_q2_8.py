#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Kernel-RH spectral scan for Fold collision moment-kernels A_q (q=2..8).

We take the audited exact integer recurrences for S_q(m) and interpret their
characteristic polynomials as the spectrum certificate of a minimal realization
(hence an intrinsic spectral fingerprint of the moment-kernel).

For each q we compute:
  r_q      := Perron root (spectral radius)
  Lambda_q := max_{mu != r_q} |mu|  (sub-spectral radius)
  ratio_q  := Lambda_q / sqrt(r_q)  (Ramanujan / kernel-RH ratio)
  beta_q   := log(Lambda_q) / log(r_q)  (s-plane pole exponent)
  delta_q  := log(Lambda_q^2 / r_q)      (Newman-style offset; RH iff <= 0)

Outputs:
  - sections/generated/tab_fold_collision_kernel_rh_scan_q2_8.tex
  - sections/generated/eq_collision_kernel_A4_rh_breaking.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp

from common_paths import generated_dir


RECURRENCE_COEFFS: Dict[int, List[int]] = {
    # Verified recurrences in table tab:fold_collision_moment_recursions
    # Format: S(m) = sum_{i=1}^d c_i S(m-i)
    2: [2, 2, -2],
    3: [2, 4, -2],
    4: [2, 7, 0, 2, -2],
    5: [2, 11, 8, 20, -10],
    6: [2, 17, 28, 88, -26, 4, -4],
    7: [2, 26, 74, 311, -34, 84, -42],
    8: [2, 40, 174, 969, 2, 428, -174, 4, -4],
}


def _poly_from_recurrence(c: Sequence[int]) -> List[mp.mpf]:
    """Return coefficients [a0..ad] for a0*x^d + ... + ad."""
    # Characteristic: x^d - c1 x^{d-1} - ... - cd
    out: List[mp.mpf] = [mp.mpf(1)]
    out.extend(mp.mpf(-int(ci)) for ci in c)
    return out


def _roots(poly_desc: Sequence[mp.mpf]) -> List[mp.mpc]:
    # mpmath.polyroots expects descending coefficients.
    roots = mp.polyroots(list(poly_desc), maxsteps=200, cleanup=True)
    return list(roots)


def _pick_perron(roots: Sequence[mp.mpc]) -> Tuple[int, mp.mpf]:
    """Return (index, r) where r is the Perron root (as a positive real mpf)."""
    # For our audited collision polynomials, Perron root is unique and real > 0.
    idx = max(range(len(roots)), key=lambda i: abs(roots[i]))
    z = roots[idx]
    if abs(mp.im(z)) < mp.mpf("1e-40"):
        r = mp.re(z)
    else:
        r = abs(z)
    if r <= 0:
        raise ValueError("Perron root should be positive")
    return idx, mp.mpf(r)


def _spectral_stats_for_q(q: int) -> Dict[str, mp.mpf]:
    c = RECURRENCE_COEFFS[q]
    poly = _poly_from_recurrence(c)
    roots = _roots(poly)
    per_idx, r = _pick_perron(roots)

    mods = [abs(z) for z in roots]
    # Exclude Perron root by index.
    Lambda = max(mods[i] for i in range(len(mods)) if i != per_idx)
    ratio = Lambda / mp.sqrt(r)
    beta = mp.log(Lambda) / mp.log(r)
    delta = mp.log((Lambda * Lambda) / r)

    # Export with stable mpf types.
    return {
        "q": mp.mpf(q),
        "r": mp.mpf(r),
        "Lambda": mp.mpf(Lambda),
        "ratio": mp.mpf(ratio),
        "beta": mp.mpf(beta),
        "delta": mp.mpf(delta),
    }


def _format_mpf(x: mp.mpf, nd: int = 12) -> str:
    # mp.nstr gives scientific notation for small values; we prefer fixed.
    # Convert to float for formatting; values here are safely in double range.
    return f"{float(x):.{nd}f}"


def _write_table(path: Path, rows: List[Dict[str, mp.mpf]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Kernel-RH spectral scan for the Fold collision moment-kernels "
        "$A_q$ derived from the audited integer recurrences for $S_q(m)$. "
        "We report the Perron root $r_q$, the sub-spectral radius "
        "$\\Lambda_q=\\max_{\\mu\\in\\mathrm{spec}(A_q)\\setminus\\{r_q\\}}|\\mu|$, "
        "the Ramanujan ratio $\\Lambda_q/\\sqrt{r_q}$, the induced pole exponent "
        "$\\beta_q=\\log\\Lambda_q/\\log r_q$, and the Newman-style offset "
        "$\\delta_q=\\log(\\Lambda_q^2/r_q)$.}"
    )
    lines.append("\\label{tab:fold_collision_kernel_rh_scan_q2_8}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & $r_q$ & $\\Lambda_q$ & $\\Lambda_q/\\sqrt{r_q}$ & $\\beta_q$ & $\\delta_q$\\\\")
    lines.append("\\midrule")
    for row in rows:
        q = int(row["q"])
        lines.append(
            f"{q} & {_format_mpf(row['r'])} & {_format_mpf(row['Lambda'])} & "
            f"{_format_mpf(row['ratio'])} & {_format_mpf(row['beta'])} & {_format_mpf(row['delta'])}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def _a4_spectrum_snippet(path: Path, mp_dps: int) -> None:
    # Use the q=4 characteristic polynomial to list the full spectrum.
    mp.mp.dps = max(mp_dps, 80)
    poly = _poly_from_recurrence(RECURRENCE_COEFFS[4])
    roots = _roots(poly)
    per_idx, r4 = _pick_perron(roots)
    per = roots[per_idx]
    tol = mp.mpf("1e-40")

    # Expect: three real roots (including Perron), plus one complex conjugate pair.
    real_roots = [z for z in roots if abs(mp.im(z)) < tol]
    complex_roots = [z for z in roots if abs(mp.im(z)) >= tol]
    if len(real_roots) != 3 or len(complex_roots) != 2:
        raise ValueError("unexpected root pattern for q=4")

    real_other = [z for z in real_roots if abs(z - per) >= mp.mpf("1e-30")]
    if len(real_other) != 2:
        raise ValueError("failed to isolate non-Perron real roots for q=4")

    # Largest-modulus non-Perron eigenvalue is real negative for q=4.
    lam2 = max(real_other, key=lambda z: abs(z))
    lam3 = min(real_other, key=lambda z: abs(z))

    # Pick the one with positive imaginary part to format ±.
    cpos = max(complex_roots, key=lambda z: mp.im(z))
    re_c = mp.re(cpos)
    im_c = abs(mp.im(cpos))

    Lambda4 = abs(lam2)
    sqrt_r4 = mp.sqrt(r4)
    ratio4 = Lambda4 / sqrt_r4
    beta4 = mp.log(Lambda4) / mp.log(r4)
    delta4 = mp.log((Lambda4 * Lambda4) / r4)
    eps4 = beta4 - mp.mpf("0.5")

    # Fixed-decimal formatting.
    def f12(x: mp.mpf) -> str:
        return _format_mpf(x, nd=12)

    def f15(x: mp.mpf) -> str:
        return _format_mpf(x, nd=15)

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_collision_kernel_rh_scan_q2_8.py")
    lines.append("\\begin{equation}\\label{eq:collision_kernel_A4_rh_breaking}")
    lines.append("\\begin{aligned}")
    lines.append(f"\\lambda_1=r_4&\\approx {f12(r4)},\\\\")
    lines.append(f"\\lambda_2&\\approx {f12(mp.re(lam2))},\\\\")
    lines.append(f"\\lambda_3&\\approx {f12(mp.re(lam3))},\\\\")
    lines.append(f"\\lambda_{{4,5}}&\\approx {f12(re_c)}\\pm {f12(im_c)}\\, i,\\\\[2pt]")
    lines.append(f"\\Lambda_4&\\approx {f12(Lambda4)},\\qquad \\sqrt{{r_4}}\\approx {f12(sqrt_r4)},\\\\")
    lines.append(f"\\frac{{\\Lambda_4}}{{\\sqrt{{r_4}}}}&\\approx {f12(ratio4)},\\\\")
    lines.append(f"\\beta_4:=\\frac{{\\log\\Lambda_4}}{{\\log r_4}}&\\approx {f12(beta4)}=\\frac12+{f15(eps4)},\\\\")
    lines.append(f"\\delta_4:=\\log\\!\\left(\\frac{{\\Lambda_4^2}}{{r_4}}\\right)&\\approx {f12(delta4)}.")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Spectral scan for Fold collision moment-kernels (q=2..8).")
    parser.add_argument("--qs", type=str, default="2,3,4,5,6,7,8", help="Comma-separated q values (default: 2..8).")
    parser.add_argument("--mp-dps", type=int, default=90, help="mpmath decimal precision (default: 90).")
    parser.add_argument(
        "--tex-table-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_kernel_rh_scan_q2_8.tex"),
    )
    parser.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_rh_breaking.tex"),
    )
    args = parser.parse_args()

    mp.mp.dps = int(args.mp_dps)

    qs: List[int] = []
    for chunk in (x.strip() for x in str(args.qs).split(",")):
        if not chunk:
            continue
        q = int(chunk)
        if q not in RECURRENCE_COEFFS:
            raise SystemExit(f"q={q} is not available in RECURRENCE_COEFFS")
        qs.append(q)
    if not qs:
        raise SystemExit("empty --qs list")

    rows: List[Dict[str, mp.mpf]] = []
    for q in qs:
        row = _spectral_stats_for_q(q)
        rows.append(row)
        print(
            f"q={q} r={float(row['r']):.12f} Lambda={float(row['Lambda']):.12f} "
            f"ratio={float(row['ratio']):.12f} beta={float(row['beta']):.12f} delta={float(row['delta']):.12f}",
            flush=True,
        )

    table_path = Path(str(args.tex_table_out))
    eq_path = Path(str(args.tex_eq_out))
    _write_table(table_path, rows=rows)
    _a4_spectrum_snippet(eq_path, mp_dps=int(args.mp_dps))

    print("Wrote:", str(table_path))
    print("Wrote:", str(eq_path))


if __name__ == "__main__":
    main()

