#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Half-angle compression image of the nearest complex branch point for hatDelta(w,s).

This script is a lightweight post-processing step for:
  scripts/exp_sync_kernel_hatdelta_discriminant.py

That script outputs the nearest complex branch point in the unit-circle angle variable
  t = 2*acos(s/2)   (principal branch),
reported as theta_* = a ± b i.

On the unit-circle twist u = e^{it}, the completed log variable is theta = log u = i t.
We therefore map the nearest branch point to the theta-plane (log coordinate) as
  theta_* = i t_* = -b ± a i,
and then apply the half-angle compression
  x = tan(theta/2).

Outputs:
  - artifacts/export/sync_kernel_hatdelta_nearest_complex_branch_point_tan_half_angle.json
  - sections/generated/tab_sync_kernel_hatdelta_nearest_complex_branch_point_tan_half_angle.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class TanHalfAngleImage:
    # Input (angle-plane) nearest complex branch point t_* = a ± b i.
    t_re: str
    t_im_abs: str
    t_abs: str
    # Log-coordinate theta = i t => theta_* = -b ± a i.
    theta_re: str
    theta_im_abs: str
    theta_abs: str
    # Compressed coordinate x = tan(theta/2).
    x_re: str
    x_im_abs: str
    x_abs: str


def _mp_nstr(x, nd_sig: int = 16) -> str:
    import mpmath as mp

    return mp.nstr(x, nd_sig)


def _load_json(p: Path) -> Dict[str, Any]:
    return json.loads(p.read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Map nearest complex branch point (hatDelta discriminant) to x=tan(theta/2) in the log coordinate."
    )
    parser.add_argument("--dps", type=int, default=80, help="mpmath decimal digits for tan().")
    parser.add_argument(
        "--in-json",
        type=str,
        default=str(export_dir() / "sync_kernel_hatdelta_discriminant.json"),
        help="Input JSON from exp_sync_kernel_hatdelta_discriminant.py.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_hatdelta_nearest_complex_branch_point_tan_half_angle.json"),
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_hatdelta_nearest_complex_branch_point_tan_half_angle.tex"),
    )
    args = parser.parse_args()

    import mpmath as mp

    mp.mp.dps = int(args.dps)

    pin = Path(args.in_json)
    if not pin.is_file():
        raise FileNotFoundError(f"missing input JSON: {pin}")

    payload = _load_json(pin)
    ncbp = payload.get("nearest_complex_branch_point", None)
    if not isinstance(ncbp, dict):
        raise ValueError("input JSON missing 'nearest_complex_branch_point' dict")

    # t_* = a ± b i (angle-plane variable; stored as magnitudes in the JSON).
    a = mp.mpf(str(ncbp["theta_re"]))
    b = mp.mpf(str(ncbp["theta_im_abs"]))
    t_abs = mp.mpf(str(ncbp.get("theta_abs", payload.get("theta_radius", "0"))))
    if t_abs == 0:
        # Fallback: compute from a,b if not present.
        t_abs = mp.sqrt(a * a + b * b)

    # theta = i t => theta_* = -b ± a i.
    theta_re = -b
    theta_im_abs = a
    theta_abs = t_abs  # |i t| = |t|

    theta_plus = mp.mpc(theta_re, theta_im_abs)
    x_plus = mp.tan(theta_plus / 2)

    x_re = mp.re(x_plus)
    x_im_abs = abs(mp.im(x_plus))
    x_abs = abs(x_plus)

    out = TanHalfAngleImage(
        t_re=_mp_nstr(a, 16),
        t_im_abs=_mp_nstr(b, 16),
        t_abs=_mp_nstr(t_abs, 16),
        theta_re=_mp_nstr(theta_re, 16),
        theta_im_abs=_mp_nstr(theta_im_abs, 16),
        theta_abs=_mp_nstr(theta_abs, 16),
        x_re=_mp_nstr(x_re, 16),
        x_im_abs=_mp_nstr(x_im_abs, 16),
        x_abs=_mp_nstr(x_abs, 16),
    )

    # JSON output (audit-friendly).
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(out), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[hatdelta-tan-half-angle] wrote {jout}", flush=True)

    # LaTeX table output.
    tab = Path(args.tex_tab_out)
    tab.parent.mkdir(parents=True, exist_ok=True)

    lines = [
        "% Auto-generated; do not edit by hand.",
        "\\begin{table}[H]",
        "\\centering",
        "\\scriptsize",
        "\\setlength{\\tabcolsep}{6pt}",
        "\\caption{Nearest complex singularity in the completed log variable $\\theta=\\log u$ on the unit-circle twist "
        "($u=e^{it}$ so $\\theta=it$), and its image under the half-angle compression $x=\\tan(\\theta/2)$. "
        "The modulus $|x_\\star|$ controls the true analytic disk for local expansions organized in $x$ around $x=0$.}",
        "\\label{tab:sync_kernel_hatdelta_nearest_complex_branch_point_tan_half_angle}",
        "\\begin{tabular}{r r r r}",
        "\\toprule",
        "$t_\\star$ & $\\theta_\\star=it_\\star$ & $x_\\star=\\tan(\\theta_\\star/2)$ & $|x_\\star|$\\\\",
        "\\midrule",
        f"${out.t_re} \\pm {out.t_im_abs}\\,i$ & "
        f"${out.theta_re} \\pm {out.theta_im_abs}\\,i$ & "
        f"${out.x_re} \\pm {out.x_im_abs}\\,i$ & "
        f"${out.x_abs}$\\\\",
        "\\bottomrule",
        "\\end{tabular}",
        "\\end{table}",
    ]
    tab.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[hatdelta-tan-half-angle] wrote {tab}", flush=True)
    print("[hatdelta-tan-half-angle] done", flush=True)


if __name__ == "__main__":
    main()

