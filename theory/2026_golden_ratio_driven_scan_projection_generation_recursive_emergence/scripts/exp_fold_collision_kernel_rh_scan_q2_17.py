#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Kernel-RH spectral scan for Fold collision moment kernels (q=2..17).

For each integer q>=2, the collision moment sequence
  S_q(m) := sum_x d_m(x)^q
admits an audited exact integer recurrence in the form
  S(m) = sum_{i=1..d} c_i S(m-i).
The associated characteristic polynomial is
  P_q(x) = x^d - c_1 x^{d-1} - ... - c_d.

We compute all roots of P_q numerically and define:
  r_q      := Perron root (dominant modulus; positive real),
  Lambda_q := subdominant spectral modulus (max |mu| over mu != r_q),
  R_q      := Lambda_q / sqrt(r_q)  (kernel-RH indicator; <=1 iff kernel RH),
  beta_q   := log Lambda_q / log r_q,
  delta_q  := log(Lambda_q^2 / r_q) = 2 log R_q  (Newman-like signed shift).

Outputs:
  - artifacts/export/fold_collision_kernel_rh_scan_q2_17.json
  - sections/generated/tab_fold_collision_kernel_rh_scan_q2_17.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Rec:
    q: int
    coeffs: List[int]  # S(m)=sum_{i=1..d} coeffs[i-1]*S(m-i)
    m0: int


# q=2..8: audited recurrences (see exp_fold_collision_moment_spectrum_k2_8.py)
RECS_2_8: List[Rec] = [
    Rec(q=2, coeffs=[2, 2, -2], m0=3),
    Rec(q=3, coeffs=[2, 4, -2], m0=3),
    Rec(q=4, coeffs=[2, 7, 0, 2, -2], m0=5),
    Rec(q=5, coeffs=[2, 11, 8, 20, -10], m0=5),
    Rec(q=6, coeffs=[2, 17, 28, 88, -26, 4, -4], m0=7),
    Rec(q=7, coeffs=[2, 26, 74, 311, -34, 84, -42], m0=7),
    Rec(q=8, coeffs=[2, 40, 174, 969, 2, 428, -174, 4, -4], m0=9),
]

# q=9..17: audited recurrences (see exp_fold_collision_moment_spectrum_k9_17.py)
RECS_9_17: List[Rec] = [
    Rec(q=9, m0=9, coeffs=[2, 62, 386, 2819, 62, 900, -450]),
    Rec(q=10, m0=11, coeffs=[2, 96, 830, 7945, 2, 1852, -830, 4, -4]),
    Rec(q=11, m0=11, coeffs=[2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174]),
    Rec(
        q=12,
        m0=15,
        coeffs=[2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8],
    ),
    Rec(
        q=13,
        m0=13,
        coeffs=[2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690],
    ),
    Rec(
        q=14,
        m0=15,
        coeffs=[2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8],
    ),
    Rec(
        q=15,
        m0=13,
        coeffs=[2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538],
    ),
    Rec(
        q=16,
        m0=15,
        coeffs=[2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8],
    ),
    Rec(
        q=17,
        m0=15,
        coeffs=[
            2,
            2599,
            125872,
            6569850,
            -96034590,
            -2764163954,
            -643026032,
            -15022392733,
            769974566,
            15329386299,
            642908352,
            1347896340,
            -673948170,
        ],
    ),
]


def _poly_from_coeffs(coeffs: List[int]) -> sp.Expr:
    d = len(coeffs)
    x = sp.Symbol("x")
    poly = x**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * x ** (d - i)
    return sp.expand(poly)


def _roots(poly: sp.Expr, *, dps: int) -> List[complex]:
    roots = sp.nroots(poly, n=int(dps), maxsteps=400)
    return [complex(sp.re(r).evalf(dps), sp.im(r).evalf(dps)) for r in roots]


def _perron_and_subdominant(roots: List[complex]) -> Tuple[float, float, complex, List[complex]]:
    roots_sorted = sorted(roots, key=lambda z: -abs(z))
    r = roots_sorted[0]
    if abs(r.imag) > 1e-16:
        raise RuntimeError(f"dominant root is not (numerically) real: {r}")
    if r.real <= 0:
        raise RuntimeError(f"dominant root is not positive: {r.real}")
    rq = float(r.real)

    tol = 1e-10
    others = [z for z in roots_sorted if abs(z - r) > tol]
    if not others:
        return rq, 0.0, 0.0 + 0.0j, roots_sorted

    mu_star = max(others, key=lambda z: abs(z))
    Lambda = float(abs(mu_star))
    return rq, Lambda, mu_star, roots_sorted


def _as_json_complex(z: complex) -> Dict[str, float]:
    return {"re": float(z.real), "im": float(z.imag)}


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Kernel-RH spectral scan for the Fold collision moment kernels $A_q$ "
        "(via their audited characteristic polynomials), $q=2,\\dots,17$. "
        "Here $r_q$ is the Perron root and $\\Lambda_q$ is the subdominant spectral modulus "
        "$\\max_{\\mu\\ne r_q}|\\mu|$. We report the kernel-RH indicator "
        "$R_q:=\\Lambda_q/\\sqrt{r_q}$, the pole-line exponent "
        "$\\beta_q:=\\log\\Lambda_q/\\log r_q$, and the signed shift "
        "$\\delta_q:=\\log(\\Lambda_q^2/r_q)=2\\log R_q$.}"
    )
    lines.append("\\label{tab:fold_collision_kernel_rh_scan_q2_17}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & order $d$ & $r_q$ & $\\Lambda_q$ & $R_q$ & $\\beta_q$ & $\\delta_q$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['q']} & {r['order']} & {r['r_q']:.12f} & {r['Lambda_q']:.12f} & {r['R_q']:.12f} "
            f"& {r['beta_q']:.12f} & {r['delta_q']:.12f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Kernel-RH scan for Fold collision moment kernels (q=2..17).")
    parser.add_argument("--dps", type=int, default=110, help="Precision (decimal digits) for root extraction.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_kernel_rh_scan_q2_17.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_kernel_rh_scan_q2_17.tex"),
    )
    args = parser.parse_args()

    recs: List[Rec] = [*RECS_2_8, *RECS_9_17]
    recs = sorted(recs, key=lambda r: r.q)

    rows: List[dict] = []
    for rec in recs:
        poly = _poly_from_coeffs(rec.coeffs)
        roots = _roots(poly, dps=int(args.dps))
        rq, Lambdaq, mu_star, roots_sorted = _perron_and_subdominant(roots)

        Rq = float("nan")
        betaq = float("nan")
        deltaq = float("nan")
        if Lambdaq > 0:
            Rq = Lambdaq / math.sqrt(rq)
            betaq = math.log(Lambdaq) / math.log(rq)
            deltaq = math.log((Lambdaq**2) / rq)

        rows.append(
            {
                "q": rec.q,
                "order": len(rec.coeffs),
                "m0": rec.m0,
                "coeffs": rec.coeffs,
                "r_q": rq,
                "Lambda_q": Lambdaq,
                "mu_star": _as_json_complex(mu_star),
                "R_q": Rq,
                "beta_q": betaq,
                "delta_q": deltaq,
                "roots_sorted_by_mod": [_as_json_complex(z) for z in roots_sorted],
            }
        )
        print(
            f"[kernel-rh-scan] q={rec.q:2d} r={rq:.12f} Lambda={Lambdaq:.12f} R={Rq:.12f} "
            f"beta={betaq:.12f} delta={deltaq:.12f}",
            flush=True,
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[kernel-rh-scan] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[kernel-rh-scan] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

