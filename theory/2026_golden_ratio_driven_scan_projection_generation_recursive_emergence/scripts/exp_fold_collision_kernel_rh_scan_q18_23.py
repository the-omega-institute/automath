#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Kernel-RH spectral scan for Fold collision moment kernels (q=18..23).

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
  delta_q  := log(Lambda_q^2 / r_q) = 2 log R_q.

Outputs:
  - artifacts/export/fold_collision_kernel_rh_scan_q18_23.json
  - sections/generated/tab_fold_collision_kernel_rh_scan_q18_23.tex

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


# Precomputed, audited recurrences (audit window m<=35).
# Derived and exported by scripts/exp_fold_collision_moment_signature_q18_25.py.
RECS_18_23: List[Rec] = [
    Rec(
        q=18,
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
        q=19,
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
        q=20,
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
        q=21,
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
        q=22,
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
        q=23,
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


def _poly_from_coeffs(coeffs: List[int]) -> sp.Expr:
    d = len(coeffs)
    x = sp.Symbol("x")
    # Coefficients for x^d - c1 x^{d-1} - ... - cd.
    cs = [1] + [-int(c) for c in coeffs]
    return sp.Poly.from_list(cs, gens=x, domain=sp.ZZ).as_expr()


def _roots(poly: sp.Expr, *, dps: int) -> List[complex]:
    roots = sp.nroots(poly, n=int(dps), maxsteps=700)
    return [complex(r) for r in roots]


def _perron_and_subdominant(roots: List[complex]) -> Tuple[float, float, complex, List[complex]]:
    roots_sorted = sorted(roots, key=lambda z: -abs(z))
    r = roots_sorted[0]
    if abs(r.imag) > 1e-14:
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
        "(via their audited characteristic polynomials), $q=18,\\dots,23$. "
        "Here $r_q$ is the Perron root and $\\Lambda_q$ is the subdominant spectral modulus "
        "$\\max_{\\mu\\ne r_q}|\\mu|$. We report the kernel-RH indicator "
        "$R_q:=\\Lambda_q/\\sqrt{r_q}$, the pole-line exponent "
        "$\\beta_q:=\\log\\Lambda_q/\\log r_q$, and the signed shift "
        "$\\delta_q:=\\log(\\Lambda_q^2/r_q)=2\\log R_q$.}"
    )
    lines.append("\\label{tab:fold_collision_kernel_rh_scan_q18_23}")
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
    ap = argparse.ArgumentParser(description="Kernel-RH scan for Fold collision moment kernels (q=18..23).")
    ap.add_argument("--dps", type=int, default=150, help="Precision (decimal digits) for root extraction.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_kernel_rh_scan_q18_23.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_kernel_rh_scan_q18_23.tex"),
    )
    args = ap.parse_args()

    rows: List[dict] = []
    for rec in RECS_18_23:
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

