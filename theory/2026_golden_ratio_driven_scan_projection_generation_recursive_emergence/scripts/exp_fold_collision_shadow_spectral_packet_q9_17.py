#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Shadow spectral packet scan for resonance-region Fold collision moments (q=9..17).

We work with the audited exact integer recurrences for S_q(m) in the form:
  S(m) = sum_{i=1..d} c_i S(m-i),
which induces the characteristic polynomial
  P_q(x) = x^d - c_1 x^{d-1} - ... - c_d.

For each q in 9..17 we compute all roots of P_q and extract a stable "packet":
  - r_q         : Perron root (dominant, positive real)
  - lambda_q^-  : outermost negative real root (most negative real root)
  - mu_q        : maximum-modulus nonreal root (we choose Im(mu_q) <= 0 by convention)

We report ratios relative to r_{q-2} and a Dirichlet real coordinate
  sigma_q(mu) := log|mu| / log r_q  (= Re(s) in the s-plane pole dictionary).

Outputs:
  - artifacts/export/fold_collision_shadow_spectral_packet_q9_17.json
  - sections/generated/tab_fold_collision_shadow_spectral_packet_q9_17.tex

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


# q=2..8: audited recurrences (see exp_fold_collision_kernel_rh_scan_q2_17.py)
RECS_2_8: List[Rec] = [
    Rec(q=2, coeffs=[2, 2, -2], m0=3),
    Rec(q=3, coeffs=[2, 4, -2], m0=3),
    Rec(q=4, coeffs=[2, 7, 0, 2, -2], m0=5),
    Rec(q=5, coeffs=[2, 11, 8, 20, -10], m0=5),
    Rec(q=6, coeffs=[2, 17, 28, 88, -26, 4, -4], m0=7),
    Rec(q=7, coeffs=[2, 26, 74, 311, -34, 84, -42], m0=7),
    Rec(q=8, coeffs=[2, 40, 174, 969, 2, 428, -174, 4, -4], m0=9),
]

# q=9..17: audited recurrences (see tab_fold_collision_moment_recursions_9_17)
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


def _perron_root(roots: List[complex]) -> float:
    z = max(roots, key=lambda w: abs(w))
    if abs(z.imag) > 1e-10:
        raise RuntimeError(f"dominant root is not (numerically) real: {z}")
    if z.real <= 0:
        raise RuntimeError(f"dominant root is not positive: {z.real}")
    return float(z.real)


def _outermost_negative_real_root(roots: List[complex]) -> float:
    tol = 1e-10
    neg_reals = [z for z in roots if abs(z.imag) <= tol and z.real < -tol]
    if not neg_reals:
        raise RuntimeError("no negative real roots found")
    # Outermost negative real root = most negative real root.
    z = min(neg_reals, key=lambda w: w.real)
    return float(z.real)


def _max_mod_nonreal_root(roots: List[complex]) -> complex:
    tol = 1e-10
    nonreals = [z for z in roots if abs(z.imag) > tol]
    if not nonreals:
        raise RuntimeError("no nonreal roots found")
    z = max(nonreals, key=lambda w: abs(w))
    if z.imag > 0:
        z = z.conjugate()
    return z


def _sigma(modulus: float, rq: float) -> float:
    return math.log(modulus) / math.log(rq)


def _as_json_complex(z: complex) -> Dict[str, float]:
    return {"re": float(z.real), "im": float(z.imag)}


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{Shadow spectral packet for resonance-region Fold collision moment polynomials $P_q$ "
        "($q=9,\\dots,17$) reconstructed from audited integer recurrences. "
        "Here $r_q$ is the Perron root; $\\lambda_q^{-}<0$ is the outermost negative real root; "
        "$\\mu_q$ is the maximum-modulus nonreal root (chosen with $\\Im(\\mu_q)\\le 0$). "
        "We report the shadow ratios $|\\mu_q|/r_{q-2}$ and $|\\lambda_q^-|/r_{q-2}$, the angle "
        "$\\arg(\\mu_q)$ (radians), and the Dirichlet real coordinate "
        "$\\sigma_q(\\mu_q):=\\log|\\mu_q|/\\log r_q$.}"
    )
    lines.append("\\label{tab:fold_collision_shadow_spectral_packet_q9_17}")
    lines.append("\\begin{tabular}{r r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$q$ & $r_q$ & $\\lambda_q^{-}$ & $|\\mu_q|$ & $\\arg(\\mu_q)$ & "
        "$|\\mu_q|/r_{q-2}$ & $|\\lambda_q^-|/r_{q-2}$ & $\\sigma_q(\\mu_q)$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['q']} & {r['r_q']:.6f} & {r['lambda_minus']:.6f} & {r['mu_mod']:.6f} & "
            f"{r['mu_arg']:.4f} & {r['mu_over_r_qm2']:.4f} & {r['abs_lambda_over_r_qm2']:.4f} & "
            f"{r['sigma_mu']:.4f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Shadow spectral packet scan for Fold collision moment polynomials (q=9..17)."
    )
    parser.add_argument("--dps", type=int, default=140, help="Decimal digits for sympy nroots.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_shadow_spectral_packet_q9_17.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_shadow_spectral_packet_q9_17.tex"),
    )
    args = parser.parse_args()

    recs_all: List[Rec] = [*RECS_2_8, *RECS_9_17]
    recs_all = sorted(recs_all, key=lambda r: r.q)

    # Precompute Perron roots for q=2..17 (needed for r_{q-2} ratios).
    r_map: Dict[int, float] = {}
    roots_map: Dict[int, List[complex]] = {}
    for rec in recs_all:
        poly = _poly_from_coeffs(rec.coeffs)
        roots = _roots(poly, dps=int(args.dps))
        rq = _perron_root(roots)
        r_map[rec.q] = rq
        roots_map[rec.q] = roots
        print(f"[shadow-packet] precompute q={rec.q:2d} r_q={rq:.12f}", flush=True)

    rows: List[dict] = []
    for q in range(9, 18):
        roots = roots_map[q]
        rq = r_map[q]
        rqm2 = r_map[q - 2]

        lam_minus = _outermost_negative_real_root(roots)
        mu = _max_mod_nonreal_root(roots)

        mu_mod = float(abs(mu))
        mu_arg = float(math.atan2(mu.imag, mu.real))

        rows.append(
            {
                "q": q,
                "order": len(next(r.coeffs for r in recs_all if r.q == q)),
                "r_q": rq,
                "r_qm2": rqm2,
                "lambda_minus": lam_minus,
                "abs_lambda_minus": float(abs(lam_minus)),
                "mu": _as_json_complex(mu),
                "mu_mod": mu_mod,
                "mu_arg": mu_arg,
                "mu_over_r_qm2": mu_mod / rqm2,
                "abs_lambda_over_r_qm2": abs(lam_minus) / rqm2,
                "sigma_mu": _sigma(mu_mod, rq),
                "sigma_lambda_minus": _sigma(abs(lam_minus), rq),
            }
        )

        print(
            f"[shadow-packet] q={q:2d} r_q={rq:.6f} lambda^-={lam_minus:.6f} |mu|={mu_mod:.6f} "
            f"arg(mu)={mu_arg:.4f} |mu|/r_{q-2}={mu_mod/rqm2:.4f} |lambda|/r_{q-2}={abs(lam_minus)/rqm2:.4f} "
            f"sigma_mu={_sigma(mu_mod, rq):.4f}",
            flush=True,
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[shadow-packet] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[shadow-packet] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

