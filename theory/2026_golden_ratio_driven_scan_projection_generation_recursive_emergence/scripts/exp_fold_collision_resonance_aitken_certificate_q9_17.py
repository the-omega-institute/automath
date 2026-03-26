#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Aitken certificate fingerprints from resonance-region Fold collision moment polynomials (q=9..17).

We start from the audited exact integer recurrences for S_q(m) in the form:
  S(m) = sum_{i=1..d} c_i S(m-i),
which induces the characteristic polynomial
  P_q(λ) = λ^d - c_1 λ^{d-1} - ... - c_d.

For each q in 9..17 we compute all roots of P_q and sort them by modulus:
  - λ1 = r_q  : Perron root (dominant, positive real)
  - λ2        : 2nd-largest modulus root (empirically negative real in this window)
  - λ3        : 3rd-largest modulus root

We export two root-ratio fingerprints useful for ratio/Aitken convergence audits:
  - sigma_osc := |λ2| / r_q  (dominant alternating error strength)
  - delta_ait := |λ3| / r_q  (post-Aitken error strength)

Outputs:
  - artifacts/export/fold_collision_resonance_aitken_certificate_q9_17.json
  - sections/generated/tab_fold_collision_resonance_aitken_certificate_q9_17.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17


def _poly_from_coeffs(coeffs: List[int]) -> sp.Expr:
    d = len(coeffs)
    lam = sp.Symbol("lambda")
    poly = lam**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * lam ** (d - i)
    return sp.expand(poly)


def _roots(poly: sp.Expr, *, dps: int) -> List[complex]:
    roots = sp.nroots(poly, n=int(dps), maxsteps=600)
    out: List[complex] = []
    for r in roots:
        re = float(sp.re(r).evalf(dps))
        im = float(sp.im(r).evalf(dps))
        out.append(complex(re, im))
    return out


def _is_real(z: complex, *, tol: float) -> bool:
    return abs(z.imag) <= tol


def _canon(z: complex, *, tol: float) -> complex:
    """Canonicalize a root for deterministic printing."""
    if _is_real(z, tol=tol):
        return complex(float(z.real), 0.0)
    if z.imag > 0:
        return z.conjugate()
    return z


def _sort_by_modulus(roots: List[complex], *, tol: float) -> List[complex]:
    rr = [_canon(z, tol=tol) for z in roots]
    # Primary: modulus (descending). Secondary: prefer real roots. Tertiary: real part (descending).
    return sorted(rr, key=lambda z: (-abs(z), abs(z.imag), -z.real, -z.imag))


def _as_json_complex(z: complex) -> Dict[str, float]:
    return {"re": float(z.real), "im": float(z.imag)}


@dataclass(frozen=True)
class Row:
    q: int
    order_d: int
    r_q: float
    lambda2: Dict[str, float]
    lambda3: Dict[str, float]
    abs_lambda2: float
    abs_lambda3: float
    sigma_osc: float
    delta_ait: float
    lambda2_is_negative_real: bool
    lambda3_is_real: bool


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{Aitken-certificate root fingerprints for resonance-region Fold collision moment "
        "characteristic polynomials $P_q$ (audited recurrences, $q=9,\\dots,17$). "
        "Roots are sorted by modulus: $\\lambda_1=r_q$ (Perron root), $\\lambda_2$ (2nd), $\\lambda_3$ (3rd). "
        "We report $\\sigma_{\\mathrm{osc}}:=|\\lambda_2|/r_q$ (dominant alternating ratio-error strength) and "
        "$\\delta_{\\mathrm{ait}}:=|\\lambda_3|/r_q$ (post-Aitken error strength).}"
    )
    lines.append("\\label{tab:fold_collision_resonance_aitken_certificate_q9_17}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$q$ & order $d_q$ & $r_q$ & $\\lambda_2$ & $\\sigma_{\\mathrm{osc}}$ & $|\\lambda_3|$ & $\\delta_{\\mathrm{ait}}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        l2 = complex(r.lambda2["re"], r.lambda2["im"])
        l2_str = f"{l2.real:.6f}" if abs(l2.imag) < 1e-18 else f"{l2.real:.6f}{l2.imag:+.6f}\\,\\mathrm{{i}}"
        lines.append(
            f"{r.q} & {r.order_d} & {r.r_q:.6f} & {l2_str} & {r.sigma_osc:.4f} & {r.abs_lambda3:.6f} & {r.delta_ait:.4f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Compute Aitken-certificate root fingerprints for resonance-region polynomials (q=9..17)."
    )
    ap.add_argument("--dps", type=int, default=160, help="Decimal digits for sympy nroots.")
    ap.add_argument("--real-tol", type=float, default=1e-12, help="Imag tolerance for classifying real roots.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_resonance_aitken_certificate_q9_17.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_resonance_aitken_certificate_q9_17.tex"),
    )
    args = ap.parse_args()

    recs: List[Tuple[int, List[int]]] = []
    for rec in PRECOMPUTED_RECS_9_17:
        q = int(rec["k"])
        coeffs = [int(x) for x in rec["coeffs"]]
        recs.append((q, coeffs))
    recs = sorted(recs, key=lambda t: t[0])

    rows_out: List[Row] = []
    for q, coeffs in recs:
        poly = _poly_from_coeffs(coeffs)
        roots = _roots(poly, dps=int(args.dps))
        roots_sorted = _sort_by_modulus(roots, tol=float(args.real_tol))

        if len(roots_sorted) < 3:
            raise RuntimeError(f"Unexpected root count for q={q}: got {len(roots_sorted)}")

        lam1 = roots_sorted[0]
        if not _is_real(lam1, tol=float(args.real_tol)):
            raise RuntimeError(f"Dominant root is not (numerically) real for q={q}: {lam1}")
        if lam1.real <= 0:
            raise RuntimeError(f"Dominant root is not positive for q={q}: {lam1.real}")
        r_q = float(lam1.real)

        lam2 = roots_sorted[1]
        lam3 = roots_sorted[2]

        abs_l2 = float(abs(lam2))
        abs_l3 = float(abs(lam3))
        sigma_osc = abs_l2 / r_q
        delta_ait = abs_l3 / r_q

        l2_neg_real = _is_real(lam2, tol=float(args.real_tol)) and (lam2.real < 0)
        l3_real = _is_real(lam3, tol=float(args.real_tol))

        rows_out.append(
            Row(
                q=int(q),
                order_d=len(coeffs),
                r_q=r_q,
                lambda2=_as_json_complex(lam2),
                lambda3=_as_json_complex(lam3),
                abs_lambda2=abs_l2,
                abs_lambda3=abs_l3,
                sigma_osc=sigma_osc,
                delta_ait=delta_ait,
                lambda2_is_negative_real=bool(l2_neg_real),
                lambda3_is_real=bool(l3_real),
            )
        )

        l2_note = "neg-real" if l2_neg_real else "other"
        print(
            f"[aitken-cert] q={q:2d} d={len(coeffs):2d} r_q={r_q:.12f} "
            f"|l2|/r={sigma_osc:.6f} |l3|/r={delta_ait:.6f} (l2={l2_note})",
            flush=True,
        )

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps({"rows": [asdict(r) for r in rows_out]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"[aitken-cert] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    write_table_tex(tout, rows_out)
    print(f"[aitken-cert] wrote {tout}", flush=True)

    # Basic sanity: sigma and delta must lie in (0,1) for a strict spectral gap.
    for r in rows_out:
        if not (0.0 < r.sigma_osc < 1.0 and 0.0 < r.delta_ait < 1.0):
            raise RuntimeError(
                f"Bad ratio range for q={r.q}: sigma_osc={r.sigma_osc}, delta_ait={r.delta_ait}"
            )


if __name__ == "__main__":
    main()

