#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute elimination certificates for primitive elements across S5 quintic fields.

This script is English-only by repository convention.

We certify (by explicit integer-coefficient eliminations):
  - The degree-25 minimal polynomial candidate for theta = alpha + beta,
    where alpha is a root of p_7(x) and beta is a root of Q_5(y).
  - The degree-125 minimal polynomial candidate for Theta = theta + gamma,
    where gamma is a root of B_5(delta).

The manuscript proves primitivity abstractly (linear disjointness + 2-transitivity),
and this script records a fully explicit integer polynomial certificate for auditing.

Outputs:
  - artifacts/export/pom_xi_s5_primitive_element_minpoly_certificate.json
  - artifacts/export/pom_xi_s5_primitive_element_minpoly_certificate.txt
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _primitive_ZZ_poly(P: sp.Poly) -> sp.Poly:
    """Normalize an integer poly to primitive content with positive leading coefficient."""
    if P.is_zero:
        raise ValueError("zero polynomial")
    # Use SymPy's primitive-part normalization to avoid accidental floor-division.
    _content, prim = P.primitive()
    prim = sp.Poly(prim.as_expr(), prim.gens[0], domain=sp.ZZ)
    if int(prim.LC()) < 0:
        prim = -prim
    return prim


def _poly_stats(P: sp.Poly) -> Dict[str, object]:
    coeffs = [int(c) for c in P.all_coeffs()]
    max_abs = max(abs(c) for c in coeffs) if coeffs else 0
    return {
        "degree": int(P.degree()),
        "n_coeffs": int(len(coeffs)),
        "lc": int(P.LC()),
        "content_gcd": int(sp.gcd_list(coeffs)),
        "max_abs_coeff": int(max_abs),
        "max_abs_coeff_bits": int(max_abs.bit_length() if max_abs else 0),
        "squarefree": bool(sp.gcd(P, P.diff()).degree() == 0),
    }


def _resultant_sum_degree25(*, x: sp.Symbol, t: sp.Symbol) -> Tuple[sp.Poly, sp.Poly]:
    """
    Compute Res_x(p7(x), Q5(t-x)) as a Z[t]-polynomial (primitive normalized).
    Returns (raw_poly, primitive_poly).
    """
    y = sp.Symbol("y")

    p7 = sp.Poly(x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2, x, domain=sp.ZZ)
    Q5 = sp.Poly(
        4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80,
        y,
        domain=sp.ZZ,
    )

    expr = sp.resultant(p7.as_expr(), sp.expand(Q5.as_expr().subs(y, t - x)), x)
    raw = sp.Poly(sp.expand(expr), t, domain=sp.ZZ)
    prim = _primitive_ZZ_poly(raw)
    return raw, prim


def _resultant_sum_degree125(*, s: sp.Symbol, t: sp.Symbol, minpoly_theta25: sp.Poly) -> Tuple[sp.Poly, sp.Poly]:
    """
    Given a primitive Z[s]-polynomial m25(s) for theta, compute Res_s(m25(s), B5(t-s)).
    Returns (raw_poly, primitive_poly) in Z[t].
    """
    delta = sp.Symbol("delta")
    B5 = sp.Poly(
        50000 * delta**5
        + 136112 * delta**4
        + 60776 * delta**3
        - 26712 * delta**2
        + 38961 * delta
        + 35964,
        delta,
        domain=sp.ZZ,
    )

    expr = sp.resultant(minpoly_theta25.as_expr(), sp.expand(B5.as_expr().subs(delta, t - s)), s)
    raw = sp.Poly(sp.expand(expr), t, domain=sp.ZZ)
    prim = _primitive_ZZ_poly(raw)
    return raw, prim


@dataclass(frozen=True)
class Certificate:
    name: str
    poly_variable: str
    stats: Dict[str, object]
    coeffs_high_to_low: List[int]


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute elimination minpoly certificates for S5 primitive elements.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(export_dir() / "pom_xi_s5_primitive_element_minpoly_certificate.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--out-txt",
        type=str,
        default=str(export_dir() / "pom_xi_s5_primitive_element_minpoly_certificate.txt"),
        help="Output text path (human-readable polynomial dump).",
    )
    args = parser.parse_args()

    x = sp.Symbol("x")
    t = sp.Symbol("t")

    print("[pom-xi-s5-primitive-element-minpoly] start", flush=True)

    raw25, prim25_t = _resultant_sum_degree25(x=x, t=t)
    # Work with a separate symbol s for the second resultant to avoid accidental captures.
    s = sp.Symbol("s")
    prim25_s = sp.Poly(prim25_t.as_expr().subs(t, s), s, domain=sp.ZZ)

    raw125, prim125_t = _resultant_sum_degree125(s=s, t=t, minpoly_theta25=prim25_s)

    certs: List[Certificate] = [
        Certificate(
            name="theta = alpha + beta (p7 + Q5)",
            poly_variable=str(t),
            stats=_poly_stats(prim25_t),
            coeffs_high_to_low=[int(c) for c in prim25_t.all_coeffs()],
        ),
        Certificate(
            name="Theta = alpha + beta + gamma (p7 + Q5 + B5)",
            poly_variable=str(t),
            stats=_poly_stats(prim125_t),
            coeffs_high_to_low=[int(c) for c in prim125_t.all_coeffs()],
        ),
    ]

    payload: Dict[str, object] = {
        "certificates": [asdict(c) for c in certs],
        "raw_stats": {
            "deg25_raw": _poly_stats(raw25),
            "deg125_raw": _poly_stats(raw125),
        },
        "polynomials": {
            "p7_x": "x^5 - 2*x^4 - 7*x^3 - 2*x + 2",
            "Q5_y": "4096*y^5 + 5376*y^4 - 464*y^3 - 2749*y^2 - 723*y + 80",
            "B5_delta": "50000*delta^5 + 136112*delta^4 + 60776*delta^3 - 26712*delta^2 + 38961*delta + 35964",
        },
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
    }

    out_json = Path(args.out_json)
    out_txt = Path(args.out_txt)

    _write_json(out_json, payload)

    # Text dump: keep it deterministic and easy to grep/parse.
    lines: List[str] = []
    lines.append("pom_xi_s5_primitive_element_minpoly_certificate")
    lines.append("")
    lines.append("== theta25 (primitive, integer coefficients) ==")
    lines.append(str(prim25_t.as_expr()))
    lines.append("")
    lines.append("== Theta125 (primitive, integer coefficients) ==")
    lines.append(str(prim125_t.as_expr()))
    lines.append("")
    _write_text(out_txt, "\n".join(lines) + "\n")

    # Lightweight assertions: degrees and squarefreeness (avoid expensive factoring).
    assert int(prim25_t.degree()) == 25, "theta resultant does not have degree 25"
    assert int(prim125_t.degree()) == 125, "Theta resultant does not have degree 125"
    assert bool(sp.gcd(prim25_t, prim25_t.diff()).degree() == 0), "theta polynomial is not squarefree"
    assert bool(sp.gcd(prim125_t, prim125_t.diff()).degree() == 0), "Theta polynomial is not squarefree"

    print(f"[pom-xi-s5-primitive-element-minpoly] wrote {out_json}", flush=True)
    print(f"[pom-xi-s5-primitive-element-minpoly] wrote {out_txt}", flush=True)


if __name__ == "__main__":
    main()

