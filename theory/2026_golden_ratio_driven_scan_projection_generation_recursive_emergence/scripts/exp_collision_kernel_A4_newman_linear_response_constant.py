#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the Newman-critical linear response constant c_* = delta'(t_*) for the A4(t) kernel family.

This script is English-only by repository convention.

Context (paper-local):
  - In parts/subsec__pom-s4.tex (Remark rem:pom-collision-rh-break-a4-threshold),
    the Newman-critical threshold is parameterized by the unique positive real root z_*>1 of

      Z_4(z) = z^8 - 2 z^6 - 2 z^5 - 2 z^4 - 2 z^3 - 2,

    and the edge-weight parameter is

      t(z) = z^2 + 2z - 2/z^2 - 2/z^3.

  - Define p_t(x) = x^5 - 2x^4 - t x^3 - 2x + 2. At the threshold:
      y_* = -z_* is the worst negative real root and r_* = z_*^2 is the Perron root,
      hence delta(t) = log(Lambda(t)^2/r(t)) equals 0 at t=t_*.

This script audits:
  - The closed-form rational expression for c_* in terms of z_*.
  - The degree-8 minimal polynomial of c_* in Z[c], by eliminating z between Z_4(z)=0 and c=f(z).
  - The real embedding split: exactly two real roots (c_+ and c_-).

Outputs:
  - artifacts/export/collision_kernel_A4_newman_linear_response_constant.json
  - sections/generated/eq_collision_kernel_A4_newman_linear_response_constant.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    z_star: str
    t_star: str
    c_star: str
    c_star_via_implicit_diff: str
    c_star_matches: bool
    minpoly_c: str
    minpoly_c_coeffs_desc: List[int]
    minpoly_c_degree: int
    num_real_roots: int
    real_roots: List[str]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Newman-critical linear response constant c_* for A4(t).")
    parser.add_argument("--dps", type=int, default=120, help="Decimal precision for nroots (default: 120).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 80:
        raise SystemExit("Require --dps >= 80 for stable outputs.")

    t0 = time.time()
    print("[A4-newman-linear-response] start", flush=True)

    z = sp.Symbol("z")
    c = sp.Symbol("c")

    Z4 = sp.Poly(z**8 - 2 * z**6 - 2 * z**5 - 2 * z**4 - 2 * z**3 - 2, z)

    # z_*: unique positive real root > 1.
    z_roots = sp.nroots(Z4.as_expr(), n=dps, maxsteps=200)
    z_star = None
    for r in z_roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)) and float(sp.re(r)) > 1.0:
            z_star = sp.N(sp.re(r), dps)
            break
    if z_star is None:
        raise RuntimeError("Failed to locate z_*>1 real root of Z_4.")

    # t(z) parameterization (paper-local convention).
    t_expr = z**2 + 2 * z - 2 / z**2 - 2 / z**3
    t_star = sp.N(t_expr.subs({z: z_star}), dps)

    # c(z) closed form (paper-local statement).
    num = z**3 * (3 * z**8 + 3 * z**7 - 6 * z**4 - 7 * z**3 + 8 * z**2 - 10)
    den = 2 * (z**5 + z**4 + 2 * z + 3) * (2 * z**8 + 2 * z**7 - 2 * z**4 - 2 * z**3 + 4 * z**2 - 5)
    c_expr = sp.together(num / den)
    c_star = sp.N(c_expr.subs({z: z_star}), dps)

    # Independent audit: c_* = delta'(t_*) via implicit differentiation on p_t(x).
    x, t = sp.symbols("x t")
    p = x**5 - 2 * x**4 - t * x**3 - 2 * x + 2
    p_x = sp.diff(p, x)

    y_star = -z_star
    r_star = z_star**2

    # root derivative: x'(t) = x^3 / p_t'(x)
    y_prime = sp.N((y_star**3) / p_x.subs({x: y_star, t: t_star}), dps)
    r_prime = sp.N((r_star**3) / p_x.subs({x: r_star, t: t_star}), dps)

    c_star_alt = sp.N(2 * y_prime / y_star - r_prime / r_star, dps)
    c_match = bool(abs(c_star_alt - c_star) < sp.Float(10) ** (-(dps // 2 - 10)))

    # Minimal polynomial of c_* by elimination: Res_z(Z4(z), num - c*den) in Z[c].
    poly2 = sp.Poly(sp.expand(num - c * den), z)
    Res = sp.resultant(Z4, poly2, z)
    minpoly = sp.Poly(Res, c)
    if minpoly.degree() != 8:
        raise RuntimeError(f"Unexpected degree for resultant minpoly: got {minpoly.degree()}, expected 8.")
    # Normalize to primitive integer polynomial with positive leading coefficient.
    minpoly = sp.Poly(sp.expand(minpoly.as_expr()), c, domain="ZZ")
    if int(minpoly.LC()) < 0:
        minpoly = sp.Poly(-minpoly.as_expr(), c, domain="ZZ")

    # Real roots of minpoly.
    roots_c = minpoly.nroots(n=dps, maxsteps=200)
    real_roots = [r for r in roots_c if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2))]
    real_roots_sorted = sorted([sp.N(sp.re(r), dps) for r in real_roots], key=lambda rr: float(rr))

    payload = Payload(
        z_star=sp.sstr(z_star),
        t_star=sp.sstr(t_star),
        c_star=sp.sstr(c_star),
        c_star_via_implicit_diff=sp.sstr(c_star_alt),
        c_star_matches=bool(c_match),
        minpoly_c=sp.sstr(minpoly.as_expr()),
        minpoly_c_coeffs_desc=[int(cc) for cc in minpoly.all_coeffs()],
        minpoly_c_degree=int(minpoly.degree()),
        num_real_roots=int(len(real_roots_sorted)),
        real_roots=[sp.sstr(rr) for rr in real_roots_sorted],
    )

    if not args.no_output:
        out_json = export_dir() / "collision_kernel_A4_newman_linear_response_constant.json"
        _write_json(out_json, asdict(payload))

        # Optional TeX snippet for auditing.
        c_plus = float(real_roots_sorted[-1])  # positive small root
        c_minus = float(real_roots_sorted[0])  # negative large root
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_collision_kernel_A4_newman_linear_response_constant.py",
                "\\[",
                f"z_\\star\\approx {float(z_star):.16f},\\qquad t_\\star\\approx {float(t_star):.16f}.",
                "\\]",
                "\\[",
                f"c_\\star\\approx {float(c_star):.16f}.",
                "\\]",
                "\\[",
                sp.latex(minpoly.as_expr()) + "=0.",
                "\\]",
                "\\[",
                f"c_+\\approx {c_plus:.10f},\\qquad c_-\\approx {c_minus:.10f}.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_collision_kernel_A4_newman_linear_response_constant.tex"
        _write_text(out_tex, tex)

        print(f"[A4-newman-linear-response] wrote {out_json}", flush=True)
        print(f"[A4-newman-linear-response] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(
        "[A4-newman-linear-response] checks:"
        f" c_match={c_match} deg={minpoly.degree()} real_roots={len(real_roots_sorted)} seconds={dt:.3f}",
        flush=True,
    )
    print("[A4-newman-linear-response] done", flush=True)


if __name__ == "__main__":
    main()

