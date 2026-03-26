#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the y-image of E[4]\\E[2] under the weight map y on E.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

Let Pi(X,y) be the induced quartic spectral curve equation (eliminating Y):
  Pi(X,y) := X^4 - X^3 - (2y+1) X^2 + X + y(y+1) = 0.

Let N6(X) be the (x-coordinate) 4-division certificate polynomial coming from the
critical sextic for the doubling Lattès map:
  N6(X) := 2X^6 - 10X^4 + 10X^3 - 10X^2 + 2X + 1.

Then the y-values of E[4]\\E[2] are exactly the roots of the degree-12 polynomial
  Q4(y) := Res_X(N6(X), Pi(X,y)).

We compute Q4(y), verify its coefficients against the paper statement, and compute
Disc(Q4) with integer factorization.

Outputs:
  - artifacts/export/fold_zm_elliptic_4division_weight_image_audit.json
  - sections/generated/eq_fold_zm_elliptic_4division_weight_image_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _squarefree_part_from_factorint(sign: int, fac: Dict[int, int]) -> int:
    out = sign
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


def _format_factorization_latex(sign: int, fac: Dict[int, int]) -> str:
    if sign == -1:
        parts: List[str] = ["-1"]
    else:
        parts = []
    for p in sorted(fac.keys()):
        e = fac[p]
        if e == 1:
            parts.append(f"{p}")
        else:
            parts.append(f"{p}^{{{e}}}")
    return r"\cdot ".join(parts) if parts else "1"


@dataclass(frozen=True)
class Payload:
    q4_degree: int
    q4_leading_coeff: int
    q4_coeffs_high_to_low: List[int]
    q4_matches_expected: bool
    q4_factor_degrees_over_Q: List[int]
    q4_irreducible_over_Q: bool
    q4_factor_mod37: str
    q4_mod37_matches_expected: bool
    disc_q4: int
    disc_q4_sign: int
    disc_q4_factorization: Dict[str, int]
    disc_q4_squarefree_part: int
    disc_q4_matches_expected: bool


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Q4(y) = Res_X(N6(X), Pi(X,y)) and Disc(Q4).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-4div-weight-image] start", flush=True)

    X, y = sp.symbols("X y")
    Pi = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)
    N6 = 2 * X**6 - 10 * X**4 + 10 * X**3 - 10 * X**2 + 2 * X + 1

    # Resultant in X, then primitive normalization in Z[y].
    res = sp.resultant(N6, Pi, X)
    Q4 = sp.Poly(sp.expand(res), y, domain=sp.ZZ)
    _content, Q4 = Q4.primitive()
    if Q4.LC() < 0:
        Q4 = -Q4

    coeffs = [int(c) for c in Q4.all_coeffs()]
    expected_coeffs = [
        16,
        -224,
        800,
        2832,
        -5912,
        -46784,
        -59144,
        -9656,
        29776,
        27576,
        6468,
        312,
        -725,
    ]
    matches_expected = coeffs == expected_coeffs

    # Factorization over Q for irreducibility.
    _c, factors = sp.factor_list(sp.Poly(Q4.as_expr(), y, domain=sp.QQ))
    factor_degrees = sorted([int(f.degree()) for (f, _e) in factors])
    irreducible = len(factors) == 1 and factor_degrees == [12]

    # Mod-37 factorization (bad prime collapse diagnostic).
    Q4_mod37 = sp.Poly(Q4.as_expr(), y, modulus=37)
    q4_factor_mod37 = str(sp.factor(Q4_mod37.as_expr(), modulus=37))
    expected_mod37 = 16 * (y - 6) ** 10 * (y**2 + 9 * y + 6)
    expected_mod37_poly = sp.Poly(expected_mod37, y, modulus=37)
    mod37_matches_expected = Q4_mod37 == expected_mod37_poly

    # Discriminant and its integer factorization.
    disc = int(sp.discriminant(Q4.as_expr(), y))
    disc_sign = -1 if disc < 0 else 1
    disc_abs = abs(disc)
    fac = sp.factorint(disc_abs)
    sqfree = _squarefree_part_from_factorint(disc_sign, {int(p): int(e) for p, e in fac.items()})

    expected_disc = (2**56) * (37**23) * (59**6) * (652225136287**2)
    disc_matches_expected = disc == expected_disc

    payload = Payload(
        q4_degree=int(Q4.degree()),
        q4_leading_coeff=int(Q4.LC()),
        q4_coeffs_high_to_low=coeffs,
        q4_matches_expected=bool(matches_expected),
        q4_factor_degrees_over_Q=factor_degrees,
        q4_irreducible_over_Q=bool(irreducible),
        q4_factor_mod37=q4_factor_mod37,
        q4_mod37_matches_expected=bool(mod37_matches_expected),
        disc_q4=int(disc),
        disc_q4_sign=int(disc_sign),
        disc_q4_factorization={str(int(p)): int(e) for p, e in fac.items()},
        disc_q4_squarefree_part=int(sqfree),
        disc_q4_matches_expected=bool(disc_matches_expected),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_4division_weight_image_audit.json"
        _write_json(out_json, asdict(payload))

        poly_latex = sp.latex(Q4.as_expr())
        disc_latex = (
            r"2^{56}\cdot 37^{23}\cdot 59^{6}\cdot(652225136287)^{2}"
            if disc_matches_expected and disc_sign == 1
            else _format_factorization_latex(disc_sign, {int(p): int(e) for p, e in fac.items()})
        )

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_elliptic_4division_weight_image_audit.py",
                "\\[",
                f"T_{{4}}(y)={poly_latex}.",
                "\\]",
                "\\[",
                f"\\operatorname{{Disc}}\\!\\bigl(T_{{4}}\\bigr)={disc_latex}.",
                "\\]",
                "\\[",
                (
                    r"T_{4}(y)\equiv 16\,(y-6)^{10}\,(y^{2}+9y+6)\ (\mathrm{mod}\ 37)."
                    if mod37_matches_expected
                    else rf"T_{{4}}(y)\equiv {sp.latex(sp.factor(Q4_mod37.as_expr(), modulus=37))}\ (\mathrm{{mod}}\ 37)."
                ),
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_elliptic_4division_weight_image_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-elliptic-4div-weight-image] wrote {out_json}", flush=True)
        print(f"[fold-zm-elliptic-4div-weight-image] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-4div-weight-image] checks:"
        f" deg={Q4.degree()} lc={Q4.LC()} match_poly={matches_expected} irreducible={irreducible}"
        f" disc_match={disc_matches_expected} sqfree={sqfree} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-4div-weight-image] done", flush=True)


if __name__ == "__main__":
    main()

