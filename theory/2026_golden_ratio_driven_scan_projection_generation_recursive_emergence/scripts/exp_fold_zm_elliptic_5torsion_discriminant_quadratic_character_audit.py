#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the 5-division weight elimination polynomial and discriminant class.

This script is English-only by repository convention.

Model:
  E: Y^2 = X^3 - X + 1/4
  y := X^2 + Y - 1/2
  Pi(X,y) := X^4 - X^3 - (2y+1)X^2 + X + y(y+1)

Definition:
  L_5(y) := Res_X(psi_5(X), Pi(X,y)) in Z[y],
  where psi_5 is the short-Weierstrass 5-division polynomial in X.

Certifications:
  - degree/irreducibility of L_5 over Q;
  - exact mod-37 factorization;
  - discriminant decomposition
      Disc(L_5) = 2^32 * 5^35 * 19^2 * 37^94 * D_5^2,
    hence squarefree class [Disc(L_5)]_sf = 5.

Outputs:
  - artifacts/export/fold_zm_elliptic_5torsion_discriminant_quadratic_character_audit.json
  - sections/generated/eq_fold_zm_elliptic_5torsion_discriminant_quadratic_character_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
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


def _normalize_primitive_ZZ(poly: sp.Poly, var: sp.Symbol) -> sp.Poly:
    if poly.domain != sp.ZZ:
        poly = sp.Poly(poly.as_expr(), var, domain=sp.ZZ)
    _content, prim = poly.primitive()
    if prim.LC() < 0:
        prim = -prim
    return prim


def _padic_valuation(n: int, p: int) -> Tuple[int, int]:
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e, n


@dataclass(frozen=True)
class Payload:
    l5_degree: int
    l5_leading_coeff: int
    l5_coeffs_high_to_low: List[int]
    l5_irreducible_over_Q: bool
    l5_mod37_matches_expected: bool
    disc_l5: int
    v2: int
    v5: int
    v19: int
    v37: int
    residual_square_part: int
    residual_is_square: bool
    residual_square_root: int
    decomposition_matches_expected: bool
    squarefree_class_disc_l5: int
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit L5(y) and Disc(L5) square class on the Lee--Yang elliptic model.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-5torsion-disc] start", flush=True)

    X, y = sp.symbols("X y")
    Pi = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)
    psi5 = (
        5 * X**12
        - 62 * X**10
        + 95 * X**9
        - 105 * X**8
        - 60 * X**7
        + 285 * X**6
        - 174 * X**5
        - 5 * X**4
        - 5 * X**3
        + 35 * X**2
        - 15 * X
        + 2
    )

    res5 = sp.resultant(psi5, Pi, X)
    L5 = _normalize_primitive_ZZ(sp.Poly(sp.expand(res5), y, domain=sp.ZZ), y)

    _c, factors_L5 = sp.factor_list(sp.Poly(L5.as_expr(), y, domain=sp.QQ))
    l5_irreducible = len(factors_L5) == 1 and int(factors_L5[0][0].degree()) == 24

    L5_mod37 = sp.Poly(L5.as_expr(), y, modulus=37)
    L5_mod37_expected = sp.Poly(-4 * (y - 6) ** 20 * (y**4 + y**3 + 10 * y**2 + 9 * y + 4), y, modulus=37)
    l5_mod37_matches_expected = L5_mod37 == L5_mod37_expected

    disc_l5 = int(sp.discriminant(L5.as_expr(), y))
    if disc_l5 <= 0:
        raise RuntimeError("Unexpected non-positive discriminant for L5.")

    rem = disc_l5
    v2, rem = _padic_valuation(rem, 2)
    v5, rem = _padic_valuation(rem, 5)
    v19, rem = _padic_valuation(rem, 19)
    v37, rem = _padic_valuation(rem, 37)

    residual_root = math.isqrt(rem)
    residual_is_square = residual_root * residual_root == rem

    decomposition_matches_expected = (
        v2 == 32 and v5 == 35 and v19 == 2 and v37 == 94 and residual_is_square
    )
    squarefree_class = 5 if decomposition_matches_expected else 0

    dt = time.time() - t0
    payload = Payload(
        l5_degree=int(L5.degree()),
        l5_leading_coeff=int(L5.LC()),
        l5_coeffs_high_to_low=[int(c) for c in L5.all_coeffs()],
        l5_irreducible_over_Q=bool(l5_irreducible),
        l5_mod37_matches_expected=bool(l5_mod37_matches_expected),
        disc_l5=int(disc_l5),
        v2=int(v2),
        v5=int(v5),
        v19=int(v19),
        v37=int(v37),
        residual_square_part=int(rem),
        residual_is_square=bool(residual_is_square),
        residual_square_root=int(residual_root),
        decomposition_matches_expected=bool(decomposition_matches_expected),
        squarefree_class_disc_l5=int(squarefree_class),
        seconds=float(dt),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_5torsion_discriminant_quadratic_character_audit.json"
        _write_json(out_json, asdict(payload))

        if decomposition_matches_expected:
            disc_line = (
                r"\operatorname{Disc}\!\bigl(L_{5}\bigr)"
                r"=2^{32}\cdot 5^{35}\cdot 19^{2}\cdot 37^{94}\cdot D_{5}^{2},"
                + f"\\qquad D_{{5}}={residual_root}."
            )
            sqfree_line = r"\bigl[\operatorname{Disc}(L_{5})\bigr]_{\mathrm{sf}}=5."
        else:
            disc_line = (
                r"\operatorname{Disc}\!\bigl(L_{5}\bigr)="
                + sp.latex(sp.Integer(disc_l5))
                + "."
            )
            sqfree_line = r"\text{(squarefree class check requires decomposition step).}"

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_elliptic_5torsion_discriminant_quadratic_character_audit.py",
                "\\[",
                f"L_{{5}}(y)={sp.latex(L5.as_expr())}.",
                "\\]",
                "\\[",
                r"L_{5}(y)\equiv -4\,(y-6)^{20}\,(y^{4}+y^{3}+10y^{2}+9y+4)\pmod{37}.",
                "\\]",
                "\\[",
                disc_line,
                "\\]",
                "\\[",
                sqfree_line,
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_elliptic_5torsion_discriminant_quadratic_character_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-elliptic-5torsion-disc] wrote {out_json}", flush=True)
        print(f"[fold-zm-elliptic-5torsion-disc] wrote {out_tex}", flush=True)

    print(
        "[fold-zm-elliptic-5torsion-disc] checks:"
        f" deg={L5.degree()} irreducible={l5_irreducible} mod37={l5_mod37_matches_expected}"
        f" v2={v2} v5={v5} v19={v19} v37={v37}"
        f" residual_square={residual_is_square} sqfree={squarefree_class}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-5torsion-disc] done", flush=True)


if __name__ == "__main__":
    main()
