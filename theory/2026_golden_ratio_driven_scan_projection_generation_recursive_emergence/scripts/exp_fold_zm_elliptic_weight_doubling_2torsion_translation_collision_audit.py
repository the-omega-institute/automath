#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the y-parameters where 2-torsion translation collides y-fibers.

This script is English-only by repository convention.

Setup:
  E: Y^2 = X^3 - X + 1/4,
  y := X^2 + Y - 1/2.

Let T=(a,0) be a nontrivial 2-torsion point, so a satisfies:
  D(a) := 4 a^3 - 4 a + 1 = 0.

For a point P=(X,Y) on E, consider the translate P+T and the collision condition:
  y(P) = y(P+T).

Eliminating X and a produces a univariate polynomial R(y) whose zero set equals the
Zariski closure of the parameter set:
  { y0 : exists P, exists T in E[2]\\{O} with y(P)=y(P+T)=y0 }.

We verify that the squarefree part of R(y) is exactly:
  Q(y) * A(y),
where Q(y)=16y^3-8y^2-4y+1 is the 2-division y-image cubic, and A(y) is the degree-12
discriminant-square factor from the weight-doubling correspondence audit.

Outputs:
  - artifacts/export/fold_zm_elliptic_weight_doubling_2torsion_translation_collision_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    R_degree: int
    R_lc: int
    R_factor_degrees_over_Q: List[int]
    R_factor_exponents_over_Q: List[int]
    R_squarefree_equals_QA: bool
    Q_degree: int
    A_degree: int


def _factor_degrees_and_exponents_over_Q(poly_Z: sp.Poly, y: sp.Symbol) -> Tuple[List[int], List[int]]:
    _c, facs = sp.factor_list(sp.Poly(poly_Z.as_expr(), y, domain=sp.QQ))
    degs: List[int] = []
    exps: List[int] = []
    for f, e in facs:
        degs.append(int(f.degree()))
        exps.append(int(e))
    return degs, exps


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit the y-parameter set where translation by nontrivial 2-torsion collides y-fibers."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    X, a, y = sp.symbols("X a y")

    # Spectral quartic certificate (eliminate Y via Y = y - X^2 + 1/2).
    Pi = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)

    # Express Y in terms of (X,y).
    Yexpr = y - X**2 + sp.Rational(1, 2)

    # Translate by T=(a,0): m = (Y-0)/(X-a), then X1=m^2 - X - a, Y1=m(X-X1)-Y.
    m = sp.together(Yexpr / (X - a))
    X1 = sp.together(m**2 - X - a)
    Y1 = sp.together(m * (X - X1) - Yexpr)

    # Collision condition y(P+T) = y(P) = y.
    y1 = sp.together(X1**2 + Y1 - sp.Rational(1, 2))
    num = sp.together(y1 - y).as_numer_denom()[0]
    num = sp.expand(num)

    # 2-torsion x-coordinate constraint.
    D = 4 * a**3 - 4 * a + 1

    # Eliminate X then a via multivariate resultants over QQ.
    Pi_poly = sp.Poly(Pi, X, a, y, domain=sp.QQ)
    num_poly = sp.Poly(num, X, a, y, domain=sp.QQ)
    res1_poly, _subres = Pi_poly.resultant(num_poly, X)

    D_poly = sp.Poly(D, a, y, domain=sp.QQ)
    res2_poly, _subres2 = res1_poly.resultant(D_poly, a)

    # Normalize to primitive integer polynomial in y.
    Rqq = sp.Poly(res2_poly.as_expr(), y, domain=sp.QQ)
    _content, Rz = sp.Poly(Rqq.as_expr(), y, domain=sp.ZZ).primitive()
    if Rz.LC() < 0:
        Rz = -Rz

    # Q(y): y-image cubic of E[2]\\{O}.
    Q = sp.Poly(16 * y**3 - 8 * y**2 - 4 * y + 1, y, domain=sp.ZZ)

    # A(y): degree-12 discriminant-square factor (see eq_fold_zm_elliptic_weight_doubling_discriminant.tex).
    A = sp.Poly(
        64 * y**12
        - 128 * y**11
        - 2576 * y**10
        - 2160 * y**9
        + 10892 * y**8
        + 32064 * y**7
        + 28873 * y**6
        - 11139 * y**5
        - 31715 * y**4
        - 8333 * y**3
        - 958 * y**2
        - 100 * y
        + 8,
        y,
        domain=sp.ZZ,
    )

    # Squarefree part comparison in QQ[y] (compare after monic normalization).
    R_sqf_QQ = sp.Poly(Rz.as_expr(), y, domain=sp.QQ).sqf_part()
    QA_QQ = sp.Poly(sp.expand(Q.as_expr() * A.as_expr()), y, domain=sp.QQ)
    R_sqf_equals_QA = sp.expand(R_sqf_QQ.monic().as_expr() - QA_QQ.monic().as_expr()) == 0

    degs, exps = _factor_degrees_and_exponents_over_Q(Rz, y)

    payload = Payload(
        R_degree=int(Rz.degree()),
        R_lc=int(Rz.LC()),
        R_factor_degrees_over_Q=degs,
        R_factor_exponents_over_Q=exps,
        R_squarefree_equals_QA=bool(R_sqf_equals_QA),
        Q_degree=int(Q.degree()),
        A_degree=int(A.degree()),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_weight_doubling_2torsion_translation_collision_audit.json"
        _write_json(out_json, asdict(payload))

    print(
        "[fold-zm-elliptic-weight-doubling-2torsion-translation-collision] "
        f"deg(R)={payload.R_degree} lc={payload.R_lc} "
        f"sqfree_equals_QA={payload.R_squarefree_equals_QA} "
        f"factor_degs={payload.R_factor_degrees_over_Q} exps={payload.R_factor_exponents_over_Q}",
        flush=True,
    )


if __name__ == "__main__":
    main()

