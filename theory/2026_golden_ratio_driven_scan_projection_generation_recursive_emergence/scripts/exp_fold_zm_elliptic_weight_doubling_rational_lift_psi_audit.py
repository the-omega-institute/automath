#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Rational lift for y([2]P) on the (lambda,y)-spectral curve.

English-only by repository convention.

We work on the elliptic curve
  E: Y^2 = X^3 - X + 1/4
with the weight function
  y = X^2 + Y - 1/2.

Let y2 := y([2]P). On the affine spectral plane curve
  Pi(lambda,y) = lambda^4 - lambda^3 - (2y+1)lambda^2 + lambda + y(y+1) = 0,
there exists an explicit rational expression
  y2 = Psi(lambda,y) = N(lambda,y) / D(lambda,y),
with N,D of degree <= 3 in lambda.

This script:
  - defines N,D in Z[lambda,y],
  - checks Psi against the elliptic doubling law at several rational multiples of a generator,
  - writes a LaTeX snippet for inclusion in the paper.

Outputs:
  - artifacts/export/fold_zm_elliptic_weight_doubling_rational_lift_psi_audit.json
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_psi.tex
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


Point = Optional[Tuple[sp.Rational, sp.Rational]]  # None means O


def on_curve(P: Point) -> bool:
    if P is None:
        return True
    x, y = P
    return sp.simplify(y**2 - (x**3 - x + sp.Rational(1, 4))) == 0


def add(P: Point, Q: Point) -> Point:
    a = sp.Rational(-1, 1)
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and y1 == -y2:
        return None
    if P == Q:
        if y1 == 0:
            return None
        m = (3 * x1**2 + a) / (2 * y1)
    else:
        m = (y2 - y1) / (x2 - x1)
    x3 = m**2 - x1 - x2
    y3 = m * (x1 - x3) - y1
    return (sp.simplify(x3), sp.simplify(y3))


def mul(n: int, P: Point) -> Point:
    if n == 0 or P is None:
        return None
    if n < 0:
        x, y = P
        return mul(-n, (x, -y))
    Q: Point = None
    R: Point = P
    k = n
    while k > 0:
        if k & 1:
            Q = add(Q, R)
        R = add(R, R)
        k >>= 1
    return Q


def weight_y(P: Point) -> sp.Rational:
    assert P is not None
    x, y = P
    return sp.simplify(x**2 + y - sp.Rational(1, 2))


@dataclass(frozen=True)
class Payload:
    points_tested: int
    checks_passed: bool
    failing_n: int
    failing_point: List[str]


def main() -> None:
    lam, yy = sp.symbols("lambda y")

    N = (
        (2 * yy**2 + 10 * yy - 1) * lam**3
        + (-2 * yy**3 + 6 * yy**2 - 34 * yy - 27) * lam**2
        + (-2 * yy**3 - 10 * yy**2 - 12 * yy + 23) * lam
        + (yy**4 + 23 * yy**2 + 23 * yy - 1)
    )
    D = (
        (-64 * yy - 8) * lam**3
        + (-48 * yy**2 - 16 * yy) * lam**2
        + (16 * yy**2 + 48 * yy + 8) * lam
        + (32 * yy**3 + 32 * yy**2 - 1)
    )
    Psi = sp.simplify(N / D)

    # Generator on E (rank 1): R=(0,1/2).
    R: Point = (sp.Rational(0), sp.Rational(1, 2))
    assert on_curve(R)

    # Test on multiples that avoid the obvious branch fibers y in {0,1}.
    tested = 0
    ok = True
    failing_n = 0
    failing_point: List[str] = []
    for n in range(1, 41):
        P = mul(n, R)
        if P is None:
            continue
        if not on_curve(P):
            ok = False
            failing_n = n
            failing_point = [str(P[0]), str(P[1])]
            break
        x, Y = P
        y0 = weight_y(P)
        if y0 in (sp.Rational(0), sp.Rational(1)):
            continue
        P2 = add(P, P)
        if P2 is None:
            continue
        y2 = weight_y(P2)
        val = sp.simplify(Psi.subs({lam: x, yy: y0}))
        if sp.denom(val) == 0:
            continue
        tested += 1
        if sp.simplify(val - y2) != 0:
            ok = False
            failing_n = n
            failing_point = [str(x), str(Y)]
            break
        if tested >= 8:
            break

    payload = Payload(points_tested=tested, checks_passed=ok, failing_n=failing_n, failing_point=failing_point)
    _write_json(export_dir() / "fold_zm_elliptic_weight_doubling_rational_lift_psi_audit.json", asdict(payload))

    def _poly_in_lambda(expr: sp.Expr) -> sp.Poly:
        return sp.Poly(sp.expand(expr), lam, domain=sp.QQ.frac_field(yy))

    def _latex_grouped_in_lambda(expr: sp.Expr) -> str:
        p = _poly_in_lambda(expr)
        deg = p.degree()
        pieces: List[str] = []
        for k in range(deg, -1, -1):
            ck = sp.simplify(p.nth(k))
            if ck == 0:
                continue
            ck_tex = sp.latex(sp.factor(ck))
            if k == 0:
                term = f"({ck_tex})"
            elif k == 1:
                term = f"({ck_tex})\\lambda"
            else:
                term = f"({ck_tex})\\lambda^{k}"
            pieces.append(term)
        if not pieces:
            return "0"
        return " + ".join(pieces).replace("+ -", "- ")

    tex: List[str] = []
    tex.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_rational_lift_psi_audit.py")
    tex.append("\\[")
    tex.append(
        "y([2]P)=\\Psi(\\lambda,y)=\\frac{N(\\lambda,y)}{D(\\lambda,y)}\\qquad \\text{in }\\QQ(\\lambda,y)/(\\Pi(\\lambda,y))."
    )
    tex.append("\\]")
    tex.append("\\[")
    tex.append("\\begin{aligned}")
    tex.append(f"N(\\lambda,y)&={_latex_grouped_in_lambda(N)}\\\\")
    tex.append(f"D(\\lambda,y)&={_latex_grouped_in_lambda(D)}")
    tex.append("\\end{aligned}")
    tex.append("\\]")
    _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_doubling_psi.tex", "\n".join(tex) + "\n")


if __name__ == "__main__":
    main()

