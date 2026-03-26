#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Finite-height rational point scan for the genus-2 discriminant ridge curve.

Curve:
  C: w^2 = -y(y-1) P_LY(y),
  P_LY(y)=256y^3+411y^2+165y+32.

We enumerate reduced rationals y=a/b with b>0, gcd(a,b)=1 and max(|a|,b) <= H,
and test whether f(y) is a square in Q (equivalently: numerator and denominator
are perfect squares after reduction).

This script is English-only by repository convention.

Outputs:
  - artifacts/export/fold_zm_discriminant_ridge_rational_points_height200_audit.json
  - sections/generated/eq_fold_zm_discriminant_ridge_rational_points_height200_audit.tex
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def P_LY(y: Fraction) -> Fraction:
    return Fraction(256) * y**3 + Fraction(411) * y**2 + Fraction(165) * y + Fraction(32)


def f(y: Fraction) -> Fraction:
    return -(y * (y - 1) * P_LY(y))


def _is_square_int(n: int) -> Tuple[bool, int]:
    if n < 0:
        return (False, 0)
    r = math.isqrt(n)
    return (r * r == n, r)


def _is_square_q(x: Fraction) -> Tuple[bool, Fraction]:
    """Return (is_square, sqrt) with sqrt>=0 when true."""
    n, d = x.numerator, x.denominator
    ok_n, rn = _is_square_int(n)
    if not ok_n:
        return (False, Fraction(0))
    ok_d, rd = _is_square_int(d)
    if not ok_d:
        return (False, Fraction(0))
    return (True, Fraction(rn, rd))


def _reduced_rationals_height(H: int) -> Iterable[Fraction]:
    H = int(H)
    for b in range(1, H + 1):
        for a in range(-H, H + 1):
            if math.gcd(a, b) != 1:
                continue
            yield Fraction(a, b)


@dataclass(frozen=True)
class AffinePoint:
    y: str
    w: str


def main() -> None:
    H = 200

    pts: Set[Tuple[Fraction, Fraction]] = set()
    scanned = 0
    for y in _reduced_rationals_height(H):
        scanned += 1
        ok, w0 = _is_square_q(f(y))
        if not ok:
            continue
        pts.add((y, w0))
        if w0 != 0:
            pts.add((y, -w0))

    pts_sorted = sorted(pts, key=lambda t: (t[0].denominator, t[0].numerator, t[1].denominator, t[1].numerator))
    affine_points: List[AffinePoint] = [
        AffinePoint(y=str(y), w=str(w)) for (y, w) in pts_sorted
    ]

    payload: Dict[str, object] = {
        "curve": "C: w^2 = -y(y-1)P_LY(y), P_LY(y)=256y^3+411y^2+165y+32",
        "height_bound": H,
        "scan_domain": "reduced rationals y=a/b with b>0, gcd(a,b)=1, max(|a|,b) <= H",
        "num_y_scanned": scanned,
        "affine_points": [asdict(p) for p in affine_points],
        "num_affine_points": len(affine_points),
        "note": "The unique point at infinity of the odd-degree model is not part of this affine scan.",
    }

    out_json = export_dir() / "fold_zm_discriminant_ridge_rational_points_height200_audit.json"
    _write_json(out_json, payload)

    # TeX snippet: report only the set of affine points found.
    pts_tex = ",\\ ".join([f"(y,w)=({p.y},{p.w})" for p in affine_points])
    if not pts_tex:
        pts_tex = "\\varnothing"
    tex = (
        "\\[\n"
        + r"\boxed{\ \{(y,w)\in C(\mathbb Q): \max\{|a|,b\}\le "
        + str(H)
        + r"\}\;=\;\{"
        + pts_tex
        + r"\}\ }"
        + "\n"
        + "\\]\n"
    )
    out_tex = generated_dir() / "eq_fold_zm_discriminant_ridge_rational_points_height200_audit.tex"
    _write_text(out_tex, tex)


if __name__ == "__main__":
    main()

