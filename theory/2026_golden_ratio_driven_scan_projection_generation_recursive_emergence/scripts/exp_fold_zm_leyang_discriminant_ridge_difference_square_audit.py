#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit a difference-square (norm) identity on the Lee–Yang discriminant ridge curve.

We work with the genus-2 hyperelliptic curve

    C_LY:  w^2 = -y(y-1) P_LY(y),
    P_LY(y) = 256y^3 + 411y^2 + 165y + 32.

This script is English-only by repository convention.

We verify symbolically:
  - The explicit polynomial identity
        Q(y)^2 - 256 A(y)^6 = 27 y(y-1) P_LY(y),
    where A(y)=1+2y and Q(y)=16+69y+219y^2+128y^3.
  - The polynomial discriminant factorization
        Disc_y(-y(y-1)P_LY(y)) = -2^20 * 3^15 * 31^2 * 37.
  - The Weierstrass-discriminant sign for the integral model
        eta^2 + eta = x^3 - x,
    under the standard invariant convention (c4^3 - c6^2 = 1728*Delta): Delta = 37.

Outputs:
  - artifacts/export/fold_zm_leyang_discriminant_ridge_difference_square_audit.json
  - sections/generated/eq_fold_zm_leyang_discriminant_ridge_difference_square_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict

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
    # difference-square identity
    identity_ok: bool
    # polynomial discriminant
    disc_f: int
    disc_f_factorization: Dict[str, int]
    disc_f_expected: int
    disc_f_matches_expected: bool
    # elliptic discriminant sign (integral model eta^2+eta = x^3-x)
    delta_integral_model: int
    c4_integral_model: int
    c6_integral_model: int
    c4c6_relation_ok: bool


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit the Lee–Yang discriminant ridge difference-square identity and discriminant fingerprints."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-leyang-disc-ridge-diff-square] start", flush=True)

    y = sp.Symbol("y")
    P = 256 * y**3 + 411 * y**2 + 165 * y + 32
    f = -y * (y - 1) * P

    A = 1 + 2 * y
    Q = 16 + 69 * y + 219 * y**2 + 128 * y**3

    identity = sp.factor(Q**2 - 256 * A**6 - 27 * y * (y - 1) * P)
    identity_ok = bool(identity == 0)
    if not identity_ok:
        raise RuntimeError(f"Difference-square identity failed: {identity}")

    disc_f = int(sp.discriminant(f, y))
    disc_expected = -2**20 * 3**15 * 31**2 * 37
    disc_ok = bool(disc_f == disc_expected)
    if not disc_ok:
        raise RuntimeError(f"Unexpected Disc(f): got {disc_f}, expected {disc_expected}")

    fac = sp.factorint(abs(disc_f))
    disc_fac = {str(int(p)): int(e) for p, e in fac.items()}

    # --- Integral Weierstrass model: eta^2 + eta = x^3 - x ---
    # Standard invariants:
    #   b2 = a1^2 + 4a2
    #   b4 = 2a4 + a1 a3
    #   b6 = a3^2 + 4a6
    #   b8 = a1^2 a6 + 4a2 a6 - a1 a3 a4 + a2 a3^2 - a4^2
    #   Delta = -b2^2 b8 - 8 b4^3 - 27 b6^2 + 9 b2 b4 b6
    #   c4 = b2^2 - 24 b4
    #   c6 = -b2^3 + 36 b2 b4 - 216 b6
    a1, a2, a3, a4, a6 = sp.Integer(0), sp.Integer(0), sp.Integer(1), sp.Integer(-1), sp.Integer(0)
    b2 = a1**2 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3**2 + 4 * a6
    b8 = a1**2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3**2 - a4**2
    Delta = sp.simplify(-b2**2 * b8 - 8 * b4**3 - 27 * b6**2 + 9 * b2 * b4 * b6)
    c4 = sp.simplify(b2**2 - 24 * b4)
    c6 = sp.simplify(-b2**3 + 36 * b2 * b4 - 216 * b6)
    rel_ok = bool(sp.simplify(c4**3 - c6**2 - 1728 * Delta) == 0)

    if not (int(Delta) == 37 and rel_ok):
        raise RuntimeError(f"Unexpected integral-model invariants: Delta={Delta}, relation_ok={rel_ok}")

    payload = Payload(
        identity_ok=identity_ok,
        disc_f=disc_f,
        disc_f_factorization=disc_fac,
        disc_f_expected=disc_expected,
        disc_f_matches_expected=disc_ok,
        delta_integral_model=int(Delta),
        c4_integral_model=int(c4),
        c6_integral_model=int(c6),
        c4c6_relation_ok=rel_ok,
    )

    if not args.no_output:
        json_path = export_dir() / "fold_zm_leyang_discriminant_ridge_difference_square_audit.json"
        tex_path = generated_dir() / "eq_fold_zm_leyang_discriminant_ridge_difference_square_audit.tex"

        _write_json(json_path, asdict(payload))

        tex = r"""\begin{equation}\label{eq:fold_zm_leyang_discriminant_ridge_difference_square_audit}
\begin{aligned}
P_{\mathrm{LY}}(y)&:=256y^{3}+411y^{2}+165y+32,\\
A(y)&:=1+2y,\qquad Q(y):=16+69y+219y^{2}+128y^{3},\\
Q(y)^{2}-256A(y)^{6}&=27y(y-1)P_{\mathrm{LY}}(y),\\
\mathrm{Disc}_{y}\!\bigl(-y(y-1)P_{\mathrm{LY}}(y)\bigr)&=-2^{20}\cdot 3^{15}\cdot 31^{2}\cdot 37.
\end{aligned}
\end{equation}
"""
        _write_text(tex_path, tex)

    dt = time.time() - t0
    print(f"[fold-zm-leyang-disc-ridge-diff-square] ok elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

