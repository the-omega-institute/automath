#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit real-rootedness and Sturm interlacing for Z_m(y) in a finite window.

This script is English-only by repository convention.

We generate Z_m(y) exactly from the verified order-4 recurrence and check (m<=m_max):
  - all zeros are real, negative, and simple;
  - zeros of Z_m and Z_{m+2} (fixed parity) strictly interlace.

Output (default):
  - artifacts/export/fold_zm_sturm_real_roots_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _zm_polys_by_recurrence(m_max: int) -> Tuple[sp.Symbol, List[sp.Poly]]:
    y = sp.Symbol("y")
    Z0 = sp.Poly(1, y, domain=sp.ZZ)
    Z1 = sp.Poly(1 + y, y, domain=sp.ZZ)
    Z2 = sp.Poly(2 + 2 * y, y, domain=sp.ZZ)
    Z3 = sp.Poly(y**2 + 5 * y + 2, y, domain=sp.ZZ)
    Z: List[sp.Poly] = [Z0, Z1, Z2, Z3]

    if m_max <= 3:
        return y, Z[: m_max + 1]

    poly_2y1 = sp.Poly(2 * y + 1, y, domain=sp.ZZ)
    poly_y_y1 = sp.Poly(y * (y + 1), y, domain=sp.ZZ)
    for m in range(4, m_max + 1):
        Zm = Z[m - 1] + poly_2y1 * Z[m - 2] - Z[m - 3] - poly_y_y1 * Z[m - 4]
        Z.append(sp.Poly(Zm, y, domain=sp.ZZ))
    return y, Z


def _check_strictly_increasing(xs: Sequence[sp.Number], tol: sp.Number) -> bool:
    for i in range(len(xs) - 1):
        if not (xs[i] < xs[i + 1] - tol):
            return False
    return True


def _check_interlacing(a: Sequence[sp.Number], b: Sequence[sp.Number], *, tol: sp.Number) -> bool:
    """Strict interlacing for sorted real root lists a (degree d) and b (degree d or d+1).

    - Alternate labels in the merged sorted list.
    - If len(b)=len(a)+1, b must appear at both ends.
    """
    da = len(a)
    db = len(b)
    if not (db == da or db == da + 1):
        return False
    merged: List[Tuple[sp.Number, str]] = [(x, "a") for x in a] + [(x, "b") for x in b]
    merged.sort(key=lambda t: float(t[0]))
    # strict order and alternation
    for i in range(len(merged) - 1):
        if not (merged[i][0] < merged[i + 1][0] - tol):
            return False
        if merged[i][1] == merged[i + 1][1]:
            return False
    if db == da + 1:
        if merged[0][1] != "b" or merged[-1][1] != "b":
            return False
    return True


@dataclass(frozen=True)
class PolyAudit:
    m: int
    degree: int
    degree_expected: int
    all_coeffs_nonnegative: bool
    constant_term: int
    n_roots: int
    max_abs_imag: str
    min_root: str
    max_root: str
    min_gap: str
    all_real: bool
    all_negative: bool
    all_simple: bool
    roots_real_sorted: List[str]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit real-rootedness and interlacing for Z_m(y).")
    parser.add_argument("--m-max", type=int, default=100, help="Max m to audit (default: 100).")
    parser.add_argument("--digits", type=int, default=90, help="Decimal digits for nroots (default: 90).")
    parser.add_argument("--maxsteps", type=int, default=200, help="Max Newton steps for nroots (default: 200).")
    parser.add_argument("--tol-imag", type=float, default=1e-30, help="Imaginary-part tolerance (default: 1e-30).")
    parser.add_argument("--tol-order", type=float, default=1e-20, help="Ordering/separation tolerance (default: 1e-20).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-sturm-real-roots] start", flush=True)

    m_max = int(args.m_max)
    if m_max < 0:
        raise SystemExit("--m-max must be non-negative")

    y, Z = _zm_polys_by_recurrence(m_max)
    tol_imag = sp.Float(str(args.tol_imag))
    tol_order = sp.Float(str(args.tol_order))

    audits: List[PolyAudit] = []
    roots_by_m: List[List[sp.Number]] = []

    overall_all_ok = True
    overall_max_imag = sp.Float(0)
    overall_min_gap: Optional[sp.Number] = None

    for m in range(0, m_max + 1):
        P = Z[m]
        deg = int(P.degree())
        deg_expected = (m + 1) // 2  # ceil(m/2)
        coeffs = [int(c) for c in P.all_coeffs()]
        all_coeffs_nonneg = all(c >= 0 for c in coeffs)
        const = int(P.eval(0))

        if deg <= 0:
            audits.append(
                PolyAudit(
                    m=m,
                    degree=deg,
                    degree_expected=deg_expected,
                    all_coeffs_nonnegative=bool(all_coeffs_nonneg),
                    constant_term=int(const),
                    n_roots=0,
                    max_abs_imag="0",
                    min_root="nan",
                    max_root="nan",
                    min_gap="inf",
                    all_real=True,
                    all_negative=True,
                    all_simple=True,
                    roots_real_sorted=[],
                )
            )
            roots_by_m.append([])
            continue

        # Numerical roots (high precision in SymPy's Float context)
        roots = sp.nroots(P.as_expr(), n=int(args.digits), maxsteps=int(args.maxsteps))
        reals: List[sp.Number] = []
        max_imag = sp.Float(0)
        all_real = True
        for r in roots:
            re = sp.re(r)
            im = sp.im(r)
            aim = abs(im)
            if aim > max_imag:
                max_imag = aim
            if aim > tol_imag:
                all_real = False
            reals.append(re)

        # Sort and assess negativity / simplicity.
        reals.sort(key=float)
        all_negative = all(x < -tol_order for x in reals)
        min_gap: sp.Number = sp.oo
        for i in range(len(reals) - 1):
            min_gap = min(min_gap, reals[i + 1] - reals[i])
        all_simple = bool(min_gap > tol_order) if len(reals) >= 2 else True

        # Consistency checks.
        deg_ok = deg == deg_expected
        n_ok = len(reals) == deg
        order_ok = _check_strictly_increasing(reals, tol=tol_order)
        ok = bool(deg_ok and n_ok and all_coeffs_nonneg and const != 0 and all_real and all_negative and all_simple and order_ok)

        overall_all_ok = overall_all_ok and ok
        if max_imag > overall_max_imag:
            overall_max_imag = max_imag
        if overall_min_gap is None:
            overall_min_gap = min_gap
        else:
            overall_min_gap = min(overall_min_gap, min_gap)

        audits.append(
            PolyAudit(
                m=m,
                degree=deg,
                degree_expected=deg_expected,
                all_coeffs_nonnegative=bool(all_coeffs_nonneg),
                constant_term=int(const),
                n_roots=int(len(reals)),
                max_abs_imag=sp.sstr(max_imag),
                min_root=sp.sstr(reals[0]),
                max_root=sp.sstr(reals[-1]),
                min_gap=sp.sstr(min_gap),
                all_real=bool(all_real),
                all_negative=bool(all_negative),
                all_simple=bool(all_simple),
                roots_real_sorted=[sp.sstr(x) for x in reals],
            )
        )
        roots_by_m.append(reals)

    # Interlacing checks along the degree-increasing step m -> m+2 (fixed parity subsequences).
    interlace: List[Dict[str, object]] = []
    interlace_all_ok = True
    for m in range(0, max(0, m_max - 1)):
        a = roots_by_m[m]
        b = roots_by_m[m + 2]
        if len(a) == 0 and len(b) == 0:
            ok = True
        elif len(a) == 0:
            ok = bool(_check_strictly_increasing(b, tol=tol_order) and len(b) == 1)
        else:
            ok = _check_interlacing(a, b, tol=tol_order)
        interlace.append(
            {"m": m, "m_plus_2": m + 2, "deg_m": len(a), "deg_m_plus_2": len(b), "interlace_ok": bool(ok)}
        )
        interlace_all_ok = interlace_all_ok and bool(ok)

    payload: Dict[str, object] = {
        "m_max": int(m_max),
        "digits": int(args.digits),
        "maxsteps": int(args.maxsteps),
        "tol_imag": float(tol_imag),
        "tol_order": float(tol_order),
        "interlacing_step": 2,
        "all_ok": bool(overall_all_ok and interlace_all_ok),
        "all_polys_ok": bool(overall_all_ok),
        "all_interlacing_ok": bool(interlace_all_ok),
        "overall_max_abs_imag": float(overall_max_imag),
        "overall_min_gap": float(overall_min_gap) if overall_min_gap is not None and overall_min_gap != sp.oo else None,
        "overall_max_abs_imag_str": sp.sstr(overall_max_imag),
        "overall_min_gap_str": sp.sstr(overall_min_gap) if overall_min_gap is not None else None,
        "polys": [asdict(a) for a in audits],
        "interlacing": interlace,
    }

    if not args.no_output:
        out = export_dir() / "fold_zm_sturm_real_roots_audit.json"
        _write_json(out, payload)

    dt = time.time() - t0
    print(
        "[fold-zm-sturm-real-roots] checks:"
        f" m_max={m_max} all_polys_ok={overall_all_ok} all_interlacing_ok={interlace_all_ok}"
        f" max_abs_imag={sp.sstr(overall_max_imag)} min_gap={sp.sstr(overall_min_gap)} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-sturm-real-roots] done", flush=True)


if __name__ == "__main__":
    main()

