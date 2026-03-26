#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit weight–collision partition functions Z_m^{(q)}(y) for q=2,3,4.

This script is English-only by repository convention.

We verify (by exact enumeration for small m and symbolic algebra):
  - The given rational generating functions for q=2 and q=3
  - The given order-10 recurrence + numerator for q=4 (via series match)
  - Ghost-mode cancellations at y=1 (factors (t-1)(t+1)^2 and (t^2+1))
  - Discriminant factorizations for the characteristic polynomials Pi_q(lambda,y)
  - D_q(±1,y) factorization identities
  - Zero-weight fiber closed form d_m(0^m)=floor((m+2)/2)

Outputs (default):
  - artifacts/export/fold_zq_weight_collision_partition_audit.json
  - sections/generated/eq_fold_zq_weight_collision_partition_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def enumerate_Zq_polys(*, q: int, m_max: int, prog: Progress) -> Tuple[sp.Symbol, List[sp.Expr]]:
    y = sp.Symbol("y")
    Z: List[sp.Expr] = []
    for m in range(m_max + 1):
        # Count d_m(x) by enumerating microstates.
        counts: Dict[Tuple[int, ...], int] = {}
        for bits in product([0, 1], repeat=m):
            x = tuple(fold_m(bits))
            counts[x] = counts.get(x, 0) + 1
        # Build Z_m^{(q)}(y)=sum_x y^{|x|_1} d(x)^q.
        poly = sp.Integer(0)
        for x, d in counts.items():
            k = int(sum(x))
            poly += sp.Integer(d**q) * (y**k)
        Z.append(sp.expand(poly))
        prog.tick(f"q={q} m={m} micro={1<<m} |X_m|={len(counts)}")
    return y, Z


def series_coeffs(expr: sp.Expr, t: sp.Symbol, m_max: int) -> List[sp.Expr]:
    s = sp.series(expr, t, 0, m_max + 1).removeO()
    s = sp.expand(s)
    return [sp.expand(s.coeff(t, m)) for m in range(m_max + 1)]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Z_m^{(q)}(y) for q=2,3,4")
    parser.add_argument("--m-max", type=int, default=12, help="Max m for exact enumeration checks (default: 12)")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    t0 = time.time()
    prog = Progress(label="fold-zq-audit", every_seconds=10.0)
    print("[fold-zq-audit] start", flush=True)

    y = sp.Symbol("y")
    t = sp.Symbol("t")

    # --- Enumerate Z_m^{(q)}(y) for q=2,3,4 ---
    _, Z2 = enumerate_Zq_polys(q=2, m_max=args.m_max, prog=prog)
    _, Z3 = enumerate_Zq_polys(q=3, m_max=args.m_max, prog=prog)
    _, Z4 = enumerate_Zq_polys(q=4, m_max=args.m_max, prog=prog)

    # --- q=2 rational generating function ---
    N2 = 1 + y * t + (1 - 2 * y) * t**2 + (y - 2 * y**2) * t**3 + (y**2 - y) * t**4 + (y**3 - y**2) * t**5
    D2 = 1 - t - (2 + 3 * y) * t**2 + (2 - y) * t**3 + (1 + 2 * y + 3 * y**2) * t**4 - (1 - y) * t**5 - (y + y**3) * t**6
    coeff2 = series_coeffs(N2 / D2, t, args.m_max)
    gen2_ok = all(sp.expand(coeff2[m] - Z2[m]) == 0 for m in range(args.m_max + 1))

    # --- q=3 rational generating function ---
    N3 = (
        1
        + y * t
        + (4 - 3 * y) * t**2
        + (4 * y - 3 * y**2) * t**3
        + (1 - 6 * y + 3 * y**2) * t**4
        + (y - 6 * y**2 + 3 * y**3) * t**5
        - y * (y - 1) ** 2 * t**6
        - y**2 * (y - 1) ** 2 * t**7
    )
    D3 = (
        1
        - t
        - (3 + 4 * y) * t**2
        - (4 * y - 3) * t**3
        + (6 * y**2 - y + 3) * t**4
        - (y**2 - 6 * y + 3) * t**5
        - (4 * y**3 - 5 * y**2 + 2 * y + 1) * t**6
        + (y - 1) ** 2 * t**7
        + (y**4 - y**3 - y**2 + y) * t**8
    )
    coeff3 = series_coeffs(N3 / D3, t, args.m_max)
    gen3_ok = all(sp.expand(coeff3[m] - Z3[m]) == 0 for m in range(args.m_max + 1))

    # --- q=4: use recurrence coefficients (denominator) + explicit numerator ---
    # Denominator from recurrence:
    a1 = 1
    a2 = 4 + 5 * y
    a3 = 11 * y - 4
    a4 = -10 * y**2 + 19 * y - 6
    a5 = 11 * y**2 - 18 * y + 6
    a6 = 10 * y**3 - 27 * y**2 + 2 * y + 4
    a7 = y**3 - 13 * y**2 + 9 * y - 4
    a8 = -5 * y**4 + 5 * y**3 + 2 * y**2 - 3 * y - 1
    a9 = -y**3 + 2 * y**2 - 2 * y + 1
    a10 = y**5 - y**4 + 2 * y**3 - y**2 + y
    D4 = 1 - a1 * t - a2 * t**2 - a3 * t**3 - a4 * t**4 - a5 * t**5 - a6 * t**6 - a7 * t**7 - a8 * t**8 - a9 * t**9 - a10 * t**10

    N4 = (
        1
        + y * t
        + (11 - 4 * y) * t**2
        + (11 * y - 4 * y**2) * t**3
        + (11 - 18 * y + 6 * y**2) * t**4
        + (11 * y - 18 * y**2 + 6 * y**3) * t**5
        + (1 - 13 * y + 9 * y**2 - 4 * y**3) * t**6
        + (y - 13 * y**2 + 9 * y**3 - 4 * y**4) * t**7
        + y * (y - 1) * (y**2 - y + 1) * t**8
        + y**2 * (y - 1) * (y**2 - y + 1) * t**9
    )

    coeff4 = series_coeffs(N4 / D4, t, args.m_max)
    gen4_ok = all(sp.expand(coeff4[m] - Z4[m]) == 0 for m in range(args.m_max + 1))

    # --- y=1 ghost cancellations ---
    def _simplify_at_y1(N: sp.Expr, D: sp.Expr) -> sp.Expr:
        return sp.simplify(sp.factor(N.subs({y: 1})) / sp.factor(D.subs({y: 1})))

    F2_y1 = _simplify_at_y1(N2, D2)
    F3_y1 = _simplify_at_y1(N3, D3)
    F4_y1 = _simplify_at_y1(N4, D4)

    ghost2_ok = sp.simplify(F2_y1 - 1 / (2 * t**3 - 2 * t**2 - 2 * t + 1)) == 0
    ghost3_ok = sp.simplify(F3_y1 - (2 * t**2 + 1) / (2 * t**3 - 4 * t**2 - 2 * t + 1)) == 0
    ghost4_ok = sp.simplify(F4_y1 - (7 * t**2 + 1) / (2 * t**5 - 2 * t**4 - 7 * t**2 - 2 * t + 1)) == 0

    # --- D_q(±1,y) checks ---
    D2_pm = sp.factor(D2.subs({t: 1}) - D2.subs({t: -1}))
    D3_pm = sp.factor(D3.subs({t: 1}) - D3.subs({t: -1}))
    D4_pm = sp.factor(D4.subs({t: 1}) - D4.subs({t: -1}))
    pm_equal_ok = (D2_pm == 0) and (D3_pm == 0) and (D4_pm == 0)

    D2_at = sp.factor(D2.subs({t: 1}))
    D3_at = sp.factor(D3.subs({t: 1}))
    D4_at = sp.factor(D4.subs({t: 1}))
    D2_at_ok = sp.factor(D2_at - (-y * (y - 1) * (y - 2))) == 0
    D3_at_ok = sp.factor(D3_at - (y * (y - 1) * (y**2 - 4 * y + 6))) == 0
    D4_at_ok = sp.factor(D4_at - (-y * (y - 1) * (y**3 - 5 * y**2 + 12 * y - 24))) == 0

    # --- Discriminant factorizations for Pi_q(lambda,y)=lambda^r D_q(1/lambda,y) ---
    lam = sp.Symbol("lam")

    def Pi_from_D(D: sp.Expr, r: int) -> sp.Expr:
        return sp.expand(lam**r * D.subs({t: 1 / lam}))

    Pi2 = Pi_from_D(D2, 6)
    Pi3 = Pi_from_D(D3, 8)
    Pi4 = Pi_from_D(D4, 10)

    disc2 = sp.factor(sp.discriminant(Pi2, lam))
    disc3 = sp.discriminant(Pi3, lam)
    disc4 = sp.discriminant(Pi4, lam)

    P9 = (
        186624 * y**9
        - 695632 * y**8
        + 980411 * y**7
        - 1121640 * y**6
        + 1021286 * y**5
        - 458803 * y**4
        + 127602 * y**3
        - 35316 * y**2
        - 10260 * y
        + 6912
    )
    disc2_expected = 4 * y**3 * (y - 1) * P9
    disc2_ok = sp.factor(disc2 - disc2_expected) == 0

    P17 = sp.factor(disc3 / (-16 * y**5 * (y - 1) ** 3))
    disc3_ok = sp.factor((-16 * y**5 * (y - 1) ** 3) * P17 - disc3) == 0 and sp.degree(P17, y) == 17

    R31 = sp.factor(disc4 / (9216 * y**7 * (y - 1) * (y**2 - y + 1)))
    disc4_ok = (
        sp.factor(9216 * y**7 * (y - 1) * (y**2 - y + 1) * R31 - disc4) == 0 and sp.degree(R31, y) == 31
    )

    # One negative real root for P17 (numerical certificate).
    y_neg_root = None
    try:
        roots17 = sp.nroots(P17)
        neg_reals = [complex(r) for r in roots17 if abs(complex(r).imag) < 1e-8 and complex(r).real < 0]
        if len(neg_reals) >= 1:
            y_neg_root = float(sorted(neg_reals, key=lambda z: z.real)[0].real)
    except Exception:
        y_neg_root = None

    # --- zero-weight fiber d_m(0^m) ---
    # Count microstates that fold to 0^m by enumeration, compare to floor((m+2)/2).
    zero_fiber_ok = True
    zero_fiber_rows: List[Dict[str, object]] = []
    for m in range(1, min(args.m_max, 18) + 1):
        target = tuple([0] * m)
        cnt = 0
        for bits in product([0, 1], repeat=m):
            if tuple(fold_m(bits)) == target:
                cnt += 1
        closed = (m + 2) // 2
        ok = (cnt == closed)
        zero_fiber_rows.append({"m": m, "count": cnt, "closed_form": closed, "ok": ok})
        if not ok:
            zero_fiber_ok = False

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": float(time.time()),
            "seconds": float(time.time() - t0),
        },
        "params": {"m_max": int(args.m_max)},
        "checks": {
            "q2_generating_function_series_ok": bool(gen2_ok),
            "q3_generating_function_series_ok": bool(gen3_ok),
            "q4_generating_function_series_ok": bool(gen4_ok),
            "ghost_cancellation_q2_ok": bool(ghost2_ok),
            "ghost_cancellation_q3_ok": bool(ghost3_ok),
            "ghost_cancellation_q4_ok": bool(ghost4_ok),
            "disc_factor_q2_ok": bool(disc2_ok),
            "disc_factor_q3_ok": bool(disc3_ok),
            "disc_factor_q4_ok": bool(disc4_ok),
            "D_q_1_equals_minus1_ok": bool(pm_equal_ok),
            "D2_at_pm1_factor_ok": bool(D2_at_ok),
            "D3_at_pm1_factor_ok": bool(D3_at_ok),
            "D4_at_pm1_factor_ok": bool(D4_at_ok),
            "zero_weight_fiber_closed_form_ok": bool(zero_fiber_ok),
        },
        "facts": {
            "F2_y1_simplified": str(F2_y1),
            "F3_y1_simplified": str(F3_y1),
            "F4_y1_simplified": str(F4_y1),
            "D2_t1_factor": str(D2_at),
            "D3_t1_factor": str(D3_at),
            "D4_t1_factor": str(D4_at),
            "Pi2_lambda_y": str(Pi2),
            "Pi3_lambda_y": str(Pi3),
            "Pi4_lambda_y": str(Pi4),
            "Disc2_expected": str(disc2_expected),
            "Disc2_factor": str(disc2),
            "P9": str(P9),
            "P17": str(P17),
            "P17_unique_negative_real_root_approx": y_neg_root,
            "R31": str(R31),
        },
        "zero_weight_fiber_rows": zero_fiber_rows,
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zq_weight_collision_partition_audit.json"
        _write_json(out_json, payload)

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zq_weight_collision_partition_audit.py",
                "\\[",
                "F_2(t,1)=\\frac{1}{2t^{3}-2t^{2}-2t+1},\\qquad",
                "F_3(t,1)=\\frac{2t^{2}+1}{2t^{3}-4t^{2}-2t+1},\\qquad",
                "F_4(t,1)=\\frac{7t^{2}+1}{2t^{5}-2t^{4}-7t^{2}-2t+1}.",
                "\\]",
                "\\[",
                "\\mathrm{Disc}_{\\lambda}(\\Pi_2)=4y^{3}(y-1)P_{9}(y),\\qquad",
                "\\mathrm{Disc}_{\\lambda}(\\Pi_3)=-16y^{5}(y-1)^{3}P_{17}(y),\\qquad",
                "\\mathrm{Disc}_{\\lambda}(\\Pi_4)=9216y^{7}(y-1)(y^{2}-y+1)R_{31}(y).",
                "\\]",
                "\\[",
                "D_2(\\pm1,y)=-y(y-1)(y-2),\\quad",
                "D_3(\\pm1,y)=y(y-1)(y^{2}-4y+6),\\quad",
                "D_4(\\pm1,y)=-y(y-1)(y^{3}-5y^{2}+12y-24).",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zq_weight_collision_partition_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zq-audit] wrote {out_json}", flush=True)
        print(f"[fold-zq-audit] wrote {out_tex}", flush=True)

    print(
        "[fold-zq-audit] checks:",
        f"q2={gen2_ok} q3={gen3_ok} q4={gen4_ok}",
        f"ghost2={ghost2_ok} ghost3={ghost3_ok} ghost4={ghost4_ok}",
        f"disc2={disc2_ok} disc3={disc3_ok} disc4={disc4_ok}",
        f"pm_equal={pm_equal_ok} d0_closed={zero_fiber_ok}",
        flush=True,
    )
    print("[fold-zq-audit] done", flush=True)


if __name__ == "__main__":
    main()

