#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Mordell–Weil low multiples, denominator growth, bad prime 37 periodicity,
and Lee–Yang near-square specializations for the Fold weight elliptic curve.

Curve (short Weierstrass):
  E: Y^2 = X^3 - X + 1/4.

Minimal integral model (LMFDB / Cremona 37a1):
  E0: y0^2 + y0 = x^3 - x.

We verify (exact, auditable):
  - Low multiples for R=(0,1/2) (the image of R0=(0,0) under Y=y0+1/2):
      2R = (1,  1/2) = -Q0,
      3R = (-1,-1/2) = -Q0',
      4R = (2, -5/2) = P where P=(2, -5/2).
  - Weight map (physical branch): y = X^2 + Y - 1/2:
      y(2Q0)=y(4R)=6,  y(2Q0')=y(6R)=21.
  - Lee–Yang cubic P_LY(y)=256 y^3+411 y^2+165 y+32:
      P_LY(6)=2*37*31^2,  P_LY(21)=4*11*241^2.
  - Quartic characteristic polynomial Pi(lambda,y):
      Pi(lambda,6)  = (lambda-2)(lambda^3 + lambda^2 - 11 lambda - 21),
      Pi(lambda,21) = (lambda-6)(lambda^3 + 5 lambda^2 - 13 lambda - 77).
  - Denominator sequence v_n for x(nP)=u_n/v_n^2 (P=(2,-5/2)) for n=1..12,
    and log(v_n)/n^2 for n=8..12 (natural log).
  - Ward-type bilinear recurrence for the positive denominator normalization (v_0=0):
      v_{n+2} v_{n-2} = 29 v_n^2 + (-1)^{floor(n/2)} 25 v_{n+1} v_{n-1}  (n>=2),
    where 25=v_2^2 and 29=v_3 for this orbit.
  - Bad prime p=37 on minimal model:
      c6=-216,  (-c6 mod 37)=31,  (31/37)=-1 (nonsplit multiplicative),
      v_37(den(x(nR))^(1/2)) is 0 if 38∤n, and v_37(n)+1 if 38|n (audited on n<=76),
      v_37(den(x(nP))^(1/2)) is 0 if 19∤n, and v_37(n)+1 if 19|n (audited on n<=38).

Outputs:
  - artifacts/export/fold_zm_elliptic_mw_height_denominator_growth_audit.json
  - sections/generated/eq_fold_zm_elliptic_mw_height_denominator_growth_audit.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import asdict, dataclass
from fractions import Fraction
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


Point = Optional[Tuple[Fraction, Fraction]]  # None denotes O


def _add(P: Point, Q: Point, *, a: Fraction) -> Point:
    """Group law on short Weierstrass: Y^2 = X^3 + aX + b (b unused)."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and y1 == -y2:
        return None
    if x1 == x2 and y1 == y2:
        m = (3 * x1 * x1 + a) / (2 * y1)
    else:
        m = (y2 - y1) / (x2 - x1)
    x3 = m * m - x1 - x2
    y3 = m * (x1 - x3) - y1
    return (x3, y3)


def _mul(n: int, P: Point, *, a: Fraction) -> Point:
    """Double-and-add scalar multiplication."""
    if n < 0:
        if P is None:
            return None
        x, y = P
        return _mul(-n, (x, -y), a=a)
    if n == 0:
        return None
    Q: Point = None
    R: Point = P
    k = int(n)
    while k > 0:
        if k & 1:
            Q = _add(Q, R, a=a)
        R = _add(R, R, a=a)
        k >>= 1
    return Q


def _y_weight(P: Point) -> Fraction:
    if P is None:
        raise ValueError("y-weight undefined at O.")
    x, y = P
    return x * x + y - Fraction(1, 2)


def _v_p(n: int, p: int) -> int:
    n = abs(int(n))
    p = int(p)
    e = 0
    while n and n % p == 0:
        n //= p
        e += 1
    return e


def _fraction_to_uv2(x: Fraction) -> Tuple[int, int, int, bool]:
    """Return (u, v, den, is_square_den) for x = u / den and attempt den=v^2."""
    num = x.numerator
    den = x.denominator
    v = int(math.isqrt(den))
    return int(num), int(v), int(den), bool(v * v == den)


def _legendre_symbol(a: int, p: int) -> int:
    """Return (a/p) for odd prime p as -1,0,1."""
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else int(t)


@dataclass(frozen=True)
class Payload:
    low_multiples_ok: bool
    points: Dict[str, str]
    branchpoint_doubling_y: Dict[str, int]
    p_ly_specializations: Dict[str, str]
    pi_fiber_factorizations: Dict[str, str]
    v_first12: List[int]
    vn_ward_bilinear_ok: bool
    vn_ward_bilinear_first_failure_n: Optional[int]
    log_v_over_n2_8_12: List[float]
    hhat_P: float
    c6_min_model: int
    minus_c6_mod_37: int
    legendre_31_over_37: int
    v37_periodicity_R_ok: bool
    v37_periodicity_P_ok: bool
    v37_R_first_hits: List[int]
    v37_P_first_hits: List[int]


def main() -> None:
    t0 = time.time()
    print("[fold-zm-elliptic-mw-height-den] start", flush=True)

    a = Fraction(-1, 1)
    b = Fraction(1, 4)

    # Base points
    R: Point = (Fraction(0, 1), Fraction(1, 2))
    P: Point = (Fraction(2, 1), Fraction(-5, 2))  # physical base point (y(P)=1)

    # Sanity: curve equation
    for name, pt in [("R", R), ("P", P)]:
        if pt is None:
            raise RuntimeError("Unexpected O.")
        x, y = pt
        if y * y != x * x * x + a * x + b:
            raise RuntimeError(f"{name} not on curve.")

    # --- Low multiples
    twoR = _mul(2, R, a=a)
    threeR = _mul(3, R, a=a)
    m4 = _mul(4, R, a=a)
    if twoR is None or threeR is None:
        raise RuntimeError("Unexpected: low multiple hit O.")
    Q0: Point = (twoR[0], -twoR[1])
    Q0p: Point = (threeR[0], -threeR[1])

    expected_twoR = (Fraction(1, 1), Fraction(1, 2))
    expected_threeR = (Fraction(-1, 1), Fraction(-1, 2))
    expected_Q0 = (Fraction(1, 1), Fraction(-1, 2))
    expected_Q0p = (Fraction(-1, 1), Fraction(1, 2))
    expected_m4 = (Fraction(2, 1), Fraction(-5, 2))
    low_ok = (
        twoR == expected_twoR
        and threeR == expected_threeR
        and Q0 == expected_Q0
        and Q0p == expected_Q0p
        and m4 == expected_m4
        and m4 == P
    )

    # --- Branchpoint doubling y-values
    y_2Q0 = int(_y_weight(_mul(2, Q0, a=a)))
    y_2Q0p = int(_y_weight(_mul(2, Q0p, a=a)))
    branch_y = {"y(2Q0)": int(y_2Q0), "y(2Q0')": int(y_2Q0p)}
    if branch_y != {"y(2Q0)": 6, "y(2Q0')": 21}:
        low_ok = False

    # --- Lee–Yang cubic specializations
    def P_LY(y: int) -> int:
        y = int(y)
        return 256 * y**3 + 411 * y**2 + 165 * y + 32

    P6 = P_LY(6)
    P21 = P_LY(21)
    f6 = sp.factorint(P6)
    f21 = sp.factorint(P21)
    p_ly_spec = {
        "P_LY(6)": str(int(P6)),
        "P_LY(6)_factor": str(f6),
        "P_LY(21)": str(int(P21)),
        "P_LY(21)_factor": str(f21),
    }
    # Expected: 2*37*31^2 and 4*11*241^2
    if f6 != {2: 1, 37: 1, 31: 2}:
        low_ok = False
    if f21 != {2: 2, 11: 1, 241: 2}:
        low_ok = False

    # --- Quartic Pi(lambda,y) fiber factorizations at y=6,21
    lam = sp.Symbol("lambda")
    y = sp.Integer(6)
    Pi6 = sp.expand(lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1))
    Pi6_fact = sp.factor(Pi6)
    y = sp.Integer(21)
    Pi21 = sp.expand(lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1))
    Pi21_fact = sp.factor(Pi21)

    pi_facts = {
        "Pi(lambda,6)": sp.sstr(Pi6_fact),
        "Pi(lambda,21)": sp.sstr(Pi21_fact),
    }
    if sp.factor(Pi6_fact - (lam - 2) * (lam**3 + lam**2 - 11 * lam - 21)) != 0:
        low_ok = False
    if sp.factor(Pi21_fact - (lam - 6) * (lam**3 + 5 * lam**2 - 13 * lam - 77)) != 0:
        low_ok = False

    # --- Denominator sequence v_n for x(nP) up to n=12
    v_first12: List[int] = []
    for n in range(1, 13):
        pt = _mul(n, P, a=a)
        if pt is None:
            raise RuntimeError("Unexpected torsion.")
        xpt, _ = pt
        _, v_n, den, is_sq = _fraction_to_uv2(xpt)
        if not is_sq:
            raise RuntimeError(f"Non-square denominator at n={n}: den={den}")
        v_first12.append(int(v_n))

    expected_v = [
        1,
        5,
        29,
        65,
        16264,
        2382785,
        398035821,
        43244638645,
        124106986093951,
        541051130050800400,
        2591758672670554328449,
        10358960321661880987253845,
    ]
    if v_first12 != expected_v:
        low_ok = False

    # --- Ward bilinear recurrence for the denominator EDS (specialized at m=2)
    # Convention: v_0=0, v_1=1.
    vn = [0] + [int(x) for x in v_first12]
    vn_bilin_ok = True
    vn_bilin_first_fail: Optional[int] = None
    for n in range(2, len(vn) - 2):
        sgn = -1 if ((n // 2) % 2 == 1) else 1  # (-1)^{floor(n/2)}
        lhs = vn[n + 2] * vn[n - 2]
        rhs = 29 * vn[n] * vn[n] + sgn * 25 * vn[n + 1] * vn[n - 1]
        if lhs != rhs:
            vn_bilin_ok = False
            vn_bilin_first_fail = int(n)
            break
    if not vn_bilin_ok:
        low_ok = False

    # log(v_n)/n^2 for n=8..12
    logs_8_12: List[float] = []
    for n in range(8, 13):
        vn = v_first12[n - 1]
        logs_8_12.append(float(math.log(vn) / (n * n)))

    # Canonical Néron–Tate height (natural log normalization) for P=[4]R on 37a1.
    # Note: LMFDB often reports the height pairing <P,P>=2*hhat(P), hence the factor 1/2.
    hhat_P = float(0.40889126523294376)

    # --- Bad prime 37 invariants on minimal model E0: y0^2 + y0 = x^3 - x
    # Weierstrass coefficients: a1=0,a2=0,a3=1,a4=-1,a6=0
    a1, a2, a3, a4, a6 = 0, 0, 1, -1, 0
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c6 = -b2**3 + 36 * b2 * b4 - 216 * b6
    minus_c6_mod_37 = (-c6) % 37
    leg_31_37 = _legendre_symbol(31, 37)
    if c6 != -216:
        low_ok = False
    if minus_c6_mod_37 != 31:
        low_ok = False
    if leg_31_37 != -1:
        low_ok = False

    # --- v_37 periodicity on denominators of x(nR) and x(nP)
    # Here we track v_37(v_n) where x = u / v_n^2 in lowest terms.
    def v37_of_x_denom_sqrt(pt: Point) -> int:
        if pt is None:
            return 0
        xpt, _ = pt
        _, v_n, _, is_sq = _fraction_to_uv2(xpt)
        if not is_sq:
            raise RuntimeError("Denominator not square.")
        return _v_p(v_n, 37)

    v37_R_hits: List[int] = []
    v37_R_ok = True
    for n in range(1, 77):  # 2 * 38
        pt = _mul(n, R, a=a)
        e = v37_of_x_denom_sqrt(pt)
        expected = 0 if (n % 38 != 0) else (_v_p(n, 37) + 1)
        if e != expected:
            v37_R_ok = False
        if e == 1:
            v37_R_hits.append(n)

    v37_P_hits: List[int] = []
    v37_P_ok = True
    for n in range(1, 39):  # 2 * 19
        pt = _mul(n, P, a=a)
        e = v37_of_x_denom_sqrt(pt)
        expected = 0 if (n % 19 != 0) else (_v_p(n, 37) + 1)
        if e != expected:
            v37_P_ok = False
        if e == 1:
            v37_P_hits.append(n)

    payload = Payload(
        low_multiples_ok=bool(low_ok),
        points={
            "R": str(R),
            "Q0=-2R": str(Q0),
            "Q0'=-3R": str(Q0p),
            "4R": str(m4),
            "P": str(P),
            "-P": str((P[0], -P[1])),
        },
        branchpoint_doubling_y=branch_y,
        p_ly_specializations=p_ly_spec,
        pi_fiber_factorizations=pi_facts,
        v_first12=[int(x) for x in v_first12],
        vn_ward_bilinear_ok=bool(vn_bilin_ok),
        vn_ward_bilinear_first_failure_n=vn_bilin_first_fail,
        log_v_over_n2_8_12=[float(x) for x in logs_8_12],
        hhat_P=float(hhat_P),
        c6_min_model=int(c6),
        minus_c6_mod_37=int(minus_c6_mod_37),
        legendre_31_over_37=int(leg_31_37),
        v37_periodicity_R_ok=bool(v37_R_ok),
        v37_periodicity_P_ok=bool(v37_P_ok),
        v37_R_first_hits=[int(x) for x in v37_R_hits[:5]],
        v37_P_first_hits=[int(x) for x in v37_P_hits[:5]],
    )

    out_json = export_dir() / "fold_zm_elliptic_mw_height_denominator_growth_audit.json"
    _write_json(out_json, asdict(payload))

    tex_lines: List[str] = [
        "% Auto-generated by scripts/exp_fold_zm_elliptic_mw_height_denominator_growth_audit.py",
        "\\[",
        "y([2]Q_0)=6,\\qquad y([2]Q_0')=21,\\qquad P_{\\mathrm{LY}}(6)=2\\cdot 37\\cdot 31^{2},\\qquad P_{\\mathrm{LY}}(21)=4\\cdot 11\\cdot 241^{2}.",
        "\\]",
        "\\[",
        "\\Pi(\\lambda,6)=(\\lambda-2)(\\lambda^{3}+\\lambda^{2}-11\\lambda-21),\\qquad \\Pi(\\lambda,21)=(\\lambda-6)(\\lambda^{3}+5\\lambda^{2}-13\\lambda-77).",
        "\\]",
        "",
    ]
    out_tex = generated_dir() / "eq_fold_zm_elliptic_mw_height_denominator_growth_audit.tex"
    _write_text(out_tex, "\n".join(tex_lines))

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-mw-height-den] checks:"
        f" low_ok={low_ok} vnBilin={vn_bilin_ok} v37R={v37_R_ok} v37P={v37_P_ok}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print(f"[fold-zm-elliptic-mw-height-den] wrote {out_json}", flush=True)
    print(f"[fold-zm-elliptic-mw-height-den] wrote {out_tex}", flush=True)
    print("[fold-zm-elliptic-mw-height-den] done", flush=True)


if __name__ == "__main__":
    main()

