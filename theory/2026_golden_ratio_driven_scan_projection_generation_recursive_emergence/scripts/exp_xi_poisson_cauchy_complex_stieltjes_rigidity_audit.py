#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: complex Stieltjes multipole rigidity in Poisson--Cauchy coarsegraining.

This script is English-only by repository convention.

It verifies three groups of identities:

1) Sixth-order KL coefficient building blocks (single-channel):
     ∫ G u^2 = 1/4,  ∫ G u w = -1/8,  ∫ G v^2 = 3/16,  ∫ G u^3 = -3/32,
   and reconstruction of
     C6 = sigma^6/64 - sigma^2 m4/8 + 3 m3^2/32.

2) Universal multipole constants:
     C_m = binom(2m-2, m-1)/2^(2m),
   via the equivalent theta-integral.

3) Symbolic dissipation-alignment ratio:
     (T * I1) / D_KL -> 2m
   under D_KL ~ C_m |mu_m|^2 T^{-2m}.

Outputs:
  - artifacts/export/xi_poisson_cauchy_complex_stieltjes_rigidity_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp
import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _as_mp(x: sp.Expr) -> mp.mpf:
    return mp.mpf(str(sp.N(x, 80)))


def _I_m_theta_numeric(m: int) -> mp.mpf:
    pi = mp.pi

    def f(theta: mp.mpf) -> mp.mpf:
        c = mp.cos(theta)
        s = mp.sin((m + 1) * (pi / 2 - theta))
        return (c ** (2 * m - 2)) * (s * s)

    return (mp.quad(f, [-pi / 2, mp.mpf("0.0"), pi / 2])) / pi


@dataclass(frozen=True)
class Payload:
    integral_exact_ok: bool
    I_u2: str
    I_uw: str
    I_v2: str
    I_u3: str
    C6_identity_ok: bool
    multipole_constants_ok: bool
    multipole_failures: List[Dict[str, object]]
    dissipation_ratio_symbolic_ok: bool
    m2_lorentz_identity_ok: bool
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit complex Stieltjes multipole rigidity constants.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument("--m-max", type=int, default=16, help="Check C_m for m=2..m-max (default: 16).")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision (default: 80).")
    parser.add_argument("--tol", type=str, default="1e-40", help="absolute tolerance (default: 1e-40).")
    args = parser.parse_args()

    t0 = time.time()
    mp.mp.dps = int(args.dps)
    tol = mp.mpf(str(args.tol))

    y = sp.symbols("y", real=True)
    G = sp.Rational(1, 1) / (sp.pi * (1 + y**2))
    u = (3 * y**2 - 1) / (1 + y**2) ** 2
    v = 4 * y * (y**2 - 1) / (1 + y**2) ** 3
    w = (5 * y**4 - 10 * y**2 + 1) / (1 + y**2) ** 4

    I_u2 = sp.simplify(sp.integrate(G * u**2, (y, -sp.oo, sp.oo)))
    I_uw = sp.simplify(sp.integrate(G * u * w, (y, -sp.oo, sp.oo)))
    I_v2 = sp.simplify(sp.integrate(G * v**2, (y, -sp.oo, sp.oo)))
    I_u3 = sp.simplify(sp.integrate(G * u**3, (y, -sp.oo, sp.oo)))

    integral_exact_ok = bool(
        (I_u2 == sp.Rational(1, 4))
        and (I_uw == sp.Rational(-1, 8))
        and (I_v2 == sp.Rational(3, 16))
        and (I_u3 == sp.Rational(-3, 32))
    )

    sigma, m3, m4 = sp.symbols("sigma m3 m4", real=True)
    C6_from_integrals = sp.simplify(
        sp.Rational(1, 2) * (2 * sigma**2 * m4 * I_uw + m3**2 * I_v2)
        - sp.Rational(1, 6) * (sigma**6 * I_u3)
    )
    C6_expected = sp.simplify(sigma**6 / 64 - sigma**2 * m4 / 8 + 3 * m3**2 / 32)
    C6_identity_ok = bool(sp.expand(C6_from_integrals - C6_expected) == 0)

    failures: List[Dict[str, object]] = []
    m_max = int(args.m_max)
    if m_max < 2:
        raise ValueError("--m-max must be >= 2")
    for m in range(2, m_max + 1):
        I_num = _I_m_theta_numeric(m)
        I_exact = _as_mp(sp.Rational(sp.binomial(2 * m - 2, m - 1), 2 ** (2 * m - 1)))
        err = abs(I_num - I_exact)
        if err > tol:
            failures.append(
                {
                    "m": int(m),
                    "I_numeric": str(I_num),
                    "I_exact": str(I_exact),
                    "abs_err": str(err),
                    "tol": str(tol),
                }
            )
    multipole_constants_ok = len(failures) == 0

    T, m, C, mu = sp.symbols("T m C mu", positive=True)
    D = C * mu**2 * T ** (-2 * m)
    I1 = sp.simplify(-sp.diff(D, T))
    ratio = sp.simplify(T * I1 / D)
    dissipation_ratio_symbolic_ok = bool(sp.simplify(ratio - 2 * m) == 0)

    A, B = sp.symbols("A B", real=True)
    m2 = A + 2 * sp.I * B
    lhs = sp.simplify(sp.Abs(m2) ** 2 / 8)
    rhs = sp.simplify((A**2 + 4 * B**2) / 8)
    m2_lorentz_identity_ok = bool(sp.simplify(lhs - rhs) == 0)

    payload = Payload(
        integral_exact_ok=bool(integral_exact_ok),
        I_u2=str(I_u2),
        I_uw=str(I_uw),
        I_v2=str(I_v2),
        I_u3=str(I_u3),
        C6_identity_ok=bool(C6_identity_ok),
        multipole_constants_ok=bool(multipole_constants_ok),
        multipole_failures=failures,
        dissipation_ratio_symbolic_ok=bool(dissipation_ratio_symbolic_ok),
        m2_lorentz_identity_ok=bool(m2_lorentz_identity_ok),
        elapsed_s=float(time.time() - t0),
    )

    if not payload.integral_exact_ok:
        raise AssertionError("integral identities for u,v,w failed")
    if not payload.C6_identity_ok:
        raise AssertionError("C6 coefficient identity failed")
    if not payload.multipole_constants_ok:
        raise AssertionError("multipole constant checks failed")
    if not payload.dissipation_ratio_symbolic_ok:
        raise AssertionError("symbolic ratio T*I1/D failed")
    if not payload.m2_lorentz_identity_ok:
        raise AssertionError("m2 Lorentz-form identity failed")

    if not args.no_output:
        out = export_dir() / "xi_poisson_cauchy_complex_stieltjes_rigidity_audit.json"
        _write_json(out, asdict(payload))
        print(f"[xi-poisson-cauchy-complex-stieltjes-rigidity] wrote {out}", flush=True)

    print(
        "[xi-poisson-cauchy-complex-stieltjes-rigidity] "
        f"integral_ok={payload.integral_exact_ok} "
        f"C6_ok={payload.C6_identity_ok} "
        f"multipole_ok={payload.multipole_constants_ok} "
        f"ratio_ok={payload.dissipation_ratio_symbolic_ok} "
        f"elapsed_s={payload.elapsed_s:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()
