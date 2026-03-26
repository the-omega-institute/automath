#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: harmonic-moment / multipole constant for Poisson–Cauchy coarsegraining KL.

This script is English-only by repository convention.

We verify:
  - The universal integral constant (for k>=2)

      I_k := ∫_R (1/pi) * (1/(1+y^2)) * (Im ((y+i)/(y-i)^k))^2 dy
          = binom(2k-2, k-1) / 2^(2k-1),

    hence the KL prefactor c_k = I_k/2 = binom(2k-2, k-1)/2^(2k).

    Numerically, we evaluate the equivalent theta-integral
      I_k = (1/pi) ∫_{-pi/2}^{pi/2} cos(theta)^(2k-2) * sin((k+1)(pi/2-theta))^2 dtheta.

  - Root-of-unity moment cancellation:
      For Z_j = r * exp(2π i j/N),
      m_k := (1/N) Σ_j Z_j^k vanishes for 1<=k<=N-1, and m_N = r^N.

Outputs:
  - artifacts/export/xi_poisson_cauchy_harmonic_multipole_kl_audit.json
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


@dataclass(frozen=True)
class Payload:
    k_max: int
    integral_checks_ok: bool
    integral_failures: List[Dict[str, object]]
    moment_cancellation_ok: bool
    moment_examples: List[Dict[str, object]]
    elapsed_s: float


def _I_k_theta_numeric(k: int) -> mp.mpf:
    pi = mp.pi

    def f(theta: mp.mpf) -> mp.mpf:
        c = mp.cos(theta)
        return (c ** (2 * k - 2)) * (mp.sin((k + 1) * (pi / 2 - theta)) ** 2)

    return (mp.quad(f, [-pi / 2, mp.mpf("0.0"), pi / 2])) / pi


def _I_k_exact(k: int) -> sp.Rational:
    return sp.Rational(sp.binomial(2 * k - 2, k - 1), 2 ** (2 * k - 1))


def _moment_cancellation_examples() -> List[Dict[str, object]]:
    out: List[Dict[str, object]] = []
    for N in [4, 5, 7]:
        # Use high-precision numeric roots of unity to avoid branch/simplification issues.
        r = mp.mpf("1.5")
        omega = mp.e ** (2j * mp.pi / N)

        def m(k: int) -> complex:
            return sum((r * (omega**j)) ** k for j in range(N)) / N

        m0 = m(0)
        m1 = m(1)
        tol = mp.mpf("1e-60")
        zeros_ok = all(abs(m(k)) <= tol for k in range(2, N))
        mN = m(N)
        mN_expected = r**N
        mN_ok = abs(mN - mN_expected) <= tol * max(mp.mpf("1.0"), abs(mN_expected))
        out.append(
            {
                "N": int(N),
                "r": "3/2",
                "m_0_abs_err": str(abs(m0 - 1)),
                "m_1_abs": str(abs(m1)),
                "m_2_to_m_{N-1}_all_zero": bool(zeros_ok),
                "m_N_abs_err": str(abs(mN - mN_expected)),
                "m_N_expected": str(mN_expected),
                "m_N_ok": bool(mN_ok),
            }
        )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit harmonic multipole KL constant for Poisson–Cauchy coarsegraining.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument("--k-max", type=int, default=18, help="Check I_k constant for k=2..k-max (default: 18).")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision (default: 80).")
    parser.add_argument("--tol", type=str, default="1e-40", help="absolute tolerance (default: 1e-40).")
    args = parser.parse_args()

    t0 = time.time()
    print("[xi-poisson-cauchy-harmonic-multipole-kl] start", flush=True)

    mp.mp.dps = int(args.dps)
    tol = mp.mpf(str(args.tol))
    k_max = int(args.k_max)
    if k_max < 2:
        raise ValueError("k-max must be >= 2")

    failures: List[Dict[str, object]] = []
    for k in range(2, k_max + 1):
        I_num = _I_k_theta_numeric(k)
        I_ex = _as_mp(_I_k_exact(k))
        err = abs(I_num - I_ex)
        if err > tol:
            failures.append(
                {
                    "k": int(k),
                    "I_numeric": str(I_num),
                    "I_exact": str(I_ex),
                    "abs_err": str(err),
                    "tol": str(tol),
                }
            )

    moment_examples = _moment_cancellation_examples()
    moment_cancellation_ok = all(
        (ex["m_2_to_m_{N-1}_all_zero"] and ex["m_N_ok"])
        for ex in moment_examples
    )

    elapsed = time.time() - t0
    payload = Payload(
        k_max=int(k_max),
        integral_checks_ok=bool(len(failures) == 0),
        integral_failures=failures,
        moment_cancellation_ok=bool(moment_cancellation_ok),
        moment_examples=moment_examples,
        elapsed_s=float(elapsed),
    )

    if not args.no_output:
        out = export_dir() / "xi_poisson_cauchy_harmonic_multipole_kl_audit.json"
        _write_json(out, asdict(payload))
        print(f"[xi-poisson-cauchy-harmonic-multipole-kl] wrote {out}", flush=True)

    print(
        "[xi-poisson-cauchy-harmonic-multipole-kl] checks:"
        f" integral_ok={payload.integral_checks_ok} moment_ok={payload.moment_cancellation_ok}"
        f" seconds={elapsed:.3f}",
        flush=True,
    )
    print("[xi-poisson-cauchy-harmonic-multipole-kl] done", flush=True)


if __name__ == "__main__":
    main()

