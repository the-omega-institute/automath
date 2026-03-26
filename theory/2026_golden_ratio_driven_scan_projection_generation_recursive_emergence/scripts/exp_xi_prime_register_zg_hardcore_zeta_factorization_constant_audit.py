#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit hard-core zeta factorization constants for the ZG prime-code Dirichlet series.

This script numerically evaluates, at controlled precision:
  - C_HC := H(1) where F(s) = H(s) * zeta(s)/zeta(2s),
  - Res_{s=1} F(s) = C_HC / zeta(2),
  - kappa_HC := (d/ds) log H(s) |_{s=1}.

Output:
  - artifacts/export/xi_prime_register_zg_hardcore_zeta_factorization_constant_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _first_n_primes(n: int) -> List[int]:
    if n <= 0:
        return []
    if n < 6:
        bound = 15
    else:
        # Rosser–Schoenfeld style upper bound for p_n (safe with slack).
        bound = int(n * (math.log(n) + math.log(math.log(n))) + 20)
    while True:
        primes = list(sp.primerange(2, bound + 1))
        if len(primes) >= n:
            return [int(p) for p in primes[:n]]
        bound *= 2


def _hc_constants(primes: List[int], s: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    """Return (H_N(s), d/ds log H_N(s)) via u_n recursion."""
    if not primes:
        return mp.mpf("1"), mp.mpf("0")

    u_prev = mp.mpf("0")
    du_prev = mp.mpf("0")
    logH = mp.mpf("0")
    dlogH = mp.mpf("0")

    for idx, p in enumerate(primes, start=1):
        lp = mp.log(p)
        w = mp.e ** (-s * lp)  # p^{-s}
        dw = -lp * w

        if idx == 1:
            u = mp.mpf("1") + w
            du = dw
        else:
            u = mp.mpf("1") + w / u_prev
            du = (dw * u_prev - w * du_prev) / (u_prev * u_prev)

        logH += mp.log(u) - mp.log(mp.mpf("1") + w)
        dlogH += du / u - dw / (mp.mpf("1") + w)

        u_prev, du_prev = u, du

    return mp.e ** logH, dlogH


def _F_N_at_one(primes: List[int]) -> mp.mpf:
    """Compute F_N(1) by linear recurrence."""
    if not primes:
        return mp.mpf("1")
    f0 = mp.mpf("1")
    f1 = mp.mpf("1") + mp.mpf(1) / primes[0]
    if len(primes) == 1:
        return f1
    f_nm2, f_nm1 = f0, f1
    for p in primes[1:]:
        f_n = f_nm1 + (mp.mpf(1) / p) * f_nm2
        f_nm2, f_nm1 = f_nm1, f_n
    return f_nm1


def _B_N_at_one(primes: List[int]) -> mp.mpf:
    b = mp.mpf("1")
    for p in primes:
        b *= mp.mpf("1") + mp.mpf(1) / p
    return b


@dataclass(frozen=True)
class Payload:
    n_primes: int
    mp_dps: int
    C_HC: float
    residue: float
    kappa_HC: float
    kappa_HC_finite_difference: float
    kappa_HC_fd_minus_rec: float
    H_from_ratio: float
    H_ratio_minus_H_u: float
    stability_C_HC_delta_last: float
    stability_kappa_delta_last: float


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit C_HC, residue, and kappa_HC for ZG hard-core zeta factorization."
    )
    parser.add_argument("--n-primes", type=int, default=6000, help="Number of initial primes used.")
    parser.add_argument("--dps", type=int, default=120, help="mpmath decimal precision.")
    parser.add_argument("--fd-h", type=str, default="1e-6", help="Step size for symmetric finite difference.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    n = int(args.n_primes)
    dps = int(args.dps)
    mp.mp.dps = dps

    primes = _first_n_primes(n)
    s = mp.mpf("1")
    h = mp.mpf(str(args.fd_h))

    # Constants via u_n recursion at s=1.
    H_u, kappa_u = _hc_constants(primes, s)

    # Cross-check via direct ratio H_N(1)=F_N(1)/prod(1+1/p).
    F1 = _F_N_at_one(primes)
    B1 = _B_N_at_one(primes)
    H_ratio = F1 / B1

    zeta2 = mp.zeta(2)
    residue = H_u / zeta2

    # Independent finite-difference check for kappa_HC.
    H_p, _ = _hc_constants(primes, s + h)
    H_m, _ = _hc_constants(primes, s - h)
    kappa_fd = (mp.log(H_p) - mp.log(H_m)) / (mp.mpf("2") * h)

    # Simple last-step stability indicator.
    if n >= 2:
        H_u_m1, kappa_u_m1 = _hc_constants(primes[:-1], s)
        dC = abs(H_u - H_u_m1)
        dk = abs(kappa_u - kappa_u_m1)
    else:
        dC = mp.mpf("0")
        dk = mp.mpf("0")

    payload = Payload(
        n_primes=n,
        mp_dps=dps,
        C_HC=float(H_u),
        residue=float(residue),
        kappa_HC=float(kappa_u),
        kappa_HC_finite_difference=float(kappa_fd),
        kappa_HC_fd_minus_rec=float(kappa_fd - kappa_u),
        H_from_ratio=float(H_ratio),
        H_ratio_minus_H_u=float(H_ratio - H_u),
        stability_C_HC_delta_last=float(dC),
        stability_kappa_delta_last=float(dk),
    )

    if not args.no_output:
        out = export_dir() / "xi_prime_register_zg_hardcore_zeta_factorization_constant_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[xi-prime-register-zg-hardcore-zeta-factorization-constant] "
        f"C_HC={payload.C_HC:.12f} "
        f"residue={payload.residue:.12f} "
        f"kappa_HC={payload.kappa_HC:.12f} "
        f"kappa_fd={payload.kappa_HC_finite_difference:.12f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

