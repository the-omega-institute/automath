#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Certificates for Hellinger Toeplitz theta/Hankel identities.

This script provides reproducible numerical/exact checks for:
  - Toeplitz symbol sigma_Δ(θ) equivalences:
      (i) Fourier series via A(nΔ),
     (ii) Poisson periodization via sech^2,
    (iii) Jacobi theta4 closed form 1 + Δ ∂_θ^2 log θ4(θ/2,q), q=e^{-Δ/2}.
  - Exact even-moment formula for w(ξ)=π^2 sech^2(π ξ) and the induced Hankel
    determinants H_k = det(μ_{p+q}) (rationality + small-k values).
  - Small-ε collision asymptotic for det G with entries A(ε(t_j-t_k)).

Outputs: one JSON certificate under artifacts/export/.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir


def A(delta: mp.mpf) -> mp.mpf:
    d = mp.fabs(delta)
    if d == 0:
        return mp.mpf(1)
    return d / (2 * mp.sinh(d / 2))


def _choose_N_fourier(Delta: mp.mpf, tol: mp.mpf) -> int:
    # Choose N so that the tail coefficient A((N+1)Δ) is below tol.
    n = 1
    while True:
        if A(n * Delta) < tol:
            return max(1, n)
        n += 1
        if n > 200000:
            return n


def sigma_fourier(theta: mp.mpf, Delta: mp.mpf, tol: mp.mpf) -> mp.mpf:
    N = _choose_N_fourier(Delta, tol)
    s = mp.mpf(1)
    for n in range(1, N + 1):
        s += 2 * A(mp.mpf(n) * Delta) * mp.cos(mp.mpf(n) * theta)
    return s


def _choose_K_poisson(theta: mp.mpf, Delta: mp.mpf, tol: mp.mpf) -> int:
    # Choose K so that the next periodic image term is below tol.
    K = 0
    while True:
        k = K + 1
        x = mp.pi * (theta + 2 * mp.pi * k) / Delta
        if mp.sech(x) ** 2 < tol:
            return K
        K += 1
        if K > 20000:
            return K


def sigma_poisson(theta: mp.mpf, Delta: mp.mpf, tol: mp.mpf) -> mp.mpf:
    K = _choose_K_poisson(theta, Delta, tol)
    s = mp.mpf(0)
    for k in range(-K, K + 1):
        x = mp.pi * (theta + 2 * mp.pi * mp.mpf(k)) / Delta
        s += mp.sech(x) ** 2
    return (mp.pi**2 / Delta) * s


def _choose_M_theta4(q: mp.mpf, tol: mp.mpf) -> int:
    # Choose M so that q^{M^2} <= tol.
    if q <= 0:
        return 1
    M = 1
    while q ** (M * M) > tol:
        M += 1
        if M > 5000:
            return M
    return max(2, M)


def _theta4_and_derivs(z: mp.mpf, q: mp.mpf, M: int) -> Tuple[mp.mpc, mp.mpc, mp.mpc]:
    # theta4(z,q) := sum_{m∈Z} (-1)^m q^{m^2} e^{2 i m z}
    # derivatives w.r.t. z:
    #   theta4'(z,q) = sum (2 i m) term
    #   theta4''(z,q) = sum (2 i m)^2 term = sum (-4 m^2) term
    th = mp.mpc(0)
    th1 = mp.mpc(0)
    th2 = mp.mpc(0)
    for m in range(-M, M + 1):
        mm = mp.mpf(m)
        term = ((-1) ** m) * (q ** (m * m)) * mp.e ** (2j * mm * z)
        th += term
        th1 += (2j * mm) * term
        th2 += (-4 * mm * mm) * term
    return th, th1, th2


def sigma_theta(theta: mp.mpf, Delta: mp.mpf, tol: mp.mpf) -> mp.mpf:
    q = mp.e ** (-Delta / 2)
    z = theta / 2
    M = _choose_M_theta4(q, tol)
    th, th1, th2 = _theta4_and_derivs(z, q, M)
    d2log_dz2 = th2 / th - (th1 / th) ** 2
    d2log_dtheta2 = d2log_dz2 / 4
    v = mp.mpf(1) + Delta * d2log_dtheta2
    # Should be real; keep the real part.
    return mp.re(v)


def vandermonde_sq(xs: Sequence[mp.mpf]) -> mp.mpf:
    v = mp.mpf(1)
    n = len(xs)
    for i in range(n):
        for j in range(i + 1, n):
            v *= (xs[j] - xs[i]) ** 2
    return v


def det_gram_cluster(t: Sequence[mp.mpf], eps: mp.mpf) -> mp.mpf:
    k = len(t)
    G = mp.matrix(k)
    for i in range(k):
        for j in range(k):
            G[i, j] = A(eps * (t[i] - t[j]))
    return mp.det(G)


def _sympy_to_str(x: sp.Expr) -> str:
    x = sp.simplify(x)
    if isinstance(x, sp.Rational):
        return f"{int(x.p)}/{int(x.q)}" if x.q != 1 else f"{int(x.p)}"
    return str(x)


def _prime_factors(n: int) -> List[int]:
    if n < 0:
        n = -n
    out: List[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        out.append(n)
    return out


def mu_exact(n: int) -> sp.Expr:
    # Moments for dμ(ξ) = w(ξ) dξ / (2π), w(ξ)=π^2 sech^2(π ξ).
    if n % 2 == 1:
        return sp.Integer(0)
    k = n // 2
    # μ_{2k} = 2^{1-2k} π^{-2k} (2k)! (1-2^{1-2k}) ζ(2k)
    expr = (
        sp.Integer(2) ** (1 - 2 * k)
        * sp.pi ** (-2 * k)
        * sp.factorial(2 * k)
        * (sp.Integer(1) - sp.Integer(2) ** (1 - 2 * k))
        * sp.zeta(2 * k)
    )
    return sp.simplify(expr)


def hankel_det_exact(kappa: int) -> sp.Expr:
    M = sp.Matrix([[mu_exact(p + q) for q in range(kappa)] for p in range(kappa)])
    return sp.simplify(M.det())


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate certificates for theta/Hankel identities in the Hellinger Toeplitz section.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "hellinger_toeplitz_theta_hankel_certificate.json"),
        help="Output JSON path.",
    )
    parser.add_argument("--mp-dps", type=int, default=90, help="mpmath working precision (decimal digits).")
    args = parser.parse_args()

    mp.mp.dps = int(args.mp_dps)
    tol = mp.mpf("1e-70")

    # --- Toeplitz symbol checks ---
    deltas = [mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("2.4")]
    thetas = [mp.mpf("0.0"), mp.mpf("0.2"), mp.mpf("1.0"), mp.mpf("-2.1")]
    toeplitz_rows: List[Dict[str, object]] = []
    max_err = mp.mpf(0)
    for Delta in deltas:
        for theta in thetas:
            sf = sigma_fourier(theta, Delta, tol)
            spoi = sigma_poisson(theta, Delta, tol)
            sth = sigma_theta(theta, Delta, tol)
            e_fp = mp.fabs(sf - spoi)
            e_ft = mp.fabs(sf - sth)
            e_pt = mp.fabs(spoi - sth)
            max_err = max(max_err, e_fp, e_ft, e_pt)
            toeplitz_rows.append(
                {
                    "Delta": str(Delta),
                    "theta": str(theta),
                    "sigma_fourier": mp.nstr(sf, 40),
                    "sigma_poisson": mp.nstr(spoi, 40),
                    "sigma_theta4": mp.nstr(sth, 40),
                    "abs_err_fourier_poisson": mp.nstr(e_fp, 10),
                    "abs_err_fourier_theta4": mp.nstr(e_ft, 10),
                    "abs_err_poisson_theta4": mp.nstr(e_pt, 10),
                }
            )

    # --- Exact moments and Hankel determinants ---
    mu_map: Dict[str, str] = {}
    for n in range(0, 12):
        mu_map[str(n)] = _sympy_to_str(mu_exact(n))

    hankel_map: Dict[str, str] = {}
    hankel_den_primes: Dict[str, List[int]] = {}
    for kappa in range(1, 7):
        H = hankel_det_exact(kappa)
        hankel_map[str(kappa)] = _sympy_to_str(H)
        if isinstance(H, sp.Rational):
            hankel_den_primes[str(kappa)] = _prime_factors(int(H.q))
        else:
            hankel_den_primes[str(kappa)] = []

    # --- Collision asymptotic checks ---
    collision_rows: List[Dict[str, object]] = []
    for kappa, t_list in [
        (4, [mp.mpf("0.0"), mp.mpf("1.0"), mp.mpf("3.0"), mp.mpf("4.0")]),
        (5, [mp.mpf("0.0"), mp.mpf("1.0"), mp.mpf("2.0"), mp.mpf("5.0"), mp.mpf("7.0")]),
    ]:
        Hk = hankel_det_exact(kappa)
        if not isinstance(Hk, sp.Rational):
            raise RuntimeError(f"Expected rational Hankel determinant, got: {Hk}")
        Hk_mp = mp.mpf(int(Hk.p)) / mp.mpf(int(Hk.q))
        prod_j = mp.mpf(1)
        for j in range(0, kappa):
            prod_j /= mp.factorial(j) ** 2
        v2 = vandermonde_sq(t_list)
        for eps in [mp.mpf("1e-1"), mp.mpf("5e-2"), mp.mpf("2e-2"), mp.mpf("1e-2")]:
            detG = det_gram_cluster(t_list, eps)
            pred = (eps ** (kappa * (kappa - 1))) * prod_j * Hk_mp * v2
            ratio = detG / pred
            rel_err = mp.fabs(ratio - 1)
            collision_rows.append(
                {
                    "kappa": kappa,
                    "t": [str(x) for x in t_list],
                    "eps": str(eps),
                    "detG": mp.nstr(detG, 40),
                    "pred": mp.nstr(pred, 40),
                    "ratio": mp.nstr(ratio, 20),
                    "abs_err_ratio_minus_1": mp.nstr(rel_err, 10),
                }
            )

    payload: Dict[str, object] = {
        "script": Path(__file__).name,
        "mp_dps": int(args.mp_dps),
        "tol": str(tol),
        "toeplitz_theta_checks": toeplitz_rows,
        "toeplitz_max_abs_err_across_representations": mp.nstr(max_err, 12),
        "mu_n_exact": mu_map,
        "hankel_det_exact": hankel_map,
        "hankel_denominator_prime_support": hankel_den_primes,
        "collision_asymptotic_checks": collision_rows,
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

