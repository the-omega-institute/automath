#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Branch points and analytic radius for the sync-kernel pressure P(theta).

We work with the sextic algebraic equation from Appendix "pressure-analytic":

  F(lambda, u) = 0,  u = exp(theta),

and locate branch points of the algebraic function lambda(u) by the
discriminant condition Disc_lambda(F)(u) = 0 (equivalently, F=0 and F_lambda=0).

This script:
  - records the explicit palindromic D(u) factor for Disc_lambda(F)(u),
  - finds the nearest branch points in theta = log(u),
  - estimates an upper bound M_r = max_{|theta|=r} |P(theta)| on a circle
    by numerical continuation of the lambda-branch with lambda(1)=3.

Outputs (English-only, reproducible artifacts):
  - artifacts/export/sync_kernel_pressure_branchpoints.json
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np

from common_paths import export_dir


def _F_coeffs(u: complex) -> List[complex]:
    """
    Return coefficients of F(lambda,u) as a degree-6 polynomial in lambda:
      sum_{k=0}^6 c[k] * lambda^{6-k}
    """
    return [
        1.0,
        -(1.0 + u),
        -5.0 * u,
        3.0 * u * (1.0 + u),
        -u * (u**2 - 3.0 * u + 1.0),
        u * (u**3 - 3.0 * u**2 - 3.0 * u + 1.0),
        (u**2) * (u**2 + u + 1.0),
    ]


def _D_coeffs_palindromic() -> List[int]:
    """
    Coefficients for the palindromic degree-20 polynomial D(u):
      D(u) = sum_{k=0}^{20} a[k] u^k, with a[k] = a[20-k].

    Stored as [a0, a1, ..., a20].
    """
    a0_to_a10 = [
        256,
        1408,
        22144,
        -20217,
        814606,
        5139405,
        10776760,
        16410991,
        23046562,
        30590013,
        34775088,
    ]
    a11_to_a20 = list(reversed(a0_to_a10[:-1]))
    return a0_to_a10 + a11_to_a20


def _poly_roots(coeffs: Iterable[complex]) -> np.ndarray:
    coeffs = np.asarray(list(coeffs), dtype=np.complex128)
    return np.roots(coeffs)


def _closest_log_to_zero(u: complex, kmax: int = 2) -> complex:
    """Return log(u) shifted by 2pi i k (|k|<=kmax) with minimal absolute value."""
    base = cmath.log(u)
    best = base
    best_abs = abs(base)
    twopi_i = 2.0 * math.pi * 1j
    for k in range(-kmax, kmax + 1):
        z = base + twopi_i * k
        az = abs(z)
        if az < best_abs:
            best_abs = az
            best = z
    return best


def _unwrap_log(prev: complex, z: complex, kmax: int = 2) -> complex:
    """Choose a branch of log(z) closest to prev by adding 2pi i k."""
    base = cmath.log(z)
    twopi_i = 2.0 * math.pi * 1j
    best = base
    best_dist = abs(base - prev)
    for k in range(-kmax, kmax + 1):
        w = base + twopi_i * k
        d = abs(w - prev)
        if d < best_dist:
            best_dist = d
            best = w
    return best


def _track_lambda_along_path(thetas: List[complex]) -> Tuple[List[complex], List[complex]]:
    """
    Track the algebraic branch lambda(u) along a theta-path using nearest-root continuation.
    Return (lambdas, logs) where logs is the unwrapped log(lambda).
    """
    lambdas: List[complex] = []
    logs: List[complex] = []

    # Initialize at theta=0 -> u=1, pick the root closest to 3.
    u0 = 1.0 + 0.0j
    r0 = _poly_roots(_F_coeffs(u0))
    lam0 = r0[np.argmin(np.abs(r0 - 3.0))]
    p0 = cmath.log(lam0)
    lambdas.append(complex(lam0))
    logs.append(complex(p0))

    lam_prev = complex(lam0)
    p_prev = complex(p0)
    t_start = time.time()

    for idx, th in enumerate(thetas[1:], start=1):
        u = cmath.exp(th)
        roots = _poly_roots(_F_coeffs(u))
        lam = roots[np.argmin(np.abs(roots - lam_prev))]
        p = _unwrap_log(p_prev, lam)
        lambdas.append(complex(lam))
        logs.append(complex(p))
        lam_prev = complex(lam)
        p_prev = complex(p)

        # Progress output (safe for longer runs).
        if idx % 200 == 0:
            elapsed = time.time() - t_start
            print(f"[branch-track] step {idx}/{len(thetas)-1}, elapsed={elapsed:.1f}s", flush=True)

    return lambdas, logs


@dataclass(frozen=True)
class BranchpointSummary:
    R_theta: float
    theta_star: str
    theta_star_conj: str
    u_star: str
    u_star_conj: str
    u_star_inv: str
    u_star_inv_conj: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Branch points and analytic radius for sync-kernel pressure.")
    parser.add_argument("--circle-steps", type=int, default=2400, help="Steps for theta circle sampling.")
    parser.add_argument("--radial-steps", type=int, default=300, help="Steps from 0 to r along real axis.")
    parser.add_argument("--kmax-log", type=int, default=2, help="|k|<=kmax for log(·)+2pi i k search.")
    parser.add_argument("--r-factor", type=float, default=0.99, help="Use r = r_factor * R_theta for circle bound.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_pressure_branchpoints.json"),
    )
    args = parser.parse_args()

    # 1) Roots of D(u) and nearest theta radius.
    D_coeffs = _D_coeffs_palindromic()  # ascending coefficients
    # numpy roots expects descending coefficients
    Du_desc = list(reversed(D_coeffs))
    u_roots = _poly_roots(Du_desc)

    # Find the root minimizing |log(u)+2pi i k|.
    best_u = None
    best_theta = None
    best_R = None
    for ur in u_roots:
        if abs(ur) == 0:
            continue
        th = _closest_log_to_zero(complex(ur), kmax=int(args.kmax_log))
        R = abs(th)
        if best_R is None or R < best_R:
            best_R = R
            best_theta = th
            best_u = complex(ur)

    assert best_u is not None and best_theta is not None and best_R is not None

    # Choose theta_star with positive real part (for reporting), keep conjugate too.
    theta_star = best_theta
    if theta_star.real < 0:
        theta_star = -theta_star
        best_u = 1.0 / best_u
    theta_star_conj = theta_star.conjugate()

    u_star = cmath.exp(theta_star)
    u_star_conj = u_star.conjugate()
    u_star_inv = 1.0 / u_star
    u_star_inv_conj = u_star_inv.conjugate()

    summary = BranchpointSummary(
        R_theta=float(abs(theta_star)),
        theta_star=str(theta_star),
        theta_star_conj=str(theta_star_conj),
        u_star=str(u_star),
        u_star_conj=str(u_star_conj),
        u_star_inv=str(u_star_inv),
        u_star_inv_conj=str(u_star_inv_conj),
    )

    print(f"[branchpoints] R_theta ≈ {summary.R_theta:.12f}", flush=True)
    print(f"[branchpoints] theta_star ≈ {theta_star}", flush=True)

    # 2) Circle bound M_r for P(theta)=log lambda(exp(theta)).
    r = float(args.r_factor) * summary.R_theta
    radial_steps = int(args.radial_steps)
    circle_steps = int(args.circle_steps)

    thetas: List[complex] = []
    # radial segment: 0 -> r (real)
    for j in range(radial_steps + 1):
        t = j / radial_steps
        thetas.append((t * r) + 0.0j)
    # circle: r * exp(i phi), phi in [0, 2pi]
    for j in range(1, circle_steps + 1):
        phi = 2.0 * math.pi * (j / circle_steps)
        thetas.append(r * (math.cos(phi) + 1j * math.sin(phi)))

    print(f"[circle] tracking along path: radial_steps={radial_steps}, circle_steps={circle_steps}", flush=True)
    _, logs = _track_lambda_along_path(thetas)

    # Compute M_r on the circle part only.
    circle_logs = logs[radial_steps:]  # includes the first circle point
    M_r = max(abs(p) for p in circle_logs)
    print(f"[circle] r = {r:.12f}, M_r ≈ {M_r:.6f}", flush=True)

    # Example remainder bound at |theta|<=0.5 (same as the paper statement).
    theta0 = 0.5
    if theta0 >= r:
        rem_bound = float("nan")
    else:
        rem_bound = float(M_r * (theta0**9) / (r**9) / (1.0 - theta0 / r))
    print(f"[remainder] |theta|<=0.5 bound ≲ {rem_bound:.6e}", flush=True)

    payload = {
        "D_u_coeffs_ascending": D_coeffs,
        "branchpoint_nearest": asdict(summary),
        "r_factor": float(args.r_factor),
        "r": r,
        "M_r": float(M_r),
        "example_theta_max": theta0,
        "example_remainder_bound": rem_bound,
        "notes": {
            "lambda_branch": "continued from lambda(1)=3 by nearest-root tracking",
            "log_branch": "unwrapped by minimizing jumps modulo 2*pi*i",
        },
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[done] wrote {jout}", flush=True)


if __name__ == "__main__":
    main()

